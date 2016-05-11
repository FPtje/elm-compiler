{-# OPTIONS_GHC -Wall #-}
module Canonicalize.Environment where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set

import AST.Expression.General (saveEnvName)
import qualified AST.Module.Name as ModuleName
import qualified AST.Pattern as P
import qualified AST.Type as Type
import qualified AST.Variable as Var
import qualified AST.Interface as Interface
import Elm.Utils ((|>))


-- ENVIRONMENT

data Environment = Env
    { _home     :: ModuleName.Canonical
    , _values   :: Dict Var.Canonical
    , _adts     :: Dict Var.Canonical
    , _aliases  :: Dict (Var.Canonical, [String], Type.Canonical')
    , _patterns :: Dict (Var.Canonical, Int)
    , _interfaces :: Map.Map String (Var.Canonical, Interface.ValidInterface)
    , _implementations :: Map.Map Type.Raw' [Interface.ValidImplementation]
    -- , _implementationTuples :: [(Type.Canonical', Interface.ValidInterface, Interface.ValidImplementation)]
    }


type Dict a =
    Map.Map String (Set.Set a)


fromPatches :: ModuleName.Canonical -> [Patch] -> Environment
fromPatches moduleName patches =
  addPatches
      patches
      (Env moduleName Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty)


addPattern :: P.Pattern ann var -> Environment -> Environment
addPattern pattern env =
  let patches =
        map (\x -> Value x (Var.local x)) (P.boundVarList pattern)
  in
      addPatches patches env

numberedTypeVars :: Type.Canonical -> Map.Map String Int
numberedTypeVars tp =
  let
    collectSubType :: [String] -> Map.Map String Int -> [String] -> (Map.Map String Int, [String])
    collectSubType [] mp res = (mp, res)
    collectSubType (s : ss) mp res =
      let
        num = (Map.findWithDefault 0 s mp) + 1
        mp' = Map.insert s num mp
        s' = s ++ "_" ++ show num
        (recMp, recRes) = collectSubType ss mp' res
      in
        (recMp, s' : recRes)

    -- first map here being var counter, second map being numbered var to arg index mapping
    collect :: Int -> Type.Canonical' -> Map.Map String Int -> (Map.Map String Int, Map.Map String Int)
    collect argNr tipe varCountMp =
        let
          vars = Type.collectVars' tipe
          (varCountMp', numberedVars) = collectSubType vars varCountMp []
        in
          (varCountMp', Map.fromList (map (flip (,) argNr) numberedVars))

    rec :: Type.Canonical' -> Int -> Map.Map String Int -> Map.Map String Int -> Map.Map String Int
    rec tipe argNr varCountMp argIndexMp =
      case tipe of
        Type.Lambda l r ->
            let
              (cCounts, cArgs) = collect argNr l varCountMp
              recArgs = rec r (argNr + 1) cCounts cArgs
            in
              Map.union cArgs recArgs
        _ ->
          Map.union argIndexMp (snd $ collect argNr tipe varCountMp)

  in
    rec (Type.qtype tp) 0 Map.empty Map.empty


addTypeRuleType :: Type.Canonical -> Environment -> Environment
addTypeRuleType tp env =
  let
    vars :: [String]
    vars = Type.collectVars tp

    collectPatches :: Map.Map String Int -> [String] -> [Patch]
    collectPatches _ [] = []
    collectPatches mp (s : ss) =
      let
        num = (Map.findWithDefault 0 s mp) + 1
        mp' = Map.insert s num mp
        s' = s ++ "_" ++ show num
      in
        Value s' (Var.local s') : collectPatches mp' ss

  in
    addPatches (collectPatches Map.empty vars) env

addTypeVars :: Type.Canonical -> Environment -> Environment
addTypeVars tp env =
  let
    vars = Type.collectVars tp
    toPatch s = Value s (Var.local s)
  in
    addPatches (map toPatch vars) env

-- PATCHES

data Patch
    = Value String Var.Canonical
    | Union String Var.Canonical
    | Alias String (Var.Canonical, [String], Type.Canonical')
    | Pattern String (Var.Canonical, Int)
    | Interface String (Var.Canonical, Interface.ValidInterface)
    | Implementation Type.Raw' Interface.ValidImplementation


-- ADD PATCH TO ENVIRONMENT

addPatches :: [Patch] -> Environment -> Environment
addPatches patches env =
  List.foldl' (flip addPatch) env patches


addPatch :: Patch -> Environment -> Environment
addPatch patch env =
  case patch of
    Value name var ->
        env { _values = insert name var (_values env) }

    Union name var ->
        env { _adts = insert name var (_adts env) }

    Alias name var ->
        env { _aliases = insert name var (_aliases env) }

    Pattern name var ->
        env { _patterns = insert name var (_patterns env) }

    Interface name ifc ->
        env
          { _interfaces = Map.insert name ifc (_interfaces env) }

    Implementation tipe impl ->
        env
          { _implementations = Map.insertWith (++) tipe [impl] (_implementations env) }


insert :: (Ord a) => String -> a -> Dict a -> Dict a
insert key value =
  Map.insertWith Set.union key (Set.singleton value)


-- PATCH HELPERS

builtinPatches :: [Patch]
builtinPatches =
  concat
    [ map (patch Value) (tupleNames ++ [saveEnvName])
    , map (patch Union) (tupleNames ++ ["List","Int","Float","Char","Bool","String"])
    , map (patternPatch) (tuples ++ [ ("::", 2), ("[]", 0) ])
    ]
  where
    patch mkPatch name =
        mkPatch name (Var.builtin name)

    patternPatch (name, args) =
        Pattern name (Var.builtin name, args)

    tupleNames =
        map fst tuples

    tuples =
        map toTuple [0..9]

    toTuple :: Int -> (String, Int)
    toTuple n =
        ("_Tuple" ++ show n, n)


-- TO TYPE DEALIASER

toDealiaser :: Environment -> Map.Map String String
toDealiaser (Env _ _ adts aliases _ _ _) =
  let
    dealiasAdt (localName, canonicalSet) =
      case Set.toList canonicalSet of
        [canonicalName] ->
            Just (Var.toString canonicalName, localName)
        _ ->
            Nothing

    dealiasAlias (localName, canonicalSet) =
      case Set.toList canonicalSet of
        [(canonicalName,_,_)] ->
            Just (Var.toString canonicalName, localName)
        _ ->
            Nothing

    adtPairs =
      Maybe.mapMaybe dealiasAdt (Map.toList adts)

    aliasPairs =
      Maybe.mapMaybe dealiasAlias (Map.toList aliases)

    add (key,value) dict =
      Map.insertWith (\v v' -> if length v < length v' then v else v') key value dict
  in
    adtPairs ++ aliasPairs
      |> foldr add Map.empty
