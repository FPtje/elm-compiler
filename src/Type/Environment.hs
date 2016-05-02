{-# OPTIONS_GHC -Wall #-}
module Type.Environment
    ( Environment
    , initialize
    , getType, freshDataScheme, ctorNames
    , addValues
    , instantiateType
    )
    where

import qualified Control.Monad.State as State
import qualified Data.List as List
import Data.Map ((!))
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified AST.Type as T
import qualified AST.Variable as V
import qualified AST.Expression.Canonical as Canonical
import qualified AST.Module as Module
import Control.Arrow (second)
import Type.Type


type TypeDict = Map.Map String Type
type VarDict = Map.Map String Variable
type RulesDict = Map.Map String [Canonical.TypeRule]


data Environment = Environment
    { _constructor :: Map.Map String (IO (Int, [Variable], [TermN Variable], TermN Variable))
    , _types :: TypeDict
    , _value :: TypeDict
    , _rules :: RulesDict
    }


initialize :: [Module.CanonicalAdt] -> RulesDict -> IO Environment
initialize datatypes rules =
  do  types <- makeTypes datatypes
      let env =
            Environment
              { _constructor = Map.empty
              , _value = Map.empty
              , _types = types
              , _rules = rules
              }
      return $ env { _constructor = makeConstructors env datatypes }


makeTypes :: [Module.CanonicalAdt] -> IO TypeDict
makeTypes datatypes =
  do  adts <- mapM makeImported datatypes
      bs   <- mapM makeBuiltin builtins
      return (Map.fromList (adts ++ bs))
  where
    makeImported :: (V.Canonical, Module.AdtInfo V.Canonical) -> IO (String, Type)
    makeImported (name, _) =
      do  tvar <- mkAtom name
          return (V.toString name, T.unqualified $ VarN tvar)

    makeBuiltin :: (String, Int) -> IO (String, Type)
    makeBuiltin (name, _) =
      do  name' <- mkAtom (V.builtin name)
          return (name, T.unqualified $ VarN name')

    builtins :: [(String, Int)]
    builtins =
        concat
          [ map tuple [0..9]
          , kind 1 ["List"]
          , kind 0 ["Int","Float","Char","String","Bool"]
          ]
      where
        tuple n = ("_Tuple" ++ show n, n)
        kind n names = map (\name -> (name, n)) names


makeConstructors
    :: Environment
    -> [Module.CanonicalAdt]
    -> Map.Map String (IO (Int, [Variable], [TermN Variable], TermN Variable))
makeConstructors env datatypes =
    Map.fromList builtins
  where
    list t =
      (_types env ! "List") <|| t

    inst :: Int -> ([TermN Variable] -> ([TermN Variable], TermN Variable)) -> IO (Int, [Variable], [TermN Variable], TermN Variable)
    inst numTVars tipe =
      do  vars <- mapM (\_ -> mkVar Nothing) [1..numTVars]
          let (args, result) = tipe (map (VarN) vars)
          return (length args, vars, args, result)

    tupleCtor n =
        let name = "_Tuple" ++ show n
        in  (name, inst n $ \vs -> (vs, foldl (<|) (T.qtype $ _types env ! name) vs))

    builtins :: [ (String, IO (Int, [Variable], [TermN Variable], TermN Variable)) ]
    builtins =
        [ ("[]", inst 1 $ \ [t] -> ([], T.qtype $ list (T.unqualified t)))
        , ("::", inst 1 $ \ [t] -> ([t, T.qtype $ list (T.unqualified t)], T.qtype $ list (T.unqualified t)))
        ] ++ map tupleCtor [0..9]
          ++ concatMap (ctorToType env) datatypes


ctorToType
    :: Environment
    -> (V.Canonical, Module.AdtInfo V.Canonical)
    -> [(String, IO (Int, [Variable], [TermN Variable], TermN Variable))]
ctorToType env (name, (tvars, ctors)) =
    zip (map (V.toString . fst) ctors) (map inst ctors)
  where
    inst :: (V.Canonical, [T.Canonical']) -> IO (Int, [Variable], [TermN Variable], TermN Variable)
    inst ctor =
      do  ((args, tipe), dict) <- State.runStateT (go ctor) Map.empty
          return (length args, Map.elems dict, args, tipe)


    go :: (V.Canonical, [T.Canonical']) -> State.StateT VarDict IO ([TermN Variable], TermN Variable)
    go (_, args) =
      do  types <- mapM (instantiator env . T.unqualified) args
          returnType <- instantiator env (T.unqualified $ T.App (T.Type name) (map T.Var tvars))
          return (map T.qtype types, T.qtype returnType)



-- ACCESS TYPES


get :: (Environment -> Map.Map String a) -> Environment -> String -> a
get subDict env key =
    Map.findWithDefault (error msg) key (subDict env)
  where
    msg = "Could not find type constructor `" ++ key ++ "` while checking types."


getType :: Environment -> String -> Type
getType =
  get _types


freshDataScheme :: Environment -> String -> IO (Int, [Variable], [TermN Variable], TermN Variable)
freshDataScheme =
  get _constructor


ctorNames :: Environment -> [String]
ctorNames env =
  Map.keys (_constructor env)


-- UPDATE ENVIRONMENT


addValues :: Environment -> [(String, Variable)] -> Environment
addValues env newValues =
  env
    { _value =
        List.foldl'
          (\dict (name, var) -> Map.insert name (T.unqualified $ VarN var) dict) -- TODO: something better than unqualified
          (_value env)
          newValues
    }



-- INSTANTIATE TYPES


instantiateType :: Environment -> T.Canonical -> VarDict -> IO ([Variable], Type)
instantiateType env sourceType dict =
  do  (tipe, dict') <- State.runStateT (instantiator env sourceType) dict
      return (Map.elems dict', tipe)


instantiator :: Environment -> T.Canonical -> State.StateT VarDict IO Type
instantiator env sourceType =
    instantiatorHelp env Set.empty sourceType


instantiatorHelp :: Environment -> Set.Set String -> T.Canonical -> State.StateT VarDict IO Type
instantiatorHelp env aliasVars (T.QT stquals sourceType) =
    let go = instantiatorHelp env aliasVars . T.unqualified
        quals = mapM (\(T.Qualifier cls var) -> T.Qualifier cls . T.qtype <$> instantiator env (T.unqualified var)) stquals
    in
    case sourceType of
      T.Lambda t1 t2 ->
          T.addQualifiers <$> ((==>) <$> go t1 <*> go t2) <*> quals

      T.Var name ->
          if Set.member name aliasVars then
              T.addQualifiers (T.unqualified (PlaceHolder name)) <$> quals

          else
              do  dict <- State.get
                  case Map.lookup name dict of
                    Just variable ->
                        T.addQualifiers (T.unqualified (VarN variable)) <$> quals

                    Nothing ->
                        do  variable <- State.liftIO (mkNamedVar name)
                            State.put (Map.insert name variable dict)
                            T.addQualifiers (T.unqualified (VarN variable)) <$> quals

      T.Aliased name args aliasType ->
          do  targs <- mapM (\(arg,tipe) -> (,) arg <$> go tipe) args
              T.QT _ realType <-
                  case aliasType of
                    T.Filled tipe ->
                        instantiatorHelp env Set.empty (T.unqualified tipe)

                    T.Holey tipe ->
                        instantiatorHelp env (Set.fromList (map fst args)) (T.unqualified tipe)

              T.addQualifiers (T.unqualified $ AliasN name (map (second T.qtype) targs) realType) <$> quals

      T.Type name ->
          case Map.lookup (V.toString name) (_types env) of
            Just tipe ->
                return tipe

            Nothing ->
                error $
                  "Could not find type constructor `" ++
                  V.toString name ++ "` while checking types."

      T.App func args ->
          do  tfunc <- go func
              targs <- mapM go args
              return $ foldl (<||) tfunc targs

      T.Record fields ext ->
          do  tfields <- traverse go (Map.fromList fields)
              text <-
                  case ext of
                    Nothing ->
                        return $ TermN EmptyRecord1

                    Just extType ->
                        T.qtype <$> go extType

              T.addQualifiers (T.unqualified $ TermN (Record1 (Map.map T.qtype tfields) text)) <$> quals
