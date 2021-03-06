{-# OPTIONS_GHC -Wall #-}
module Canonicalize.Type (tipe, tipe') where

import qualified Data.Traversable as Trav

import qualified AST.Type as T
import qualified AST.Variable as Var

import qualified Reporting.Annotation as A
import qualified Reporting.Error.Canonicalize as Error
import qualified Reporting.Region as R
import qualified Canonicalize.Environment as Env
import qualified Canonicalize.Result as Result
import qualified Canonicalize.Variable as Canonicalize
import qualified Reporting.Error.Canonicalize as CError
import qualified Reporting.Error.Helpers as ErrorHelp

import qualified Data.Map as Map

tipe
    :: Env.Environment
    -> T.Raw
    -> Result.ResultErr T.Canonical
tipe env (T.QT quals typ) =
    Result.map (canonicalizeQualifier env) quals
      `Result.andThen` \newQuals ->
        tipe' env typ
          `Result.andThen` \newtyp ->
            Result.ok $ T.QT newQuals newtyp

tipe'
    :: Env.Environment
    -> T.Raw'
    -> Result.ResultErr T.Canonical'
tipe' env typ@(A.A region typ') =
    let go = tipe' env
        goSnd (name,t) =
            (,) name <$> go t
    in
    case typ' of
      T.RVar x ->
          Result.ok (T.Var x)

      T.RType _ ->
          canonicalizeApp region env typ []

      T.RApp t ts ->
          canonicalizeApp region env t ts

      T.RLambda a b ->
          T.Lambda <$> go a <*> go b

      T.RRecord fields ext ->
          T.Record <$> Trav.traverse goSnd fields <*> Trav.traverse go ext


canonicalizeQualifier
    :: Env.Environment
    -> T.Qualifier' (A.Located String) String
    -> Result.ResultErr (T.Qualifier' Var.Canonical T.Canonical')
canonicalizeQualifier env (T.Qualifier (A.A rg classref) var) =
  case Map.lookup classref (Env._interfaces env) of
    Just (ifvar, _) -> Result.ok $ T.Qualifier ifvar (T.Var var)
    Nothing -> Result.err (A.A rg (CError.Export classref $ ErrorHelp.nearbyNames id classref (map fst . Map.toList $ Env._interfaces env)))


canonicalizeApp
    :: R.Region
    -> Env.Environment
    -> T.Raw'
    -> [T.Raw']
    -> Result.ResultErr T.Canonical'
canonicalizeApp region env f args =
  case f of
    A.A _ (T.RType (Var.Raw rawName)) ->
        Canonicalize.tvar region env rawName
          `Result.andThen` canonicalizeWithTvar

    _ ->
        T.App <$> tipe' env f <*> Trav.traverse (tipe' env) args

  where
    canonicalizeWithTvar tvar =
        case tvar of
          Right alias ->
              canonicalizeAlias region env alias args

          Left name ->
              case args of
                [] ->
                    Result.ok (T.Type name)
                _ ->
                    T.App (T.Type name) <$> Trav.traverse (tipe' env) args


canonicalizeAlias
    :: R.Region
    -> Env.Environment
    -> (Var.Canonical, [String], T.Canonical')
    -> [T.Raw']
    -> Result.ResultErr T.Canonical'
canonicalizeAlias region env (name, tvars, dealiasedTipe) types =
  if typesLen /= tvarsLen
    then Result.err (A.A region (Error.alias name tvarsLen typesLen))
    else toAlias <$> Trav.traverse (tipe' env) types
  where
    typesLen = length types
    tvarsLen = length tvars

    toAlias canonicalTypes =
        T.Aliased name (zip tvars canonicalTypes) (T.Holey dealiasedTipe)
