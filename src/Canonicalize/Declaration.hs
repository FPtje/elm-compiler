{-# OPTIONS_GHC -Wall #-}
module Canonicalize.Declaration (toExpr) where

import qualified AST.Declaration as D
import qualified AST.Expression.General as E
import qualified AST.Expression.Canonical as Canonical
import qualified AST.Interface as Interface
import qualified AST.Module.Name as ModuleName
import qualified AST.Pattern as P
import qualified AST.Type as T
import qualified AST.Variable as Var
import qualified Reporting.Annotation as A
import qualified Reporting.Region as R


toExpr :: ModuleName.Canonical -> [D.CanonicalDecl] -> [Canonical.Def]
toExpr moduleName decls =
  concatMap (toDefs moduleName) decls


toDefs :: ModuleName.Canonical -> D.CanonicalDecl -> [Canonical.Def]
toDefs moduleName (A.A (region,_) decl) =
  let
    typeVar =
      Var.fromModule moduleName

    loc expr =
      A.A region expr
  in
  case decl of
    D.Definition def ->
        [def]

    D.Datatype name tvars constructors ->
        concatMap toDefs' constructors
      where
        toDefs' (ctor, tipes) =
            let vars = take (length tipes) infiniteArgs
                tbody = T.App (T.Type (typeVar name)) (map T.Var tvars)
                body = loc . E.Data ctor $ map (loc . E.localVar) vars
            in
                [ definition ctor (buildFunction body vars) region (T.unqualified (foldr T.Lambda tbody tipes)) [] ]

    D.TypeAlias name tvars tipe@(T.Record fields Nothing) ->
        [ definition name (buildFunction record vars) region (T.unqualified (foldr T.Lambda result args)) [] ]
      where
        result =
          T.Aliased (typeVar name) (zip tvars (map T.Var tvars)) (T.Holey tipe)

        args =
          map snd fields

        vars =
          take (length args) infiniteArgs

        record =
          loc (E.Record (zip (map fst fields) (map (loc . E.localVar) vars)))

    -- Type aliases must be added to an extended equality dictionary,
    -- but they do not require any basic constraints.
    D.TypeAlias _ _ _ ->
        []

    D.Port (D.CanonicalPort impl) ->
        let body = loc (E.Port impl)
        in
        case impl of
          E.In name tipe ->
              [ definition name body region (T.unqualified $ T.getPortType tipe) [] ]

          E.Out name _expr tipe ->
              [ definition name body region (T.unqualified $ T.getPortType tipe) [] ]

          E.Task name _expr tipe ->
              [ definition name body region (T.unqualified $ T.getPortType tipe) [] ]

    D.IFace ifc ->
      map (interfaceToDecl ifc) (Interface.decls ifc)

    D.Impl impl ->
      map (changeName impl) $ Interface.implementations impl

    D.Sibling _ _ ->
        []

    -- no constraints are needed for fixity declarations
    D.Fixity _ _ _ ->
        []

-- | Change the name of an implementation's declaration
-- So it doesn't conflict with the
changeName :: Interface.CanonicalImplementation -> Canonical.Def -> Canonical.Def
changeName impl (Canonical.Definition facts (A.A rg (P.Var nm)) expr ann clstp@(Just (A.A _ tp)) rules) =
    Canonical.Definition facts (A.A rg (P.Var ("$" ++ nm ++ "$" ++ show tp ++ "$" ++ show (Interface.impltype impl)))) expr ann clstp rules

interfaceToDecl
    :: Interface.CanonicalInterface
    -> Interface.CanonicalInterfaceDecl
    -> Canonical.Def
interfaceToDecl ifc (A.A _ (Interface.IFType name (A.A rg tp) rules)) =
    definition (Var.name name) (A.A rg (E.Var name)) rg (T.addQualifiers tp [T.Qualifier (Interface.classname ifc) (Interface.interfacevar ifc)]) rules


infiniteArgs :: [String]
infiniteArgs =
  map (:[]) ['a'..'z'] ++ map (\n -> "_" ++ show (n :: Int)) [1..]


buildFunction :: Canonical.Expr -> [String] -> Canonical.Expr
buildFunction body@(A.A ann _) vars =
  foldr
      (\pattern expr -> A.A ann (E.Lambda pattern expr))
      body
      (map (A.A ann . P.Var) vars)


definition :: String -> Canonical.Expr -> R.Region -> T.Canonical -> [Canonical.TypeRule] -> Canonical.Def
definition name expr@(A.A ann _) region tipe rules =
  Canonical.Definition
    Canonical.dummyFacts
    (A.A ann (P.Var name))
    expr
    (Just (A.A region tipe))
    Nothing
    rules
