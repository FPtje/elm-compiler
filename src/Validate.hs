{-# OPTIONS_GHC -Wall #-}
module Validate (declarations) where

import Control.Monad (foldM, when)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Foldable as F
import qualified Data.Traversable as T

import AST.Expression.General as Expr
import qualified AST.Expression.Source as Source
import qualified AST.Expression.Valid as Valid
import qualified AST.Variable as Var
import qualified AST.Declaration as D
import qualified AST.Pattern as Pattern
import qualified AST.Type as Type
import qualified AST.Interface as Interface
import qualified AST.Rule as Rule
import Elm.Utils ((|>))
import qualified Reporting.Annotation as A
import qualified Reporting.Error.Syntax as Error
import qualified Reporting.Region as R
import qualified Reporting.Result as Result

-- VALIDATE DECLARATIONS

declarations
    :: Bool
    -> [D.SourceDecl]
    -> Result.Result wrn Error.Error [D.ValidDecl]
declarations isRoot sourceDecls =
  do  validDecls <- validateDecls Nothing sourceDecls
      (\_ _ -> validDecls)
        <$> declDuplicates validDecls
        <*> T.traverse (checkDecl isRoot) validDecls


validateDecls
    :: Maybe String
    -> [D.SourceDecl]
    -> Result.Result wrn Error.Error [D.ValidDecl]
validateDecls maybeComment sourceDecls =
  case sourceDecls of
    [] ->
        return []

    sourceDecl : decls ->
        case sourceDecl of
          D.Comment comment ->
              validateDecls (Just comment) decls

          D.Decl decl ->
              validateDeclsHelp maybeComment decl decls


validateDeclsHelp
    :: Maybe String
    -> A.Located D.SourceDecl'
    -> [D.SourceDecl]
    -> Result.Result wrn Error.Error [D.ValidDecl]
validateDeclsHelp comment (A.A region decl) decls =
  let addRest validDecl =
        (:) (A.A (region, comment) validDecl)
          <$> validateDecls Nothing decls
  in
  case decl of
    D.Datatype name tvars ctors ->
        addRest (D.Datatype name tvars ctors)

    D.TypeAlias name tvars alias ->
        addRest (D.TypeAlias name tvars alias)

    D.Fixity assoc prec op ->
        addRest (D.Fixity assoc prec op)

    D.Definition def ->
        defHelp comment def decls

    D.Port port ->
        portHelp comment region port decls

    D.IFace intf ->
        do
          newintf <- ifaceHelp region intf
          addRest (D.IFace newintf)

    D.Impl impl ->
      do
        newimpl <- implHelp comment impl
        addRest (D.Impl newimpl)

    {-D.TypeRule pats rules ->
      do
        pats' <- mapM validatePattern pats
        addRest (D.TypeRule pats' (typeRuleHelp rules))-}

    D.Sibling from to ->
        addRest (D.Sibling from to)


typeRuleHelp :: [Rule.SourceRule] -> [Rule.ValidRule]
typeRuleHelp rs = [A.A rg (toValid r) | (A.A rg r) <- rs]
  where
    toValid :: Rule.SourceRule' -> Rule.ValidRule'
    toValid (Rule.SubRule var) = Rule.SubRule (Var.Raw var)
    toValid (Rule.Qualifier (Type.Qualifier (A.A crg classNm) var) expl) = Rule.Qualifier (Type.Qualifier (A.A crg $ Var.Raw classNm) (Var.Raw var)) expl
    toValid constr = constr { Rule.lhs = Var.Raw (Rule.lhs constr) }


validateIFaceDecls :: [Source.Def] -> Result.Result wrn Error.Error [Interface.ValidInterfaceDecl]
validateIFaceDecls [] = Result.ok []
validateIFaceDecls (A.A region def : defs) =
  let
    collectRules _ _ [] = Result.ok ([], [])
    collectRules patCounts name defs'@(A.A rg def' : rest) =
      case def' of
        Source.TypeRule pats@((A.A _ (Pattern.Var name')) : _) rules ->
          if name == name' then
            do
              pats' <- mapM validatePattern pats
              rule <- checkRule $ A.A rg $ Valid.TypeRule pats' (typeRuleHelp rules)

              when (length pats' `Set.member` patCounts) $
                Result.throw rg Error.TypeRuleDuplicate

              (otherRules, rest') <- collectRules (Set.insert (length pats') patCounts) name rest
              Result.ok (rule : otherRules, rest')
          else
            Result.throw region (Error.TypeRuleNotBetweenTypeAndDef name) -- TODO: Better, interface specific error

        _ -> Result.ok ([], defs')
  in
    case def of
      Source.TypeRule ((A.A _ (Pattern.Var name)) : _) _ ->
          Result.throw region (Error.TypeRuleNotBetweenTypeAndDef name) -- TODO: Better, interface specific error

      Source.TypeAnnotation name tipe ->
        do
          (rules, rest) <- collectRules Set.empty name defs
          otherDefs <- validateIFaceDecls rest

          Result.ok $ A.A region (Interface.IFType name tipe rules) : otherDefs



ifaceHelp
    :: R.Region
    -> Interface.SourceInterface
    -> Result.Result wrn Error.Error Interface.ValidInterface
ifaceHelp region (Interface.Interface quals (A.A rg classNm) var decls) =
  do
    newQuals <- mapM qualifierHelp quals
    -- TODO: Check for duplicate qualifiers
    -- TODO: make sure class var is mentioned in all sigs
    -- TODO: Check whether qualifier doesn't contain classname itself
    let badQuals = filter (\(Type.Qualifier _ var') -> var /= var') quals
    let errs = map (\(Type.Qualifier (A.A _ cls) var') -> Error.MessyTypeVarsInInterface classNm cls var' var) badQuals
    mapM_ (Result.throw region) errs

    newDecls <- validateIFaceDecls decls

    return $ Interface.Interface newQuals (A.A rg $ Var.Raw classNm) (Var.Raw var) newDecls

implHelp
    :: Maybe String
    -> Interface.Implementation' (A.Located String) String Type.Raw' Source.Def
    -> Result.Result wrn Error.Error (Interface.Implementation' (A.Located Var.Raw) Var.Raw Type.Raw' Valid.Def)
implHelp _ (Interface.Implementation quals (A.A rg classNm) tipe defs) =
  do
    newQuals <- mapM qualifierHelp quals
    newDefs <- definitions defs
    return $ Interface.Implementation newQuals (A.A rg $ Var.Raw classNm) tipe newDefs

qualifierHelp
    :: Type.Qualifier' (A.Located String) String
    -> Result.Result wrn Error.Error (Type.Qualifier' (A.Located Var.Raw) Var.Raw)
qualifierHelp (Type.Qualifier (A.A rg classNm) var) =
  return $ Type.Qualifier (A.A rg $ Var.Raw classNm) (Var.Raw var)

-- VALIDATE DEFINITIONS IN DECLARATIONS

defHelp
    :: Maybe String
    -> Source.Def
    -> [D.SourceDecl]
    -> Result.Result wrn Error.Error [D.ValidDecl]
defHelp comment (A.A region def) decls =
  let addRest def' rest =
        (:) (A.A (region, comment) (D.Definition def'))
          <$> validateDecls Nothing rest

      typeRuledDef name _ _ [] = Result.throw region (Error.TypeWithoutDefinition name)
      typeRuledDef name tipe valids (d : rest) =
          case d of
            D.Decl (A.A _ (D.Definition (A.A rg (Source.TypeRule pats@((A.A _ (Pattern.Var name')) : _) rules))))
              | name == name'->
              do
                pats' <- mapM validatePattern pats
                rule <- checkRule $ A.A rg $ Valid.TypeRule pats' (typeRuleHelp rules)

                typeRuledDef name tipe (rule : valids) rest
            D.Decl (A.A _ (D.Definition (A.A _ (Source.Definition pat@(A.A _ (Pattern.Var name')) expr))))
              | name == name' ->
              do
                expr' <- expression expr
                let def' = Valid.Definition pat expr' (Just tipe) valids
                return (def', rest)
            _ -> Result.throw region (Error.TypeWithoutDefinition name)
  in
  case def of
    Source.Definition pat expr ->
        do  expr' <- expression expr
            let def' = Valid.Definition pat expr' Nothing []
            checkDefinition def'
            addRest def' decls

    Source.TypeRule ((A.A _ (Pattern.Var name)) : _) _ ->
        Result.throw region (Error.TypeRuleNotBetweenTypeAndDef name)

    Source.TypeAnnotation name tipe ->
        case decls of
          D.Decl (A.A _ (D.Definition (A.A _
            (Source.Definition pat@(A.A _ (Pattern.Var name')) expr)))) : rest
              | name == name' ->
                  do  expr' <- expression expr
                      let def' = Valid.Definition pat expr' (Just tipe) []
                      checkDefinition def'
                      addRest def' rest

          D.Decl (A.A _ (D.Definition (A.A _ (Source.TypeRule _ _)))) : _ ->
              do
                (def', rest) <- typeRuledDef name tipe [] decls
                addRest def' rest

          _ ->
              Result.throw region (Error.TypeWithoutDefinition name)

-- Checks a rule
-- Inserts missing subrules
-- Checks whether each argument of the function appears in the type rules
checkRule
    :: Valid.TypeRule
    -> Result.Result wrn Error.Error Valid.TypeRule
checkRule (A.A region (Valid.TypeRule pats rules)) =
  let
    args :: [Pattern.RawPattern]
    args = tail pats

    ret :: Pattern.RawPattern
    ret =  A.A undefined (Pattern.Var "return")

    ruleCoversPat :: Pattern.RawPattern -> Rule.ValidRule -> Bool
    ruleCoversPat (A.A _ (Pattern.Var pat)) (A.A _ (Rule.SubRule (Var.Raw var))) = var == pat
    ruleCoversPat _ _ = False

    patIsCovered :: [Rule.ValidRule] -> Pattern.RawPattern -> Bool
    patIsCovered ruls pat = any (ruleCoversPat pat) ruls

    patToRule :: Pattern.RawPattern -> Rule.ValidRule
    patToRule (A.A rg (Pattern.Var pat)) = A.A rg $ Rule.SubRule (Var.Raw pat)

    missingArgs :: [Rule.ValidRule]
    missingArgs = map patToRule . filter (not . patIsCovered rules) $ args

    missingRet :: [Rule.ValidRule]
    missingRet = [patToRule ret | not (patIsCovered rules ret)]

    leftHandSides :: Set.Set String
    leftHandSides = Set.fromList [ var | A.A _ (Rule.Constraint (Var.Raw var) _ _) <- rules ]

    missingArgsInConstraints :: [String]
    missingArgsInConstraints =
      [ arg | A.A _ (Pattern.Var arg) <- (ret : args), not $ Set.member arg leftHandSides ]


    -- Check for duplicate subrules
    allSubRules :: [(R.Region, String)]
    allSubRules = [ (rg, var) | A.A rg (Rule.SubRule (Var.Raw var)) <- rules ]

    getDuplicates :: (Set.Set String, [(R.Region, Error.Error)]) -> (R.Region, String) -> (Set.Set String, [(R.Region, Error.Error)])
    getDuplicates (s, res) (rg, str) = (Set.insert str s, if str `Set.member` s then (rg, Error.TypeRuleDuplicateSubRule str) : res else res)

    duplicates :: [(R.Region, Error.Error)]
    duplicates = snd $ foldl getDuplicates (Set.empty, []) allSubRules
  in
    do
      when (not $ null missingArgsInConstraints) $
        Result.throw region (Error.TypeRuleMissingArgs missingArgsInConstraints)

      mapM (uncurry Result.throw) duplicates

      return $ A.A region $ Valid.TypeRule pats (missingArgs ++ rules ++ missingRet)

-- VALIDATE PORTS IN DECLARATIONS

portHelp
    :: Maybe String
    -> R.Region
    -> D.SourcePort
    -> [D.SourceDecl]
    -> Result.Result wrn Error.Error [D.ValidDecl]
portHelp comment region port decls =
  let addRest port' rest =
        (:) (A.A (region,comment) (D.Port port'))
          <$> validateDecls Nothing rest
  in
  case port of
    D.PortDefinition name _ ->
        Result.throw region (Error.PortWithoutAnnotation name)

    D.PortAnnotation name tipe ->
        case decls of
          D.Decl (A.A _ (D.Port (D.PortDefinition name' expr))) : rest
              | name == name' ->
                  do  expr' <- expression expr
                      let port' = D.Out name expr' tipe
                      addRest port' rest

          _ ->
              addRest (D.In name tipe) decls


-- VALIDATE DEFINITIONS

definitions :: [Source.Def] -> Result.Result wrn Error.Error [Valid.Def]
definitions sourceDefs =
  do  validDefs <- definitionsHelp sourceDefs
      let patterns = map (\(Valid.Definition p _ _ _) -> p) validDefs
      defDuplicates patterns
      return validDefs


definitionsHelp :: [Source.Def] -> Result.Result wrn Error.Error [Valid.Def]
definitionsHelp sourceDefs =
  case sourceDefs of
    [] ->
        return []

    A.A _ (Source.Definition pat expr) : rest ->
        do  expr' <- expression expr
            let def = Valid.Definition pat expr' Nothing []
            checkDefinition def
            (:) def <$> definitionsHelp rest

    A.A region (Source.TypeAnnotation name tipe) : rest ->
        case rest of
          A.A _ (Source.Definition pat@(A.A _ (Pattern.Var name')) expr) : rest'
              | name == name' ->
                  do  expr' <- expression expr
                      let def = Valid.Definition pat expr' (Just tipe) []
                      checkDefinition def
                      (:) def <$> definitionsHelp rest'

          _ ->
              Result.throw region (Error.TypeWithoutDefinition name)

    A.A region (Source.TypeRule _ _) : _ ->
        Result.throw region Error.TypeRuleNotTopLevel


checkDefinition :: Valid.Def -> Result.Result wrn Error.Error ()
checkDefinition (Valid.Definition pattern body _ _) =
  case fst (Expr.collectLambdas body) of
    [] ->
        return ()

    args ->
        case pattern of
          A.A _ (Pattern.Var _) ->
              return ()

          _ ->
              let
                (A.A start _) = pattern
                (A.A end _) = last args
              in
                Result.throw (R.merge start end) (Error.BadFunctionName (length args))


-- VALIDATE EXPRESSIONS

expression :: Source.Expr -> Result.Result wrn Error.Error Valid.Expr
expression (A.A ann sourceExpression) =
  A.A ann <$>
  case sourceExpression of
    Var x ->
        return (Var x)

    Lambda pattern body ->
        Lambda
            <$> validatePattern pattern
            <*> expression body

    Binop op leftExpr rightExpr ->
        Binop op
          <$> expression leftExpr
          <*> expression rightExpr

    Case e branches ->
        Case
          <$> expression e
          <*> T.traverse (\(p,b) -> (,) <$> validatePattern p <*> expression b) branches

    Data name args ->
        Data name <$> T.traverse expression args

    Literal lit ->
        return (Literal lit)

    Range lowExpr highExpr ->
        Range
          <$> expression lowExpr
          <*> expression highExpr

    ExplicitList expressions ->
        ExplicitList
          <$> T.traverse expression expressions

    App funcExpr argExpr ->
        App
          <$> expression funcExpr
          <*> expression argExpr

    If branches finally ->
        If
          <$> T.traverse both branches
          <*> expression finally

    Access record field ->
        Access
          <$> expression record
          <*> return field

    Update record fields ->
        Update
          <$> expression record
          <*> T.traverse second fields

    Record fields ->
        let
          checkDups seenFields (field,_) =
              if Set.member field seenFields then
                  Result.throw ann (Error.DuplicateFieldName field)

              else
                  return (Set.insert field seenFields)
        in
          do  _ <- foldM checkDups Set.empty fields
              Record <$> T.traverse second fields

    Let defs body ->
        Let
          <$> definitions defs
          <*> expression body

    GLShader uid src gltipe ->
        return (GLShader uid src gltipe)

    Port impl ->
        Port <$>
          case impl of
            In name tipe ->
                return (In name tipe)

            Out name expr tipe ->
                do  expr' <- expression expr
                    return (Out name expr' tipe)

            Task name expr tipe ->
                do  expr' <- expression expr
                    return (Task name expr' tipe)


second :: (a, Source.Expr) -> Result.Result wrn Error.Error (a, Valid.Expr)
second (value, expr) =
    (,) value <$> expression expr


both
    :: (Source.Expr, Source.Expr)
    -> Result.Result wrn Error.Error (Valid.Expr, Valid.Expr)
both (expr1, expr2) =
    (,) <$> expression expr1 <*> expression expr2


-- VALIDATE PATTERNS

validatePattern :: Pattern.RawPattern -> Result.Result wrn Error.Error Pattern.RawPattern
validatePattern pattern =
  do  detectDuplicates Error.BadPattern (Pattern.boundVars pattern)
      return pattern


-- DETECT DUPLICATES

detectDuplicates
    :: (String -> Error.Error)
    -> [A.Located String]
    -> Result.Result wrn Error.Error ()
detectDuplicates tag names =
  let add (A.A region name) dict =
          Map.insertWith (++) name [region] dict

      makeGroups pairs =
          Map.toList (foldr add Map.empty pairs)

      check (name, regions) =
        case regions of
          _ : region : _ ->
              Result.throw region (tag name)

          _ ->
              return ()
  in
      F.traverse_ check (makeGroups names)


defDuplicates
    :: [Pattern.RawPattern]
    -> Result.Result wrn Error.Error ()
defDuplicates patterns =
  concatMap Pattern.boundVars patterns
    |> detectDuplicates Error.DuplicateDefinition


declDuplicates :: [D.ValidDecl] -> Result.Result wrn Error.Error ()
declDuplicates decls =
  let (valueLists, typeLists, sibLists) = unzip3 (map extractValues decls)
  in
      (\_ _ _ -> ())
        <$> detectDuplicates Error.DuplicateValueDeclaration (concat valueLists)
        <*> detectDuplicates Error.DuplicateTypeDeclaration (concat typeLists)
        <*> detectDuplicates Error.DuplicateSiblingDeclaration (concat sibLists)


extractValues :: D.ValidDecl -> ([A.Located String], [A.Located String], [A.Located String])
extractValues (A.A (region, _) decl) =
  case decl of
    D.Definition (Valid.Definition pattern _ _ _) ->
        ( Pattern.boundVars pattern
        , []
        , []
        )

    D.Datatype name _ ctors ->
        ( map (A.A region . fst) ctors
        , [A.A region name]
        , []
        )

    D.TypeAlias name _ (A.A _ (Type.RRecord _ _)) ->
        ( [A.A region name]
        , [A.A region name]
        , []
        )

    D.TypeAlias name _ _ ->
        ( []
        , [A.A region name]
        , []
        )

    D.Port port ->
        ( [A.A region (D.validPortName port)]
        , []
        , []
        )

    -- TODO: duplicate detection
    D.IFace _ ->
        ( []
        , []
        , []
        )

    -- TODO: duplicate detection
    D.Impl _ ->
        ( []
        , []
        , []
        )

    D.Sibling from to ->
        ( []
        , []
        , [A.A region (from ++ " resembles " ++ to)]
        )

    D.Fixity _ _ _ ->
        ( []
        , []
        , []
        )


-- UNBOUND TYPE VARIABLES

checkDecl :: Bool -> D.ValidDecl -> Result.Result wrn Error.Error ()
checkDecl isRoot (A.A (region,_) decl) =
  case decl of
    D.Definition _ ->
        return ()

    D.Datatype name boundVars ctors ->
        case diff boundVars (concatMap freeVars (concatMap snd ctors)) of
          (_, []) ->
              return ()

          (_, unbound) ->
              Result.throw region
                (Error.UnboundTypeVarsInUnion name boundVars unbound)

    D.TypeAlias name boundVars tipe ->
        case diff boundVars (freeVars tipe) of
          ([], []) ->
              return ()

          ([], unbound) ->
              Result.throw region
                (Error.UnboundTypeVarsInAlias name boundVars unbound)

          (unused, []) ->
              Result.throw region
                (Error.UnusedTypeVarsInAlias name boundVars unused)

          (unused, unbound) ->
              Result.throw region
                (Error.MessyTypeVarsInAlias name boundVars unused unbound)

    D.Port _ ->
        if isRoot then
            return ()

        else
            Result.throw region Error.UnexpectedPort

    D.IFace {} ->
        return ()

    D.Impl {} ->
        return ()

    D.Sibling _ _ ->
        return ()
    D.Fixity _ _ _ ->
        return ()


diff :: [String] -> [A.Located String] -> ([String], [String])
diff left right =
  let
    leftSet =
      Set.fromList left

    rightSet =
      Set.fromList (map A.drop right)
  in
    ( Set.toList (Set.difference leftSet rightSet)
    , Set.toList (Set.difference rightSet leftSet)
    )



freeVars :: Type.Raw' -> [A.Located String]
freeVars (A.A region tipe) =
    case tipe of
      Type.RLambda t1 t2 ->
          freeVars t1 ++ freeVars t2

      Type.RVar x ->
          [A.A region x]

      Type.RType _ ->
          []

      Type.RApp t ts ->
          concatMap freeVars (t:ts)

      Type.RRecord fields ext ->
          maybe [] freeVars ext
          ++ concatMap (freeVars . snd) fields

