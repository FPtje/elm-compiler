module Canonicalize (module') where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import qualified Data.Traversable as T
import qualified Data.Foldable as T
import Control.Monad (when)

import AST.Expression.General (Expr'(..), dummyLet)
import AST.Module (Body(..))
import Elm.Utils ((|>))

import qualified AST.Declaration as D
import qualified AST.Expression.General as E
import qualified AST.Expression.Valid as Valid
import qualified AST.Expression.Canonical as Canonical
import qualified AST.Expression.Source as Source
import qualified AST.Module as Module
import qualified AST.Module.Name as ModuleName
import qualified AST.Pattern as P
import qualified AST.Type as Type
import qualified AST.Interface as Interface
import qualified AST.Variable as Var
import qualified AST.Rule as Rule
import qualified Docs.AST as Docs
import qualified Docs.Centralize as Docs
import qualified Reporting.Annotation as A
import qualified Reporting.Error as Error
import qualified Reporting.Error.Canonicalize as CError
import qualified Reporting.Error.Helpers as ErrorHelp
import qualified Reporting.Region as Region
import qualified Reporting.Result as R
import qualified Reporting.Warning as Warning
import qualified Canonicalize.Declaration as Decls
import qualified Canonicalize.Environment as Env
import qualified Canonicalize.Port as Port
import qualified Canonicalize.Result as Result
import qualified Canonicalize.Setup as Setup
import qualified Canonicalize.Sort as Sort
import qualified Canonicalize.Type as Canonicalize
import qualified Canonicalize.Variable as Canonicalize
import qualified AST.Expression.Source as Source

-- MODULES

module'
    :: [ModuleName.Canonical]
    -> Module.Interfaces
    -> Module.ValidModule
    -> R.Result Warning.Warning Error.Error Module.CanonicalModule
module' canonicalImports interfaces modul =
  let
    importDict =
      canonicalImports
        |> map (\cName -> (ModuleName._module cName, cName))
        |> Map.fromList

    (Result.Result uses rawResults) =
      moduleHelp importDict interfaces modul
  in
      case rawResults of
        Result.Ok (env, almostCanonicalModule) ->
            R.addDealiaser (Env.toDealiaser env) $
              filterImports uses almostCanonicalModule

        Result.Err msgs ->
            R.throwMany (map (A.map Error.Canonicalize) msgs)


type AlmostCanonicalModule =
    Module.Module
      Docs.Centralized
      ([Module.DefaultImport], [Module.UserImport])
      [Var.Value]
      (Module.Body Canonical.Expr)


moduleHelp
    :: Map.Map ModuleName.Raw ModuleName.Canonical
    -> Module.Interfaces
    -> Module.ValidModule
    -> Result.ResultErr (Env.Environment, AlmostCanonicalModule)
moduleHelp importDict interfaces modul@(Module.Module _ _ comment exports _ decls) =
    canonicalModule
      <$> canonicalDeclsResult
      <*> resolveExports locals exports
  where
    canonicalModule (env, canonicalDecls) canonicalExports =
        (,) env $
        modul
          { Module.docs = A.map (fmap (Docs.centralize canonicalDecls)) comment
          , Module.exports = canonicalExports
          , Module.body = body canonicalDecls
          }

    locals :: [Var.Value]
    locals =
        concatMap declToValue decls

    canonicalDeclsResult =
        Setup.environment importDict interfaces modul
          `Result.andThen` \env -> (,) env <$> T.traverse (declaration (Module.name modul) env) decls

    body :: [D.CanonicalDecl] -> Module.Body Canonical.Expr
    body decls =
        let nakedDecls = map A.drop decls
            ifces = [ i | D.IFace i <- nakedDecls ]
        in
        Module.Body
          { program =
              let expr = Decls.toExpr (Module.name modul) decls
              in
                  Sort.definitions (dummyLet expr)

          , types =
              Map.empty

          , datatypes =
              Map.fromList [ (name,(vars,ctors)) | D.Datatype name vars ctors <- nakedDecls ]

          , siblings =
              (
                Map.fromList
                [((from, to), rg) | A.A (rg, _) (D.Sibling from to) <- decls]
              ,
                foldl (
                  \mp (from, to) ->
                    Map.insert from
                    (to `Set.insert` Map.findWithDefault Set.empty from mp) mp
                  )
                Map.empty
                [(from, to) | D.Sibling from to <- nakedDecls]
              )

          , fixities =
              [ (assoc,level,op) | D.Fixity assoc level op <- nakedDecls ]

          , aliases =
              Map.fromList [ (name,(tvs,alias)) | D.TypeAlias name tvs alias <- nakedDecls ]

          , interfaces =
              ifces

          , implementations =
              [ (getMatchingIFace ifces i, i) | D.Impl i <- nakedDecls ]

          , typeRules =
              Map.fromList $ [ (name, rules) | D.Definition (Canonical.Definition _ (A.A _ (P.Var name)) _ _ _ rules) <- nakedDecls, not (null rules) ]  ++ interfaceRules ifces

          , ports =
              [ E.portName impl | D.Port (D.CanonicalPort impl) <- nakedDecls ]
          }


interfaceRules :: [Interface.CanonicalInterface] -> [(String, [Canonical.TypeRule])]
interfaceRules ifcs =
  let
    ifrule :: Interface.CanonicalInterface -> [(String, [Canonical.TypeRule])]
    ifrule ifc = [ (Var.toString name, rules) | A.A _ (Interface.IFType name _ rules) <- Interface.decls ifc]

  in
    concatMap ifrule ifcs

getMatchingIFace :: [Interface.CanonicalInterface]
               -> Interface.CanonicalImplementation
               -> Interface.CanonicalInterface
getMatchingIFace ifces impl = head $ filter (\ifc -> Interface.classname ifc == Interface.classref impl) ifces

-- IMPORTS

filterImports
    :: Set.Set ModuleName.Raw
    -> AlmostCanonicalModule
    -> R.Result Warning.Warning e Module.CanonicalModule
filterImports uses modul@(Module.Module _ _ _ _ (defaults, imports) _) =
  do  reducedImports <-
          Maybe.catMaybes <$> T.traverse checkImport imports

      return $ modul
        { Module.imports =
              Set.toList (Set.fromList (map fst defaults ++ reducedImports))
        }
  where
    checkImport (A.A region (name, _method)) =
      if Set.member name uses then
          return (Just name)
      else
          do  R.warn region (Warning.UnusedImport name)
              return Nothing


-- EXPORTS

resolveExports
    :: [Var.Value]
    -> Var.Listing (A.Located Var.Value)
    -> Result.ResultErr [Var.Value]
resolveExports fullList (Var.Listing partialList open) =
  if open then
    Result.ok fullList
  else
    let
      (allValues, allAliases, allAdts) =
          maybeUnzip3 (map splitValue fullList)

      (values, aliases, adts) =
          maybeUnzip3 (map splitLocatedValue partialList)

      adtTypes =
          map fst allAdts
    in
      (\xs ys zs _ -> xs ++ ys ++ zs)
        <$> T.traverse (getValueExport allValues (Set.fromList allValues)) values
        <*> (concat <$> T.traverse (getAliasExport allValues allAliases adtTypes) aliases)
        <*> T.traverse (getAdtExport allAdts adtTypes) adts
        <*> allUnique partialList


getValueExport
    :: [String]
    -> Set.Set String
    -> A.Located String
    -> Result.ResultErr Var.Value
getValueExport allValues allValuesSet (A.A region name) =
  if Set.member name allValuesSet then
    Result.ok (Var.Value name)
  else
    manyNotFound region [name] allValues


getAliasExport
    :: [String]
    -> [String]
    -> [String]
    -> A.Located String
    -> Result.ResultErr [Var.Value]
getAliasExport allValues allAliases adtTypes (A.A region alias) =
  if alias `elem` allAliases then

      Result.ok $ (:) (Var.Alias alias) $
          if alias `elem` allValues then [Var.Value alias] else []

  else if List.elem alias adtTypes then

      Result.ok [Var.Union alias (Var.Listing [] False)]

  else

      manyNotFound region [alias] (allAliases ++ adtTypes)


getAdtExport
    :: [(String, Var.Listing String)]
    -> [String]
    -> A.Located (String, Var.Listing String)
    -> Result.ResultErr Var.Value
getAdtExport allAdts adtTypes (A.A region (name, Var.Listing ctors open)) =
  case List.lookup name allAdts of
    Nothing ->
        manyNotFound region [name] adtTypes

    Just (Var.Listing allCtors _) ->
        if open then
            Result.ok (Var.Union name (Var.Listing allCtors False))
        else
          case filter (`notElem` allCtors) ctors of
            [] ->
                Result.ok (Var.Union name (Var.Listing ctors False))
            unfoundCtors ->
                manyNotFound region unfoundCtors allCtors


manyNotFound :: Region.Region -> [String] -> [String] -> Result.ResultErr a
manyNotFound region nameList possibilities =
    Result.errors (map (notFound region possibilities) nameList)


notFound :: Region.Region -> [String] -> String -> A.Located CError.Error
notFound region possibilities name =
    A.A region $ CError.Export name $
        ErrorHelp.nearbyNames id name possibilities


allUnique :: [A.Located Var.Value] -> Result.ResultErr ()
allUnique statedExports =
  let
    valueToString value =
        case value of
          Var.Value name -> name
          Var.Alias name -> name
          Var.Union name _ -> name

    locations =
        Map.fromListWith (++) (map (\(A.A region value) -> (value, [region])) statedExports)

    isUnique value allRegions =
        case allRegions of
          region : _ : _ ->
              Result.err (A.A region (CError.DuplicateExport (valueToString value)))

          _ ->
              Result.ok ()
  in
    T.traverse_ id (Map.mapWithKey isUnique locations)


-- GROUPING VALUES

maybeUnzip3 :: [(Maybe a, Maybe b, Maybe c)] -> ([a],[b],[c])
maybeUnzip3 tuples =
  let (as, bs, cs) = unzip3 tuples
  in
    (Maybe.catMaybes as, Maybe.catMaybes bs, Maybe.catMaybes cs)


splitValue
    :: Var.Value
    -> ( Maybe String, Maybe String, Maybe (String, Var.Listing String) )
splitValue value =
  case value of
    Var.Value name ->
        (Just name, Nothing, Nothing)

    Var.Alias name ->
        (Nothing, Just name, Nothing)

    Var.Union name listing ->
        (Nothing, Nothing, Just (name, listing))


splitLocatedValue
    :: A.Located Var.Value
    ->
      ( Maybe (A.Located String)
      , Maybe (A.Located String)
      , Maybe (A.Located (String, Var.Listing String))
      )
splitLocatedValue (A.A region value) =
  case value of
    Var.Value name ->
        (Just (A.A region name), Nothing, Nothing)

    Var.Alias name ->
        (Nothing, Just (A.A region name), Nothing)

    Var.Union name listing ->
        (Nothing, Nothing, Just (A.A region (name, listing)))


-- DECLARATIONS

declToValue :: D.ValidDecl -> [Var.Value]
declToValue (A.A _ decl) =
    case decl of
      D.Definition (Valid.Definition pattern _ _ _) ->
          map Var.Value (P.boundVarList pattern)

      D.Datatype name _tvs ctors ->
          [ Var.Union name (Var.Listing (map fst ctors) False) ]

      D.TypeAlias name _ tipe ->
          case tipe of
            A.A _ (Type.RRecord _ Nothing) ->
                [ Var.Alias name, Var.Value name ]

            _ ->
                [ Var.Alias name ]

      _ -> []

-- | Checks whether the type variables in the right hand sides
-- of type rules are correct
checkTyperuletype'
    :: Env.Environment
    -> Region.Region
    -> Type.Canonical
    -> Type.Canonical
    -> Result.ResultErr Type.Canonical
checkTyperuletype' env rg typ annotation =
  let
    vars :: [String]
    vars = Type.collectVars typ

    varSet :: Set.Set String
    varSet = Set.fromList (Type.collectVars annotation)

    exists :: String -> a -> Result.ResultErr a
    exists s rs =
        if s `Set.member` varSet then
          Result.errors [A.A rg $ CError.TypeRuleVarInTypeAnnotation s]
        else if not ('_' `elem` s) then
          Result.ok rs -- Fresh type variable
        else
          case Map.lookup s (Env._values env) of
              Nothing -> Result.errors [A.A rg $ CError.variable "parameter" s CError.ExposedUnknown (ErrorHelp.nearbyNames id s $ Map.keys $ Env._values env)]
              Just _ -> Result.ok rs
  in
      Result.foldl exists typ vars

-- | mapping between the variables in rules and the parameters they reason about
varArgMappingFromRules
  :: [Rule.CanonicalRule]
  -> Map.Map String Int
  -> Map.Map String Int
varArgMappingFromRules [] mp = mp
varArgMappingFromRules ((A.A _ (Rule.Qualifier {})) : rs) mp = varArgMappingFromRules rs mp
varArgMappingFromRules ((A.A _ (Rule.SubRule {})) : rs) mp = varArgMappingFromRules rs mp
varArgMappingFromRules (r@(A.A _ rule) : rs) mp =
  let
    vars :: [String]
    vars = Type.collectVars $ Rule.rhs rule

    insertIgnore :: Ord k => a -> Map.Map k a -> k -> Map.Map k a
    insertIgnore a mp' k =
      case Map.lookup k mp' of
        Just _ -> mp'
        Nothing -> Map.insert k a mp'
  in
    case Map.lookup (Var.toString (Rule.lhs rule)) mp of
      Just argNr -> varArgMappingFromRules rs (foldl (insertIgnore argNr) mp vars)
      Nothing -> varArgMappingFromRules (rs ++ [r]) mp

-- | Defines a mapping between individual type rules and the parameters/return value they reason about
typeRuleVarArgMapping
    :: [P.CanonicalPattern]
    -> [Rule.CanonicalRule]
    -> Type.Canonical
    -> Map.Map String Int
typeRuleVarArgMapping pats rules tipe =
  let
    patToString :: P.CanonicalPattern -> String
    patToString (A.A _ (P.Var s)) = s

    addPatToMap :: (Int, Map.Map String Int) -> P.CanonicalPattern -> (Int, Map.Map String Int)
    addPatToMap (argNr, mp) pat = (argNr + 1, Map.insert (patToString pat) argNr mp)

    mapFromPats :: Map.Map String Int
    mapFromPats = snd $ foldl addPatToMap (0, Map.singleton "return" (length pats - 1)) (tail pats)

    initialMap :: Map.Map String Int
    initialMap = Map.union mapFromPats $ Env.numberedTypeVars tipe
  in
    varArgMappingFromRules rules initialMap

typeRuleConstraint :: Type.Canonical -> Rule.ValidRule  -> (Env.Environment, [Rule.CanonicalRule])-> Result.Result (A.Located CError.Error) (Env.Environment, [Rule.CanonicalRule])
typeRuleConstraint _ (A.A rg (Rule.SubRule (Var.Raw var))) (env, rs) =
  do
    v <- Canonicalize.variable rg env var
    Result.ok (env, A.A rg (Rule.SubRule v) : rs )
typeRuleConstraint tp (A.A rg (Rule.Constraint (Var.Raw lhs) rhs expl)) (env, rs) =
  do
    lhs' <- Canonicalize.variable rg env lhs
    rhs' <- Canonicalize.tipe env rhs
    rhs'' <- checkTyperuletype' env rg rhs' tp
    Result.ok (Env.addTypeVars rhs'' env, A.A rg (Rule.Constraint lhs' rhs'' expl) : rs)
typeRuleConstraint _ (A.A rg (Rule.Qualifier qual expl)) (env, rs) =
  do
    qual' <- Canonicalize.qualifier env qual

    Result.ok $ (env, A.A rg (Rule.Qualifier qual' expl) : rs)

typerule :: Env.Environment -> Maybe (A.Located Type.Canonical) -> Valid.TypeRule -> Result.Result (A.Located CError.Error) Canonical.TypeRule
typerule _ Nothing _ = error "Type annotation should exist when there are type rules"
typerule env (Just (A.A _ tp)) (A.A rg (Valid.TypeRule pats rules)) =
  do
    pats' <- mapM (pattern env) pats
    let env' = foldr Env.addPattern env (tail pats ++ [A.A undefined $ P.Var "return"]) -- Don't include the function names
    let env'' = Env.addTypeRuleType tp env'
    (_, constrs) <- Result.foldl (typeRuleConstraint tp) (env'', []) rules
    let constrs' = reverse constrs

    -- Check whether type variables in the signature appear in the rhs of the unify rules
    let tpVars = Set.fromList $ Type.collectNumberedVars tp
    let ruleVars = Set.fromList $ concat [ Type.collectVars rhs | A.A _ (Rule.Constraint _ rhs _) <- constrs' ]
    let missingTpVars = Set.difference tpVars ruleVars

    when (not $ Set.null missingTpVars) $
      Result.err $ A.A rg $ CError.TypeRuleMissingVars $ Set.toList $ missingTpVars

    -- let toCheckRule :: Type.Qualifier' Var.Canonical Type.Canonical' -> Rule.CanonicalRule
    --     toCheckRule (Type.Qualifier classNm (Type.Var name)) =
    --       A.A (error "Rule should not have its region inspected") $
    --         Rule.Qualifier (Type.Qualifier classNm (Type.Var $ name ++ "_1")) Nothing


    -- Add "Check" rules for all qualifiers at the end
    -- Even if they're already there in the type rules.
    -- let qualChecks = map toCheckRule $ Type.qualifiers tp
    -- let constrs'' = constrs' -- ++ qualChecks

    Result.ok $ Canonical.TypeRule pats' constrs' (typeRuleVarArgMapping pats' constrs tp)

definition
    :: Env.Environment
    -> Valid.Def
    -> Result.ResultErr Canonical.Def
definition env (Valid.Definition pat expr typ rules) =
    T.traverse (regionType env) typ
      `Result.andThen` \tp ->

        Canonical.Definition Canonical.dummyFacts
          <$> pattern env pat
          <*> expression env expr
          <*> pure tp
          <*> pure Nothing
          <*> Result.map (typerule env tp) rules

declaration
    :: ModuleName.Canonical
    -> Env.Environment
    -> D.ValidDecl
    -> Result.ResultErr D.CanonicalDecl
declaration modulname env (A.A ann@(region,_) decl) =
    A.A ann <$>
    case decl of
      D.Definition def ->
          D.Definition <$> definition env def

      D.Datatype name tvars ctors ->
          D.Datatype name tvars <$> T.traverse canonicalize' ctors
        where
          canonicalize' (ctor,args) =
              (,) ctor <$> T.traverse (Canonicalize.tipe' env) args

      D.TypeAlias name tvars expanded ->
          D.TypeAlias name tvars
            <$> Canonicalize.tipe' env expanded

      D.Port validPort ->
          Result.addModule ["Native","Port"] $
          Result.addModule ["Native","Json"] $
              case validPort of
                D.In name tipe ->
                    Canonicalize.tipe' env tipe
                      `Result.andThen` \canonicalType ->
                          D.Port <$> Port.check region name Nothing canonicalType

                D.Out name expr tipe ->
                    let exprTypeResult =
                          (,)
                            <$> expression env expr
                            <*> Canonicalize.tipe' env tipe
                    in
                        exprTypeResult
                          `Result.andThen` \(expr', tipe') ->
                              D.Port <$> Port.check region name (Just expr') tipe'


      D.IFace ifc@(Interface.Interface quals (A.A rg (Var.Raw classref)) (Var.Raw var) decls) ->
          let
            exists = Map.member classref (Env._interfaces env)
            Just (classnm, _) = Map.lookup classref (Env._interfaces env)
          in
            Result.map (qualifier env) quals
              `Result.andThen` \newQuals ->

                if (not exists) then
                  Result.errors [notFound rg (Map.keys . Env._interfaces $ env) classref]
                else
                  Result.map (interfaceDeclaration classnm var modulname env) decls
                    `Result.andThen` \newDecls ->
                      Result.ok . D.IFace $ Interface.Interface newQuals classnm (Type.Var var) newDecls

      D.Impl (Interface.Implementation quals (A.A rg (Var.Raw classref)) tipe defs) ->
          let
            exists = Map.member classref (Env._interfaces env)
            Just (classnm, _) = Map.lookup classref (Env._interfaces env)
          in
            if not exists then
              Result.errors [notFound rg (Map.keys . Env._interfaces $ env) classref]
            else

            Result.map (qualifier env) quals
              `Result.andThen` \newQuals ->
                Result.map (definition env) defs
                  `Result.andThen` \newDefs ->
                    Canonicalize.tipe' env tipe
                      `Result.andThen` \newtipe ->
                        Result.map (insertInterfaceType env classref newQuals newtipe) newDefs
                          `Result.andThen` \newnewDefs ->
                            Result.ok . D.Impl $ Interface.Implementation newQuals classnm newtipe newnewDefs

      D.Sibling from to ->
        do
          Canonicalize.variable region env from
            `Result.andThen` \fromVar ->
              Canonicalize.variable region env to
              `Result.andThen` \toVar ->
                Result.ok (D.Sibling fromVar toVar)

      D.Fixity assoc prec op ->
          Result.ok (D.Fixity assoc prec op)


insertInterfaceType
    :: Env.Environment
    -> String
    -> [Type.Qualifier' Var.Canonical Type.Canonical']
    -> Type.Canonical' -- implementation type
    -> Canonical.Def
    -> Result.ResultErr Canonical.Def
insertInterfaceType env classref quals impltype (Canonical.Definition facts pat@(A.A drg (P.Var name)) expr typ _ rules) =
  let
    (ifvar, interface) = Map.findWithDefault (error "Interface doesn't exist, this check was already made somewhere") classref (Env._interfaces env)
    typeAnns = [A.A rg tpe | A.A rg (Interface.IFType nm tpe _) <- Interface.decls interface, nm == name]
    (A.A tprg typeAnn) = if null typeAnns then error "No fitting definition in type class!" else head typeAnns -- TODO: throw proper error message
    Var.Raw interfaceVar = Interface.interfacevar interface
  in
    Canonicalize.tipe env typeAnn
      `Result.andThen`
        \newtipe -> Result.ok $ Canonical.Definition facts pat expr typ (Just (A.A tprg (Type.addQualifiers (Type.substitute (Type.Var interfaceVar) impltype newtipe) quals))) rules


interfaceDeclaration
    :: Var.Canonical
    -> String
    -> ModuleName.Canonical
    -> Env.Environment
    -> Interface.ValidInterfaceDecl
    -> Result.ResultErr Interface.CanonicalInterfaceDecl
interfaceDeclaration ifcName var modul env (A.A rg (Interface.IFType nm tipe rules)) =
  do
    newtipe <- Canonicalize.tipe env tipe
    let classNm = (Var.topLevel modul nm)
    let newtipe' = Type.addQualifiers newtipe [Type.Qualifier ifcName (Type.Var var)]
    newrules <- Result.map (typerule env (Just $ A.A rg $ newtipe')) rules

    Result.ok . A.A rg $ Interface.IFType classNm (A.A rg newtipe) newrules


qualifier
    :: Env.Environment
    -> Type.Qualifier' (A.Located Var.Raw) Var.Raw
    -> Result.ResultErr (Type.Qualifier' Var.Canonical Type.Canonical')
qualifier env (Type.Qualifier (A.A rg (Var.Raw classref)) (Var.Raw var)) =
    let
        exists = Map.member classref (Env._interfaces env)

        Just (classnm, _) = Map.lookup classref (Env._interfaces env)
    in
        if not exists then
          Result.errors [notFound rg (Map.keys . Env._interfaces $ env) classref]
        else
          Result.ok $ Type.Qualifier classnm (Type.Var var)

regionType
    :: Env.Environment
    -> Type.Raw
    -> Result.ResultErr (A.Located Type.Canonical)
regionType env typ@(Type.QT _ (A.A region _)) =
  A.A region <$> Canonicalize.tipe env typ


expression
    :: Env.Environment
    -> Valid.Expr
    -> Result.ResultErr Canonical.Expr
expression env (A.A region validExpr) =
    let go = expression env
    in
    A.A region <$>
    case validExpr of
      Literal lit ->
          Result.ok (Literal lit)

      Range lowExpr highExpr ->
          Range <$> go lowExpr <*> go highExpr

      Access record field ->
          Access <$> go record <*> Result.ok field

      Update record fields ->
          Update
            <$> go record
            <*> T.traverse (\(field,expr) -> (,) field <$> go expr) fields

      Record fields ->
          Record
            <$> T.traverse (\(field,expr) -> (,) field <$> go expr) fields

      Binop (Var.Raw op) leftExpr rightExpr ->
          Binop
            <$> Canonicalize.variable region env op
            <*> go leftExpr
            <*> go rightExpr

      Lambda arg body ->
          let env' = Env.addPattern arg env
          in
              Lambda <$> pattern env' arg <*> expression env' body

      App func arg ->
          App <$> go func <*> go arg

      If branches finally ->
          If
            <$> T.traverse go' branches
            <*> go finally
        where
          go' (condition, branch) =
              (,) <$> go condition <*> go branch

      Let defs body ->
          Let <$> T.traverse rename' defs <*> expression env' body
        where
          env' =
              foldr Env.addPattern env $ map (\(Valid.Definition p _ _ _) -> p) defs

          rename' (Valid.Definition p body mtipe _) =
              Canonical.Definition Canonical.dummyFacts
                  <$> pattern env' p
                  <*> expression env' body
                  <*> T.traverse (regionType env') mtipe
                  <*> pure Nothing
                  <*> pure []

      Var (Var.Raw x) ->
          Var <$> Canonicalize.variable region env x

      Data name exprs ->
          Data name <$> T.traverse go exprs

      ExplicitList exprs ->
          ExplicitList <$> T.traverse go exprs

      Case expr cases ->
          Case <$> go expr <*> T.traverse branch cases
        where
          branch (ptrn, brnch) =
              (,) <$> pattern env ptrn
                  <*> expression (Env.addPattern ptrn env) brnch

      Port impl ->
          let portType pt =
                case pt of
                  Type.Normal t ->
                      Type.Normal
                          <$> Canonicalize.tipe' env t

                  Type.Signal root arg ->
                      Type.Signal
                          <$> Canonicalize.tipe' env root
                          <*> Canonicalize.tipe' env arg
          in
              Port <$>
                  case impl of
                    E.In name tipe ->
                        E.In name <$> portType tipe

                    E.Out name expr tipe ->
                        E.Out name <$> go expr <*> portType tipe

                    E.Task name expr tipe ->
                        E.Task name <$> go expr <*> portType tipe

      GLShader uid src tipe ->
          Result.ok (GLShader uid src tipe)


pattern
    :: Env.Environment
    -> P.RawPattern
    -> Result.ResultErr P.CanonicalPattern
pattern env (A.A region ptrn) =
  A.A region <$>
    case ptrn of
      P.Var x ->
          Result.ok (P.Var x)

      P.Literal lit ->
          Result.ok (P.Literal lit)

      P.Record fields ->
          Result.ok (P.Record fields)

      P.Anything ->
          Result.ok P.Anything

      P.Alias x p ->
          P.Alias x <$> pattern env p

      P.Data (Var.Raw name) patterns ->
          P.Data
            <$> Canonicalize.pvar region env name (length patterns)
            <*> T.traverse (pattern env) patterns
