{-# OPTIONS_GHC -Wall #-}
module Type.Constrain.Expression where

import Control.Arrow (second)
import Control.Monad (foldM)
import Data.List (nub, sort)
import Data.Maybe (catMaybes)
import qualified Control.Monad as Monad
import qualified Data.Map as Map
import qualified Data.UnionFind.IO as UF

import qualified AST.Expression.General as E
import qualified AST.Expression.Canonical as Canonical
import qualified AST.Literal as Lit
import qualified AST.Pattern as P
import qualified AST.Rule as Rule
import qualified AST.Type as ST
import qualified AST.Variable as V
import qualified Reporting.Annotation as A
import qualified Reporting.Error.Type as Error
import qualified Reporting.Region as R
import qualified Type.Constrain.Literal as Literal
import qualified Type.Constrain.Pattern as Pattern
import qualified Type.Environment as Env
import qualified Type.Fragment as Fragment
import Type.Type


constrain
    :: Env.Environment
    -> Canonical.Expr
    -> Type
    -> IO TypeConstraint
constrain env annotatedExpr@(A.A region expression) tipe =
    let list t = Env.getType env "List" <| t
        (<?) = CInstance region
    in
    case expression of
      E.Literal lit ->
          Literal.constrain env region lit tipe

      E.GLShader _uid _src gltipe ->
          exists $ \attr ->
          exists $ \unif ->
            let
                shaderTipe a u v =
                    Env.getType env "WebGL.Shader" <| a <| u <| v

                glToType glTipe =
                    Env.getType env (Lit.glTipeName glTipe)

                makeRec accessor baseRec =
                    let decls = accessor gltipe
                    in
                      if Map.size decls == 0 then
                          baseRec
                      else
                          record (Map.map (glToType) decls) baseRec

                attribute = makeRec Lit.attribute attr
                uniform = makeRec Lit.uniform unif
                varying = makeRec Lit.varying (TermN EmptyRecord1)
            in
                return (CEqual Error.Shader region (shaderTipe attribute uniform varying) tipe ShaderType)

      E.Var var ->
          let name = V.toString var
          in
              return (if name == E.saveEnvName then CSaveEnv else (name <? tipe) (varTrustFactor var))

      E.Range lowExpr highExpr ->
          existsNumber $ \n ->
              do  lowCon <- constrain env lowExpr n
                  highCon <- constrain env highExpr n
                  return $ CAnd
                    [ lowCon
                    , highCon
                    , CEqual Error.Range region (list n) tipe ListRange
                    ]

      E.ExplicitList exprs ->
          constrainList env region exprs tipe

      E.Binop op leftExpr rightExpr ->
          constrainBinop' env region op leftExpr rightExpr tipe

      E.Lambda pattern body ->
          exists $ \argType ->
          exists $ \resType ->
              do  fragment <- Pattern.constrain env pattern argType
                  bodyCon <- constrain env body resType
                  let con =
                        ex (Fragment.vars fragment)
                            (CLet [monoscheme (Fragment.typeEnv fragment)]
                                  (Fragment.typeConstraint fragment /\ bodyCon)
                            )
                  return $ con /\ CEqual Error.Lambda region (argType ==> resType) tipe LambdaType

      E.App _ _ ->
          let
            (f:args) = E.collectApps annotatedExpr
          in
            constrainApp' env region f args tipe

      E.If branches finally ->
          constrainIf env region branches finally tipe

      E.Case expr branches ->
          constrainCase env region expr branches tipe

      E.Data name exprs ->
          do  vars <- Monad.forM exprs $ \_ -> mkVar Nothing
              let pairs = zip exprs (map VarN vars)
              (ctipe, cs) <- Monad.foldM step (tipe, CTrue) (reverse pairs)
              return $ ex vars (cs /\ (name <? ctipe) DataInstance)
          where
            step (t,c) (e,x) =
                do  c' <- constrain env e x
                    return (x ==> t, c /\ c')

      E.Access expr label ->
          exists $ \t ->
              constrain env expr (record (Map.singleton label tipe) t)

      E.Update expr fields ->
          exists $ \t ->
              do  oldVars <- mapM (\_ -> mkVar Nothing) fields
                  let oldFields = Map.fromList (zip (map fst fields) (map VarN oldVars))
                  cOld <- ex oldVars <$> constrain env expr (record oldFields t)

                  newVars <- mapM (\_ -> mkVar Nothing) fields
                  let newFields = Map.fromList (zip (map fst fields) (map VarN newVars))
                  let cNew = CEqual Error.Record region (record newFields t) tipe RecordType

                  cs <- Monad.zipWithM (constrain env) (map snd fields) (map VarN newVars)

                  return $ cOld /\ ex newVars (CAnd (cNew : cs))

      E.Record fields ->
          do  vars <- Monad.forM fields (\_ -> mkVar Nothing)
              fieldCons <-
                  Monad.zipWithM
                      (constrain env)
                      (map snd fields)
                      (map VarN vars)
              let fields' = Map.fromList (zip (map fst fields) (map VarN vars))
              let recordType = record fields' (TermN EmptyRecord1)
              return (ex vars (CAnd (fieldCons ++ [CEqual Error.Record region recordType tipe RecordType])))

      E.Let defs body ->
          do  bodyCon <- constrain env body tipe

              (Info schemes rqs fqs headers c2 c1) <-
                  Monad.foldM
                      (constrainDef env)
                      (Info [] [] [] Map.empty CTrue CTrue)
                      (concatMap expandPattern defs)

              let letScheme =
                    [ Scheme rqs fqs (CLet [monoscheme headers] c2) headers ]

              return $ CLet schemes (CLet letScheme (c1 /\ bodyCon))

      E.Port impl ->
          case impl of
            E.In _ _ ->
                return CTrue

            E.Out _ expr _ ->
                constrain env expr tipe

            E.Task _ expr _ ->
                constrain env expr tipe


-- CONSTRAIN APP

constrainApp
    :: Env.Environment
    -> R.Region
    -> Canonical.Expr
    -> [Canonical.Expr]
    -> Type
    -> IO TypeConstraint
constrainApp env region f args tipe =
  do  funcVar <- mkVar Nothing
      funcCon <- constrain env f (VarN funcVar)

      (vars, argCons, numberOfArgsCons, argMatchCons, _, returnVar) <-
          argConstraints env (maybeName f) region (length args) funcVar 1 args

      let returnCon =
            CEqual (Error.Function (maybeName f) Nothing) region (VarN returnVar) tipe FuncReturnType

      return $ ex (funcVar : vars) $
        CAnd (funcCon : argCons ++ numberOfArgsCons ++ argMatchCons ++ [returnCon])


maybeName :: Canonical.Expr -> Maybe V.Canonical
maybeName f =
  case f of
    A.A _ (E.Var canonicalName) ->
        Just canonicalName

    _ ->
      Nothing

-- | Figures out which type error to throw when a type rule constraint is broken
typeRuleError
    :: R.Region
    -> Maybe V.Canonical
    -> Rule.CanonicalRule'
    -> Map.Map String Int
    -> Error.Hint
typeRuleError rg mName (Rule.Qualifier (ST.Qualifier _ (ST.Var var)) explanation) varMap =
  let
    Just var' = Map.lookup var varMap

    returnNr :: Int
    (Just returnNr') = Map.lookup "return" varMap
    returnNr = returnNr' + 1
  in
    Error.UnexpectedArg mName (var' + 1) returnNr rg explanation

typeRuleError rg mName (Rule.Constraint lhs rhs explanation) varMap =
  let
    Just lhsVar' = Map.lookup (V.toString lhs) varMap
    lhsVar = lhsVar' + 1
    rhsVars = [ argNr + 1 | var <- ST.collectVars rhs, let Just argNr = Map.lookup var varMap ]

    returnNr :: Int
    (Just returnNr') = Map.lookup "return" varMap
    returnNr = returnNr' + 1

    vars :: [Int]
    vars = sort . nub $ (lhsVar : rhsVars)

  in
    case (returnNr `elem` vars, length vars) of
      (True, 1) -> Error.Function mName explanation
      (True, _) -> Error.ArgumentsReturn mName (init vars) lhsVar returnNr rg explanation
      (False, 1) -> Error.UnexpectedArg mName (head vars) returnNr rg explanation
      (False, _) -> Error.ArgumentsMisMatch mName vars lhsVar rg explanation

applyCustomTypeRule
    :: Env.Environment
    -> R.Region
    -> Canonical.Expr
    -> [Canonical.Expr]
    -> Type
    -> [P.CanonicalPattern]
    -> Map.Map String Int -- Type variable to related argument/return value
    -> (Int, Map.Map String Variable, TypeConstraint) -- the int being the counter of the rules
    -> Rule.CanonicalRule
    -> IO (Int, Map.Map String Variable, TypeConstraint)
applyCustomTypeRule env region f args tipe pats varNumbers (ruleNumber, varmap, constr) (A.A _ rule) =
    case rule of
      Rule.SubRule var ->
        case V.toString var of
          "return" ->
            do
              let (Just returnVar) = Map.lookup "return" varmap
              return (ruleNumber + 1, varmap, constr /\ CEqual (Error.Function (maybeName f) Nothing) region (VarN returnVar) tipe FuncReturnType)
          name ->
            do
              let (Just argVar) = Map.lookup name varmap

              let exprIx = findArgIndex var (tail pats) 0
              let expr = args !! exprIx

              varConstr <- constrain env expr (VarN argVar)

              return (ruleNumber + 1, varmap, constr /\ varConstr)
      Rule.Qualifier (ST.Qualifier classNm vartp) expl ->
        do
          (varmap', vartp') <- Env.instantiateExplainedType env (ST.unqualified vartp) varmap expl
          var <- mkQualifiedVar [classNm]

          case expl of
            Nothing -> return ()
            Just e ->
                UF.modifyDescriptor var (\d -> d { _qualifierExplanations = Map.singleton classNm e })

          return (ruleNumber + 1, varmap', constr /\ CEqual (typeRuleError region (maybeName f) rule varNumbers) region vartp' (VarN var) (CustomError ruleNumber))
      Rule.Constraint lhs rhs expl ->
        do
          (varmap', rhsT) <- Env.instantiateExplainedType env rhs varmap expl

          -- let varmap' = Map.union varmap vars

          (lhsT, varmap'') <-
                case Map.lookup (V.toString lhs) varmap' of
                    Just var -> return (var, varmap')
                    Nothing ->
                      do
                        var <- mkVar Nothing
                        return (var, Map.insert (V.toString lhs) var varmap')

          return (ruleNumber + 1, varmap'', constr /\ CEqual (typeRuleError region (maybeName f) rule varNumbers) region rhsT (VarN lhsT) (CustomError ruleNumber))
  where
    findArgIndex :: V.Canonical -> [P.CanonicalPattern] -> Int -> Int
    findArgIndex var [] _ = error $ "Parameter " ++ V.toString var ++ " does not occur in parameter list!"
    findArgIndex var ((A.A _ (P.Var s)) : ps) i
        | V.toString var == s = i
        | otherwise = findArgIndex var ps (i + 1)

constrainOverriddenApp
    :: Env.Environment
    -> R.Region
    -> Canonical.Expr
    -> [Canonical.Expr]
    -> Type
    -> Canonical.TypeRule
    -> IO TypeConstraint
constrainOverriddenApp env region f args tipe (Canonical.TypeRule pats rules argMap) =
    do
      funcVar <- mkVar Nothing

      argVars <- mapM (\_ -> mkVar Nothing) (tail pats ++ [A.A undefined $ P.Var "return"])
      varmap <- foldM mkVarFromString Map.empty (zip argVars $ tail pats ++ [A.A undefined $ P.Var "return"])

      (_, vars, rconstraints) <- foldM (applyCustomTypeRule env region f args tipe pats argMap) (0, varmap, CTrue) rules

      (returnVars, returnConstrs) <- mkReturnTypeConstrs 1 (length args) (init argVars) funcVar rconstraints

      return returnConstrs
  where
      mkVarFromString :: Map.Map String Variable -> (Variable, P.CanonicalPattern) -> IO (Map.Map String Variable)
      mkVarFromString varmap (var, A.A _ (P.Var name)) =
        return $ Map.insert name var varmap

      mkReturnTypeConstrs :: Int -> Int -> [Variable] -> Variable -> TypeConstraint -> IO ([Variable], TypeConstraint)
      mkReturnTypeConstrs _ _ [] _ constr = return ([], constr)
      mkReturnTypeConstrs index totalArgs (t : ts) funcVar constr =
        do
          localReturnVar <- mkVar Nothing
          (rets, constr') <- mkReturnTypeConstrs (index + 1) totalArgs ts localReturnVar constr
          return (localReturnVar : rets, constr' /\ CEqual
            (Error.FunctionArity (maybeName f) index totalArgs region)
            region
            ((VarN t) ==> (VarN localReturnVar))
            ((VarN funcVar))
            (FunctionArity index))


constrainApp'
    :: Env.Environment
    -> R.Region
    -> Canonical.Expr
    -> [Canonical.Expr]
    -> Type
    -> IO TypeConstraint
constrainApp' env region f@(A.A _ expr) args tipe =
  case expr of
    -- The thing applied is a variable that might have type rules
    E.Var name ->
      case Map.lookup (V.toString name) (Env._rules env) of
          Nothing -> constrainApp env region f args tipe
          Just rules ->
            -- The amount of arguments given in the type application must match
            -- the amount of arguments in the type rule
            case [ rule | rule@(Canonical.TypeRule pats _ _) <- rules, length args == (length pats - 1) ] of
              -- No fitting rules
              [] -> constrainApp env region f args tipe
              [rule] -> constrainOverriddenApp env region f args tipe rule
              _ -> error "Multiple rules fit this thing. That shouldn't happen!"
    _ -> constrainApp env region f args tipe

argConstraints
    :: Env.Environment
    -> Maybe V.Canonical
    -> R.Region
    -> Int
    -> Variable
    -> Int
    -> [Canonical.Expr]
    -> IO ([Variable], [TypeConstraint], [TypeConstraint], [TypeConstraint], Maybe R.Region, Variable)
argConstraints env name region totalArgs overallVar index args =
  case args of
    [] ->
      return ([], [], [], [], Nothing, overallVar)

    expr@(A.A subregion _) : rest ->
      do  argVar <- mkVar Nothing
          argCon <- constrain env expr (VarN argVar)
          argIndexVar <- mkVar Nothing
          localReturnVar <- mkVar Nothing

          (vars, argConRest, numberOfArgsRest, argMatchRest, restRegion, returnVar) <-
              argConstraints env name region totalArgs localReturnVar (index + 1) rest

          let arityRegion =
                maybe subregion (R.merge subregion) restRegion

          let numberOfArgsCon =
                CEqual
                  (Error.FunctionArity name (index - 1) totalArgs arityRegion)
                  region
                  ((VarN argIndexVar) ==> (VarN localReturnVar))
                  ((VarN overallVar))
                  (FunctionArity (index - 1))

          let argMatchCon =
                CEqual
                  (Error.UnexpectedArg name index totalArgs subregion Nothing)
                  region
                  (VarN argIndexVar)
                  (VarN argVar)
                  BadParameter

          return
            ( argVar : argIndexVar : localReturnVar : vars
            , argCon : argConRest
            , numberOfArgsCon : numberOfArgsRest
            , argMatchCon : argMatchRest
            , Just arityRegion
            , returnVar
            )


constrainBinop'
    :: Env.Environment
    -> R.Region
    -> V.Canonical
    -> Canonical.Expr
    -> Canonical.Expr
    -> Type
    -> IO TypeConstraint
constrainBinop' env region op leftExpr rightExpr tipe =
    -- The thing applied is a variable that might have type rules
    case Map.lookup (V.toString op) (Env._rules env) of
        Nothing -> constrainBinop env region op leftExpr rightExpr tipe
        Just rules ->
          -- The amount of arguments given in the type application must match
          -- the amount of arguments in the type rule
          case [ rule | rule@(Canonical.TypeRule pats _ _) <- rules, (length pats - 1) == 2 ] of
            -- No fitting rules
            [] -> constrainBinop env region op leftExpr rightExpr tipe
            [rule] -> constrainOverriddenApp env region (A.A region (E.Var op)) [leftExpr, rightExpr] tipe rule
            _ -> error "Multiple rules fit this thing. That shouldn't happen!"

-- CONSTRAIN BINOP

constrainBinop
    :: Env.Environment
    -> R.Region
    -> V.Canonical
    -> Canonical.Expr
    -> Canonical.Expr
    -> Type
    -> IO TypeConstraint
constrainBinop env region op leftExpr@(A.A leftRegion _) rightExpr@(A.A rightRegion _) tipe =
  do  leftVar <- mkVar Nothing
      rightVar <- mkVar Nothing

      leftCon <- constrain env leftExpr (VarN leftVar)
      rightCon <- constrain env rightExpr (VarN rightVar)

      leftVar' <- mkVar Nothing
      rightVar' <- mkVar Nothing
      answerVar <- mkVar Nothing

      let opType = (VarN leftVar') ==> (VarN rightVar') ==> (VarN answerVar)

      return $
        ex [leftVar,rightVar,leftVar',rightVar',answerVar] $ CAnd $
          [ leftCon
          , rightCon
          , CInstance region (V.toString op) opType (varTrustFactor op)
          , CEqual (Error.BinopLeft op leftRegion) region (VarN leftVar') (VarN leftVar) BadParameter
          , CEqual (Error.BinopRight op rightRegion) region (VarN rightVar') (VarN rightVar) BadParameter
          , CEqual (Error.Binop op) region (VarN answerVar) tipe FuncReturnType
          ]


-- CONSTRAIN LISTS

constrainList
    :: Env.Environment
    -> R.Region
    -> [Canonical.Expr]
    -> Type
    -> IO TypeConstraint
constrainList env region exprs tipe =
  do  (exprInfo, exprCons) <-
          unzip <$> mapM elementConstraint exprs

      (vars, cons) <- pairCons region Error.ListElement varToCon ListValues exprInfo

      return $ ex vars (CAnd (exprCons ++ cons))
  where
    elementConstraint expr@(A.A region' _) =
      do  var <- mkVar Nothing
          con <- constrain env expr (VarN var)
          return ( (var, region'), con )

    varToCon var =
      CEqual Error.List region (Env.getType env "List" <| VarN var) tipe ListType


-- CONSTRAIN IF EXPRESSIONS

constrainIf
    :: Env.Environment
    -> R.Region
    -> [(Canonical.Expr, Canonical.Expr)]
    -> Canonical.Expr
    -> Type
    -> IO TypeConstraint
constrainIf env region branches finally tipe =
  do  let (conditions, branchExprs) =
            second (++ [finally]) (unzip branches)

      (condVars, condCons) <-
          unzip <$> mapM constrainCondition conditions

      (branchInfo, branchExprCons) <-
          unzip <$> mapM constrainBranch branchExprs

      (vars,cons) <- branchCons branchInfo

      return $ ex (condVars ++ vars) (CAnd (condCons ++ branchExprCons ++ cons))
  where
    bool =
      Env.getType env "Bool"

    constrainCondition condition@(A.A condRegion _) =
      do  condVar <- mkVar Nothing
          condCon <- constrain env condition (VarN condVar)
          let boolCon = CEqual Error.IfCondition condRegion (VarN condVar) bool IfCondition
          return (condVar, CAnd [ condCon, boolCon ])

    constrainBranch expr@(A.A branchRegion _) =
      do  branchVar <- mkVar Nothing
          exprCon <- constrain env expr (VarN branchVar)
          return
            ( (branchVar, branchRegion)
            , exprCon
            )

    branchCons branchInfo =
      case branchInfo of
        [(thenVar, _), (elseVar, _)] ->
            return
              ( [thenVar,elseVar]
              , [ CEqual Error.IfBranches region (VarN thenVar) (VarN elseVar) IfBranches
                , varToCon thenVar
                ]
              )

        _ ->
            pairCons region Error.MultiIfBranch varToCon IfBranches branchInfo

    varToCon var =
      CEqual Error.If region (VarN var) tipe IfType



-- CONSTRAIN CASE EXPRESSIONS

constrainCase
    :: Env.Environment
    -> R.Region
    -> Canonical.Expr
    -> [(P.CanonicalPattern, Canonical.Expr)]
    -> Type
    -> IO TypeConstraint
constrainCase env region expr branches tipe =
  do  exprVar <- mkVar Nothing
      exprCon <- constrain env expr (VarN exprVar)

      (branchInfo, branchExprCons) <-
          unzip <$> mapM (branch (VarN exprVar)) branches

      (vars, cons) <- pairCons region Error.CaseBranch varToCon CaseBranches branchInfo

      return $ ex (exprVar : vars) (CAnd (exprCon : branchExprCons ++ cons))
  where
    branch patternType (pattern, branchExpr@(A.A branchRegion _)) =
        do  branchVar <- mkVar Nothing
            fragment <- Pattern.constrain env pattern patternType
            branchCon <- constrain env branchExpr (VarN branchVar)
            return
                ( (branchVar, branchRegion)
                , CLet [Fragment.toScheme fragment] branchCon
                )

    varToCon var =
      CEqual Error.Case region tipe (VarN var) CaseType

-- | Decide the trust factor for different kinds of variables
varTrustFactor :: V.Canonical -> TrustFactor
varTrustFactor var =
  case var of
    V.Canonical (V.BuiltIn) _ -> BuiltInVar
    V.Canonical (V.Module _) _ -> ModuleVar
    V.Canonical (V.TopLevel _) _ -> TopLevelVar
    V.Canonical (V.Local) _ -> LocalVar


-- COLLECT PAIRS

data Pair = Pair
    { _index :: Int
    , _var1 :: Variable
    , _var2 :: Variable
    , _region :: R.Region
    }


pairCons
    :: R.Region
    -> (Int -> R.Region -> Error.Hint)
    -> (Variable -> TypeConstraint)
    -> TrustFactor
    -> [(Variable, R.Region)]
    -> IO ([Variable], [TypeConstraint])
pairCons region pairHint varToCon trust items =
  let
    pairToCon (Pair index var1 var2 subregion) =
      CEqual (pairHint index subregion) region (VarN var1) (VarN var2) trust
  in
  case collectPairs 2 items of
    Nothing ->
        do  var <- mkVar Nothing
            return ([var], [varToCon var])

    Just (pairs, var) ->
        return (map fst items, map pairToCon pairs ++ [varToCon var])


collectPairs :: Int -> [(Variable, R.Region)] -> Maybe ([Pair], Variable)
collectPairs index items =
  case items of
    [] ->
        Nothing

    (var,_) : [] ->
        Just ([], var)

    (var,_) : rest@((var',region) : _) ->
        do  (pairs, summaryVar) <- collectPairs (index+1) rest
            return (Pair index var var' region : pairs, summaryVar)


-- EXPAND PATTERNS

expandPattern :: Canonical.Def -> [Canonical.Def]
expandPattern def@(Canonical.Definition facts lpattern expr maybeType interfaceType rules) =
  let (A.A patternRegion pattern) = lpattern
  in
  case pattern of
    P.Var _ ->
        [def]

    _ ->
        mainDef : map toDef vars
      where
        vars = P.boundVarList lpattern

        combinedName = "$" ++ concat vars

        pvar name =
            A.A patternRegion (P.Var name)

        localVar name =
            A.A patternRegion (E.localVar name)

        mainDef = Canonical.Definition facts (pvar combinedName) expr maybeType interfaceType rules

        toDef name =
            let extract =
                  E.Case (localVar combinedName) [(lpattern, localVar name)]
            in
                Canonical.Definition facts (pvar name) (A.A patternRegion extract) Nothing Nothing rules


-- CONSTRAIN DEFINITIONS

data Info = Info
    { iSchemes :: [TypeScheme]
    , iRigid :: [Variable]
    , iFlex :: [Variable]
    , iHeaders :: Map.Map String (A.Located Type)
    , iC2 :: TypeConstraint
    , iC1 :: TypeConstraint
    }


constrainDef :: Env.Environment -> Info -> Canonical.Def -> IO Info
constrainDef env info (Canonical.Definition _ (A.A patternRegion pattern) expr maybeTipe interfaceType rules) =
  let qs = [] -- should come from the def, but I'm not sure what would live there...
  in
  case (pattern, maybeTipe) of
    (P.Var name, Just (A.A typeRegion tipe)) ->
        constrainAnnotatedDef env info qs patternRegion typeRegion name expr tipe interfaceType >>=
        constrainRules env tipe typeRegion rules

    (P.Var name, Nothing) ->
        constrainUnannotatedDef env info qs patternRegion name expr interfaceType

    _ ->
        error "canonical definitions must not have complex patterns as names in the contstraint generation phase"

constrainRule
    :: Env.Environment
    -> ST.Canonical
    -> R.Region
    -> TypeConstraint
    -> Canonical.TypeRule
    -> IO TypeConstraint
constrainRule env tipeAnn tipeAnnRg constr (Canonical.TypeRule pats constrs _) =
  let
    lambdas :: [ST.Canonical']
    lambdas = ST.collectLambdas tipeAnn

    -- Qualify a type with the qualifiers from the type annotation
    qlf :: ST.Canonical' -> ST.Canonical
    qlf tp = ST.QT (ST.qualifiers tipeAnn) tp

    mkVarFromString :: Map.Map String Variable -> (Variable, P.CanonicalPattern) -> IO (Map.Map String Variable)
    mkVarFromString varmap (var, A.A _ (P.Var name')) =
      return $ Map.insert name' var varmap

    -- In partial functions, the "return" refers to the rest of the type annotation
    -- This builds that last bit of the type annotation
    instantiateRestFunc :: [ST.Canonical'] -> Map.Map String Variable -> IO (Map.Map String Variable, Type)
    instantiateRestFunc [t] varmap = Env.instantiateType env (qlf t) varmap
    instantiateRestFunc (t : ts) varmap =
      do
        (varmap', t') <- Env.instantiateType env (qlf t) varmap
        (varmap'', recTp) <- instantiateRestFunc ts varmap'

        return (varmap'', t' ==> recTp)

    -- Create constraints between the variables of the arguments and the type annotation
    matchVarsTypeAnn
      :: [P.CanonicalPattern]
      -> [Variable]
      -> [ST.Canonical']
      -> Map.Map String Variable
      -> IO (Map.Map String Variable, TypeConstraint)
    matchVarsTypeAnn _ [returnVar] tipes varmap =
      do
        (varmap', restFunc) <- instantiateRestFunc tipes varmap
        let constr' = CEqual Error.TypeRuleReturn tipeAnnRg restFunc (VarN returnVar) (CustomError (-1000))

        return (varmap', constr')
    matchVarsTypeAnn (A.A _ (P.Var argName) : ps) (v : vs) (t : ts) varmap =
      do
        (varmap', tp) <- Env.instantiateType env (qlf t) varmap

        (recVarmap, recConstr) <- matchVarsTypeAnn ps vs ts varmap'

        return (recVarmap, CEqual (Error.TypeRuleArgument argName) tipeAnnRg tp (VarN v) (CustomError (-1000)) /\ recConstr)

    -- Constrain one custom constraint
    constrainSubrule
      :: (Int, Map.Map String Variable, TypeConstraint)
      -> Rule.CanonicalRule
      -> IO (Int, Map.Map String Variable, TypeConstraint)
    constrainSubrule x (A.A _ (Rule.SubRule _)) = return x
    constrainSubrule (ruleNr, varmap, constr') (A.A rg (Rule.Qualifier (ST.Qualifier classNm vartp) _)) =
      do
        (varmap', vartp') <- Env.instantiateType env (ST.unqualified vartp) varmap
        var <- mkQualifiedVar [classNm]


        return (ruleNr + 1, varmap', constr' /\ CEqual Error.TypeRuleQualifierMismatch rg vartp' (VarN var) (CustomError ruleNr))
    constrainSubrule (ruleNr, varmap, constr') (A.A rg (Rule.Constraint lhs rhs _)) =
      do
        (varmap', rhsT) <- Env.instantiateType env rhs varmap
        (lhsT, varmap'') <-
          case Map.lookup (V.toString lhs) varmap' of
              Just var -> return (var, varmap')
              Nothing ->
                do
                  var <- mkVar Nothing
                  return (var, Map.insert (V.toString lhs) var varmap')

        return (ruleNr + 1, varmap'', constr' /\ CEqual Error.TypeRuleMismatch rg (VarN lhsT) rhsT (CustomError ruleNr))
  in
    do
      argVars <- mapM (\_ -> mkVar Nothing) (tail pats ++ [A.A undefined $ P.Var "return"])
      varmap <- foldM mkVarFromString Map.empty (zip argVars $ tail pats ++ [A.A undefined $ P.Var "return"])

      (varmap', typeAnnConstr) <- matchVarsTypeAnn (tail pats) argVars lambdas varmap

      -- type annotation vars must be rigid
      let typeAnnVars = Map.elems $ Map.difference varmap' varmap
      mapM_ mkVarRigid typeAnnVars

      -- Constrain the subrules
      (_, _, trConstrs) <- foldM constrainSubrule (0, varmap', CTrue) constrs

      let scheme =
            Scheme
              { _rigidQuantifiers = typeAnnVars
              , _flexibleQuantifiers = []
              , _constraint = CTrue
              , _header = Map.empty
              }

      -- Second round of constraints
      -- Used to check for missing qualifiers in type rules
      argVars2 <- mapM (\_ -> mkVar Nothing) (tail pats ++ [A.A undefined $ P.Var "return"])
      varmap2 <- foldM mkVarFromString Map.empty (zip argVars2 $ tail pats ++ [A.A undefined $ P.Var "return"])


      (_, varmap2', trConstrs2) <- foldM constrainSubrule (0, varmap2, CTrue) constrs

      let nrVars = [ v ++ "_1" | v <- nub $ ST.collectVars tipeAnn ]
      let nrVariables = catMaybes $ map (flip Map.lookup varmap2') nrVars

      let ruleRepresentedFunc = foldr1 (==>) $ map VarN argVars2
      (_, tipeAnnType) <- Env.instantiateType env tipeAnn Map.empty
      let typeAnnConstr2 = CEqual Error.TypeRuleAnnotation tipeAnnRg ruleRepresentedFunc tipeAnnType (CustomError (-1000))

      let scheme2 =
            Scheme
              { _rigidQuantifiers = nrVariables
              , _flexibleQuantifiers = Map.elems varmap2'
              , _constraint = trConstrs2
              , _header = Map.empty
              }


      return $ CLet [scheme] (typeAnnConstr /\ trConstrs) /\ CLet [scheme2] (typeAnnConstr2 /\ constr)

constrainRules
    :: Env.Environment
    -> ST.Canonical
    -> R.Region
    -> [Canonical.TypeRule]
    -> Info
    -> IO Info
constrainRules env tipeAnn tipeAnnRg rules info =
  do
    lets <- foldM (constrainRule env tipeAnn tipeAnnRg) CTrue rules
    return info { iC1 = lets /\ iC1 info }

constrainAnnotatedDef
    :: Env.Environment
    -> Info
    -> [String]
    -> R.Region
    -> R.Region
    -> String
    -> Canonical.Expr
    -> ST.Canonical
    -> Maybe (A.Located ST.Canonical)
    -> IO Info
constrainAnnotatedDef env info qs patternRegion typeRegion name expr tipe interfaceType =
  do  -- Some mistake may be happening here. Currently, qs is always [].
      rigidVars <- mapM mkRigid qs


      flexiVars <- mapM mkNamedVar qs

      let env' = Env.addValues env (zip qs flexiVars)

      (vars', typ) <- Env.instantiateType env tipe Map.empty
      (ifvars', iftyp) <- case interfaceType of
            Nothing -> return (Map.empty, undefined)
            Just (A.A _ tp) -> Env.instantiateType env tp Map.empty

      let ifvars = Map.elems ifvars'
      let vars = Map.elems vars'

      mapM mkVarRigid ifvars

      let scheme =
            Scheme
              { _rigidQuantifiers = [] ++ ifvars
              , _flexibleQuantifiers = flexiVars ++ vars ++ ifvars
              , _constraint = CTrue
              , _header = Map.singleton name (A.A patternRegion typ)
              }


      var <- mkVar Nothing
      defCon <- constrain env' expr (VarN var)
      let annCon =
            CEqual (Error.BadTypeAnnotation name) typeRegion typ (VarN var) Annotation

      case interfaceType of
            Nothing ->
                return $ info
                    { iSchemes = scheme : iSchemes info
                    , iC1 = iC1 info /\ ex [var] (defCon /\ fl rigidVars annCon)
                    }
            Just (A.A ifrg _) -> --CEqual (Error.BadMatchWithInterface name) ifrg iftyp (VarN var) Annotation -- TODO: different descriptor than Annotation
                  return $ info
                    { iSchemes = scheme : iSchemes info
                    , iC1 = iC1 info /\ ex [var] (defCon /\ (fl rigidVars (annCon /\ (CEqual (Error.BadMatchWithInterface name) ifrg iftyp (VarN var) Annotation))))
                    }




constrainUnannotatedDef
    :: Env.Environment
    -> Info
    -> [String]
    -> R.Region
    -> String
    -> Canonical.Expr
    -> Maybe (A.Located ST.Canonical)
    -> IO Info
constrainUnannotatedDef env info qs patternRegion name expr interfaceType =
  do  -- Some mistake may be happening here. Currently, qs is always [].
      rigidVars <- mapM mkRigid qs

      v <- mkVar Nothing

      let tipe = VarN v

      let env' = Env.addValues env (zip qs rigidVars)

      (ifvars', iftyp) <- case interfaceType of
            Nothing -> return (Map.empty, undefined)
            Just (A.A _ tp) -> Env.instantiateType env tp Map.empty

      let ifvars = Map.elems ifvars'

      mapM mkVarRigid ifvars
      con <- constrain env' expr tipe

      case interfaceType of
            Nothing ->
                return $ info
                    { iRigid = rigidVars ++ ifvars ++ iRigid info
                    , iFlex = v : iFlex info ++ ifvars
                    , iHeaders = Map.insert name (A.A patternRegion tipe) (iHeaders info)
                    , iC2 = con /\ iC2 info
                    }
            Just (A.A ifrg _) -> --CEqual (Error.BadMatchWithInterface name) ifrg iftyp tipe Annotation -- TODO: different descriptor than Annotation
                return $ info
                    { iRigid = rigidVars ++ ifvars ++ iRigid info
                    , iFlex = v : iFlex info ++ ifvars
                    , iC2 = con /\ iC2 info /\ fl rigidVars (CEqual (Error.BadMatchWithInterface name) ifrg iftyp tipe Annotation)
                    }



