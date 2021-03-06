{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wall #-}
module Type.Type where

import Control.Monad.State (StateT, liftIO)
import qualified Control.Monad.State as State
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as Traverse (traverse)
import qualified Data.UnionFind.IO as UF

import qualified AST.Type as T
import qualified AST.Variable as Var
import qualified Reporting.Annotation as A
import qualified Reporting.Error.Type as Error
import qualified Reporting.Region as R

import Data.Maybe (fromJust)

import System.IO.Unsafe

-- CONCRETE TYPES


type Type =
    TermN Variable


type Variable =
    UF.Point Descriptor


instance (Eq a, Show a) => Show (UF.Point a) where
  show x = unsafePerformIO $ do
            desc <- UF.descriptor x

            return $ "UnionFindThing " ++ show desc

type TypeConstraint =
    Constraint Type Variable


type TypeScheme =
    Scheme Type Variable



-- TYPE PRIMITIVES


data Term1 a
    = App1 a a
    | Fun1 a a
    | EmptyRecord1
    | Record1 (Map.Map String a) a
    deriving (Show, Eq)



data TermN a
    = PlaceHolder String
    | AliasN Var.Canonical [(String, TermN a)] (TermN a)
    | VarN a
    | TermN (Term1 (TermN a))
    deriving (Eq)

instance Show a => Show (TermN a) where
    show _ = "TermN"
    -- Don't show infinite types with this code:
    -- show (PlaceHolder s) = "PlaceHolder " ++ s
    -- show (AliasN v _ t) = "AliasN " ++ show v ++ " term: " ++ show t
    -- show (VarN a) = "VarN " ++ show a
    -- show (TermN t1) = "TermN " ++ show t1


record :: Map.Map String (TermN a) -> TermN a -> TermN a
record fs rec =
  TermN (Record1 fs rec)



-- DESCRIPTORS


data Descriptor = Descriptor
    { _content :: Content
    , _rank :: Int
    , _mark :: Int
    , _copy :: Maybe Variable
    , _qualifiers :: Set.Set Var.Canonical
    , _qualifierExplanations :: Map.Map Var.Canonical String
    , _typegraphid :: Maybe Int
    , _typegraphCopyId :: Maybe Int
    }
    deriving (Show, Eq)


data Content
    = Structure (Term1 Variable)
    | Atom Var.Canonical
    | Var Flex (Maybe Super) (Maybe String)
    | Alias Var.Canonical [(String,Variable)] Variable
    | Error Content
    deriving(Show, Eq)


data Flex
    = Rigid
    | Flex
    deriving (Show, Eq, Ord)


data Super
    = Number
    | Comparable
    | Appendable
    | CompAppend
    deriving (Eq, Ord, Show)


noRank :: Int
noRank = -1


outermostRank :: Int
outermostRank = 0


noMark :: Int
noMark = 0


initialMark :: Int
initialMark = 1


occursMark :: Int
occursMark =
  -1


getVarNamesMark :: Int
getVarNamesMark =
  -2



-- CONSTRAINTS

data TrustFactor
    = Pattern
    | Literal
    | Annotation
    | BuiltInVar
    | CustomError Int
    | ModuleVar
    | TopLevelVar
    | LocalVar
    | DataInstance
    | BadParameter
    | FuncReturnType
    | ListType
    | ShaderType
    | IfType
    | CaseType
    | LambdaType
    | RecordType
    | IfBranches
    | IfCondition
    | CaseBranches
    | ListValues
    | ListRange
    | FunctionArity Int
    deriving (Eq, Ord, Show)

data Constraint a b
    = CTrue
    | CSaveEnv
    | CEqual Error.Hint R.Region a a TrustFactor
    | CAnd [Constraint a b]
    | CLet [Scheme a b] (Constraint a b)
    | CInstance R.Region SchemeName a TrustFactor
    deriving (Eq)

instance (Show a, Show b) => Show (Constraint a b) where
  show CTrue = "CTrue"
  show CSaveEnv = "CSaveEnv"
  show (CEqual h _ l r trust) = "CEqual " ++ (show h) ++ {-" {ltype: " ++ show l ++ ", rtype: " ++ show r ++ "}" ++-}  show trust
  show (CAnd cs) = "CAnd {" ++ (concat . List.intersperse ", " . map show $ cs) ++ "}"
  show (CLet schs constr) = "CLet (" ++ show schs ++ ". CLetConstr: (" ++ show constr ++ "))"
  show (CInstance _ name val trust) = "CInstance " ++ name ++ " val: " ++ show val ++ show trust


type SchemeName = String


data Scheme a b = Scheme
    { _rigidQuantifiers :: [b]
    , _flexibleQuantifiers :: [b]
    , _constraint :: Constraint a b
    , _header :: Map.Map String (A.Located a)
    }
    deriving (Eq)

instance (Show a, Show b) => Show (Scheme a b) where
  show schm = "SCHEME { header = " ++ show (_header schm) ++ ", constraint: {" ++ show (_constraint schm) ++ "}}"


-- TYPE HELPERS


infixr 9 ==>
infixr 9 ==>|


(==>) :: Type -> Type -> Type
(==>) a b =
  TermN (Fun1 a b)

(==>|) :: TermN a -> TermN a -> TermN a
(==>|) a b =
  TermN (Fun1 a b)


{-(<||) :: Type -> Type -> Type
(<||) (T.QT fq f) (T.QT aq a) =
  T.QT (fq ++ aq) (f <| a)-}

(<|) :: TermN a -> TermN a -> TermN a
(<|) f a =
  TermN (App1 f a)



copyTerm1 :: Map.Map Int Variable -> Term1 (TermN Variable) -> IO (Term1 (TermN Variable), Map.Map Int Variable)
copyTerm1 mp (App1 l r) =
  do
    (l', mp1) <- copyType' mp l
    (r', mp2) <- copyType' mp1 r
    return $ (App1 l' r', mp2)

copyTerm1 mp (Fun1 l r) =
  do
    (l', mp1) <- copyType' mp l
    (r', mp2) <- copyType' mp1 r
    return $ (Fun1 l' r', mp2)

copyTerm1 mp EmptyRecord1 = return (EmptyRecord1, mp)
copyTerm1 vmp (Record1 mp var) =
  do
    (var', vmp1) <- copyType' vmp var
    (smp', vmp4) <- Map.foldlWithKey (\iom key val -> do
      (smp, vmp2) <- iom
      (val', vmp3) <- copyType' vmp2 val
      return $ (Map.insert key val' smp, vmp3)) (return (Map.empty, vmp1)) mp
    return $ (Record1 smp' var', vmp4)


copyVariable :: Map.Map Int Variable -> Variable -> IO (Variable, Map.Map Int Variable)
copyVariable mp var =
  do
    desc <- UF.descriptor var

    case _typegraphCopyId desc of
      Nothing ->
        do
          let newId = if Map.null mp then 0 else (+ 1) . fst . Map.findMax $ mp

          var' <- UF.fresh desc
          UF.modifyDescriptor var (\d -> d { _typegraphCopyId = Just newId })
          UF.modifyDescriptor var' (\d -> d { _copy = Just var })

          let mp' = Map.insert newId var' mp
          return (var', mp')

      Just i -> return $ (Map.findWithDefault (error (show mp)) i mp, mp)

copyScheme :: Map.Map Int Variable -> Scheme Type Variable -> IO (Scheme Type Variable, Map.Map Int Variable)
copyScheme mp scheme =
  do
    let fold = foldr (\quant acc -> do
        (lst, mp') <- acc
        (val', mp1) <- copyVariable mp' quant
        return (val' : lst, mp1)
        )

    (rquants, mp1) <- fold (return ([], mp)) (_rigidQuantifiers scheme)
    (fquants, mp2) <- fold (return ([], mp1)) (_flexibleQuantifiers scheme)
    (constr, mp3) <- copyConstraintHelp mp2 (_constraint scheme)

    return (Scheme rquants fquants constr (_header scheme), mp3)


copyType :: Map.Map Int Variable -> Type -> IO (Type, Map.Map Int Variable)
copyType mp tp=
  do
    (newtp, newmp) <- copyType' mp tp
    return (newtp, newmp)

copyType' :: Map.Map Int Variable -> TermN Variable -> IO (TermN Variable, Map.Map Int Variable)
copyType' mp (PlaceHolder s) = return (PlaceHolder s, mp)
copyType' mp (AliasN vc aliases term) =
  do
    (aliases', mp1) <- foldr (\(s, var) acc -> do
      (lst, mp') <- acc
      (var', mp'') <- copyType' mp' var
      return ((s, var') : lst, mp'')) (return ([], mp)) aliases
    (term', mp2) <- copyType' mp1 term

    return (AliasN vc aliases' term', mp2)

copyType' mp (VarN var) = -- TODO: copy qualifiers from copied variable?
  do
    (var', mp1) <- copyVariable mp var

    return $ (VarN var', mp1)

copyType' mp (TermN term1) =
  do
    (t1', mp1) <- copyTerm1 mp term1
    return (TermN t1', mp1)

copyConstraint :: TypeConstraint -> IO TypeConstraint
copyConstraint cnstr =
  do
    (cnstr', mp') <- copyConstraintHelp Map.empty cnstr

    -- Unregister all vars for reuse
    let vars = map snd . Map.toList $ mp'
    let unregister var = do
        desc <- UF.descriptor var
        let old = fromJust (_copy desc)
        UF.modifyDescriptor old (\d -> d { _typegraphCopyId = Nothing })

    mapM_ unregister vars

    return cnstr'

copyConstraintHelp :: Map.Map Int Variable -> TypeConstraint -> IO (TypeConstraint, Map.Map Int Variable)
copyConstraintHelp mp (CEqual h rg l r trust) =
  do
    (l', mp1) <- copyType mp l
    (r', mp2) <- copyType mp1 r

    return $ (CEqual h rg l' r' trust, mp2)

copyConstraintHelp mp (CAnd cs) = do
  (cnstrs, mp') <- foldr (\cnstr acc -> do
    (lst, mp1) <- acc
    (cnstr', mp2) <- copyConstraintHelp mp1 cnstr
    return (cnstr' : lst, mp2)) (return ([], mp)) cs

  return (CAnd cnstrs, mp')

copyConstraintHelp mp (CLet schemes cnstr) =
  do
    (schemes', mp1) <- foldr (\scheme acc -> do
      (lst, mp') <- acc
      (scheme', mp'') <- copyScheme mp' scheme
      return (scheme' : lst, mp'')) (return ([], mp)) schemes

    (cnstr', mp2) <- copyConstraintHelp mp1 cnstr

    return $ (CLet schemes' cnstr', mp2)

copyConstraintHelp mp (CInstance rg nm tp trust) =
  do
    (tp', mp') <- copyType mp tp
    return (CInstance rg nm tp' trust, mp')

copyConstraintHelp mp x = return (x, mp)


trustFactor :: Constraint a b -> Maybe TrustFactor
trustFactor (CEqual _ _ _ _ t) = Just t
trustFactor (CInstance _ _ _ t) = Just t
trustFactor _ = Nothing

-- Valuation of trust
-- Decides how much trust is assigned to each kind of constraint
trustValuation :: TrustFactor -> Int
trustValuation Pattern          = 200
trustValuation Literal          = 800
trustValuation Annotation       = 500
trustValuation BuiltInVar       = 1000
trustValuation (CustomError i)  = 10 - i -- Lowest trust factor
trustValuation ModuleVar        = 700
trustValuation TopLevelVar      = 400
trustValuation LocalVar         = 300
trustValuation DataInstance     = 400
trustValuation BadParameter     = 100
trustValuation FuncReturnType   = 150
trustValuation ListType         = 100
trustValuation ShaderType       = 100
trustValuation IfType           = 100
trustValuation CaseType         = 100
trustValuation LambdaType       = 100
trustValuation RecordType       = 100
trustValuation IfBranches       = 100
trustValuation IfCondition      = 50
trustValuation CaseBranches     = 100
trustValuation ListValues       = 100
trustValuation ListRange        = 50
trustValuation (FunctionArity i)    = 800 - i

-- VARIABLE CREATION


mkDescriptor :: Content -> Descriptor
mkDescriptor content =
  Descriptor
    { _content = content
    , _rank = noRank
    , _mark = noMark
    , _copy = Nothing
    , _qualifiers = Set.empty
    , _qualifierExplanations = Map.empty
    , _typegraphid = Nothing
    , _typegraphCopyId = Nothing
    }


mkAtom :: Var.Canonical -> IO Variable
mkAtom name =
  UF.fresh $ mkDescriptor (Atom name)


mkVar :: Maybe Super -> IO Variable
mkVar maybeSuper =
  UF.fresh $ mkDescriptor (Var Flex maybeSuper Nothing)

mkQualifiedVar :: [Var.Canonical] -> IO Variable
mkQualifiedVar quals =
  do
    var <- mkVar Nothing
    UF.modifyDescriptor var (\d -> d { _qualifiers = Set.fromList quals })
    return var


mkNamedVar :: String -> IO Variable
mkNamedVar name =
    UF.fresh $ mkDescriptor (Var Flex (toSuper name) Nothing)


mkRigid :: String -> IO Variable
mkRigid name =
    UF.fresh $ mkDescriptor (Var Rigid (toSuper name) (Just name))


mkVarRigid :: Variable -> IO ()
mkVarRigid var =
    let updContent (Var _ sup nm) = Var Rigid sup nm
    in
      UF.modifyDescriptor var (\desc -> desc { _content = updContent (_content desc) })


toSuper :: String -> Maybe Super
toSuper name =
  if List.isPrefixOf "number" name then
      Just Number

  else if List.isPrefixOf "comparable" name then
      Just Comparable

  else if List.isPrefixOf "appendable" name then
      Just Appendable

  else
      Nothing



-- CONSTRAINT HELPERS


monoscheme :: Map.Map String (A.Located a) -> Scheme a b
monoscheme headers =
  Scheme [] [] CTrue headers


infixl 8 /\

(/\) :: Constraint a b -> Constraint a b -> Constraint a b
(/\) c1 c2 =
    case (c1, c2) of
      (CTrue, _) -> c2
      (_, CTrue) -> c1
      _ -> CAnd [c1,c2]


-- ex qs constraint == exists qs. constraint
ex :: [Variable] -> TypeConstraint -> TypeConstraint
ex fqs constraint =
    CLet [Scheme [] fqs constraint Map.empty] CTrue


-- fl qs constraint == forall qs. constraint
fl :: [Variable] -> TypeConstraint -> TypeConstraint
fl rqs constraint =
    CLet [Scheme rqs [] constraint Map.empty] CTrue


exists :: (Type -> IO TypeConstraint) -> IO TypeConstraint
exists f =
  do  v <- mkVar Nothing
      ex [v] <$> f (VarN v)


existsNumber :: (Type -> IO TypeConstraint) -> IO TypeConstraint
existsNumber f =
  do  v <- mkVar (Just Number)
      ex [v] <$> f (VarN v)



-- CONVERT TO SOURCE TYPES


-- TODO: Attach resulting type to the descriptor so that you
-- never have to do extra work, particularly nice for aliased types
toSrcType :: Variable -> IO T.Canonical
toSrcType variable =
  do  usedNames <- getVarNames variable
      State.evalStateT (variableToSrcType variable) (makeNameState usedNames)


variableToSrcType :: Variable -> StateT NameState IO T.Canonical
variableToSrcType variable =
  do  descriptor <- liftIO $ UF.descriptor variable
      let mark = _mark descriptor
      if mark == occursMark
        then
          return (T.QT [T.Qualifier classref (T.Var "∞") | classref <- Set.toList $ _qualifiers descriptor] $ T.Var "∞")

        else
          do  liftIO $ UF.modifyDescriptor variable (\desc -> desc { _mark = occursMark })
              srcType <- contentToSrcType variable descriptor
              liftIO $ UF.modifyDescriptor variable (\desc -> desc { _mark = mark })
              return srcType


contentToSrcType :: Variable -> Descriptor -> StateT NameState IO T.Canonical
contentToSrcType variable desc =
  let
      content = _content desc
      qualify t = T.QT [T.Qualifier q t | q <- Set.toList $ _qualifiers desc] t
  in
    case content of
      Structure term ->
          termToSrcType term (_qualifiers desc)

      Atom name ->
          return . qualify $ T.Type name

      Var _ _ (Just name) ->
          return . qualify $ (T.Var name)

      Var flex maybeSuper Nothing ->
          do  freshName <- getFreshName maybeSuper
              liftIO $ UF.modifyDescriptor variable $ \desc ->
                  desc { _content = Var flex maybeSuper (Just freshName) }
              return . qualify $ (T.Var freshName)

      Alias name args realVariable ->
          do  srcArgs <- mapM (\(arg,tvar) -> (,) arg . T.qtype <$> variableToSrcType tvar) args
              srcType <- variableToSrcType realVariable
              return . qualify $ T.Aliased name srcArgs (T.Filled (T.qtype srcType))

      Error  _->
          return . qualify $ T.Var "?"


termToSrcType :: Term1 Variable -> Set.Set Var.Canonical -> StateT NameState IO T.Canonical
termToSrcType term quals =
  case term of
    App1 func arg ->
        do  T.QT funcQuals srcFunc <- variableToSrcType func
            T.QT argQuals srcArg <- variableToSrcType arg
            case srcFunc of
              T.App f args ->
                  let
                    typ = T.App f (args ++ [srcArg])
                  in
                    return (T.QT ([T.Qualifier q typ | q <- Set.toList quals] ++ funcQuals ++ argQuals) typ)

              _ ->
                  let
                    typ = T.App srcFunc [srcArg]
                  in
                    return (T.QT ([T.Qualifier q typ | q <- Set.toList quals] ++ funcQuals ++ argQuals) typ)

    Fun1 a b ->
      do
        (T.QT fquals f) <- variableToSrcType a
        (T.QT argquals arg) <- variableToSrcType b

        return (T.QT (fquals ++ argquals) (T.Lambda f arg))
        {-T.Lambda
            <$> variableToSrcType a
            <*> variableToSrcType b-}

    EmptyRecord1 ->
        return . T.QT [] $ T.Record [] Nothing

    Record1 fields extension ->
      do  srcFields <- Map.toList <$> Traverse.traverse variableToSrcType fields
          let tfields = map (\(n, t) -> (n, T.qtype t)) srcFields
          T.QT extQuals srcExt <- T.iteratedDealias <$> variableToSrcType extension


          return $
              case srcExt of
                T.Record subFields subExt ->
                    let
                        typ = T.Record (subFields ++ tfields) subExt
                    in
                        T.QT ([T.Qualifier q typ | q <- Set.toList quals] ++ extQuals) typ

                T.Var _ ->
                    let
                      typ = T.Record tfields (Just srcExt)
                    in
                        T.QT ([T.Qualifier q typ | q <- Set.toList quals] ++ extQuals) typ

                _ ->
                    error "Used toSrcType on a type that is not well-formed"



-- MANAGE FRESH VARIABLE NAMES


data NameState = NameState
    { _freeNames :: [String]
    , _numberPrimes :: Int
    , _comparablePrimes :: Int
    , _appendablePrimes :: Int
    , _compAppendPrimes :: Int
    , _vertexNames :: Map.Map Int String
    }


makeNameState :: Set.Set String -> NameState
makeNameState usedNames =
  let
    makeName suffix =
      map (:suffix) ['a'..'z']

    allNames =
      concatMap makeName ("" : map show [ (1 :: Int) .. ])

    freeNames =
      filter (\name -> Set.notMember name usedNames) allNames
  in
    NameState freeNames 0 0 0 0 Map.empty


getFreshName :: (Monad m) => Maybe Super -> StateT NameState m String
getFreshName maybeSuper =
  case maybeSuper of
    Nothing ->
        do  names <- State.gets _freeNames
            State.modify (\state -> state { _freeNames = tail names })
            return (head names)

    Just Number ->
        do  primes <- State.gets _numberPrimes
            State.modify (\state -> state { _numberPrimes = primes + 1 })
            return ("number" ++ replicate primes '\'')

    Just Comparable ->
        do  primes <- State.gets _comparablePrimes
            State.modify (\state -> state { _comparablePrimes = primes + 1 })
            return ("comparable" ++ replicate primes '\'')

    Just Appendable ->
        do  primes <- State.gets _appendablePrimes
            State.modify (\state -> state { _appendablePrimes = primes + 1 })
            return ("appendable" ++ replicate primes '\'')

    Just CompAppend ->
        do  primes <- State.gets _compAppendPrimes
            State.modify (\state -> state { _compAppendPrimes = primes + 1 })
            return ("compappend" ++ replicate primes '\'')

addVertexName :: Monad m => Int -> String -> StateT NameState m ()
addVertexName i s = State.modify (\state -> state { _vertexNames = Map.insert i s (_vertexNames state) })

getVertexName :: Monad m => Int -> Maybe Super -> StateT NameState m String
getVertexName i msuper =
  do
    state <- State.gets _vertexNames

    case Map.lookup i state of
      Just x -> return x
      Nothing ->
        do
          name <- getFreshName msuper
          addVertexName i name
          return name

-- GET ALL VARIABLE NAMES


getVarNames :: Variable -> IO (Set.Set String)
getVarNames var =
  do  desc <- UF.descriptor var
      if _mark desc == getVarNamesMark
        then
          return Set.empty

        else
          do  UF.setDescriptor var (desc { _mark = getVarNamesMark })
              getVarNamesHelp (_content desc)


getVarNamesHelp :: Content -> IO (Set.Set String)
getVarNamesHelp content =
  case content of
    Var _ _ (Just name) ->
        return (Set.singleton name)

    Var _ _ Nothing ->
        return Set.empty

    Structure term ->
        getVarNamesTerm term

    Alias _name args realVar ->
        do  let argSet = Set.fromList (map fst args)
            realSet <- getVarNames realVar
            sets <- mapM (getVarNames . snd) args
            return (Set.unions (realSet : argSet : sets))

    Atom _ ->
        return Set.empty

    Error _ ->
        return Set.empty


getVarNamesTerm :: Term1 Variable -> IO (Set.Set String)
getVarNamesTerm term =
  let go = getVarNames in
  case term of
    App1 a b ->
        Set.union <$> go a <*> go b

    Fun1 a b ->
        Set.union <$> go a <*> go b

    EmptyRecord1 ->
        return Set.empty

    Record1 fields extension ->
        do  fieldVars <- Set.unions <$> mapM go (Map.elems fields)
            Set.union fieldVars <$> go extension

