{-# OPTIONS_GHC -Wall #-}
module Type.Unify (unify, atomMatchesSuper, ExtensionStructure (..), findImplementation) where

import Control.Monad (zipWithM_, when)
import Control.Monad.Except (ExceptT, lift, liftIO, throwError, runExceptT)
import qualified Data.Map as Map
import qualified Data.UnionFind.IO as UF
import qualified Data.Set as Set

import qualified AST.Variable as Var
import qualified AST.Type as T
import qualified Reporting.Region as R
import qualified Reporting.Error.Type as Error
import qualified Type.State as TS
import Type.Type as Type
import qualified AST.Interface as Interface

import Data.Maybe (listToMaybe)

-- KICK OFF UNIFICATION


unify :: Error.Hint -> R.Region -> Variable -> Variable -> TS.Solver ()
unify hint region expected actual =
  do
      result <- runExceptT (guardedUnify ExpectedActual expected actual)
      case result of
        Right state ->
            return state

        Left (Mismatch _subExpected _subActual maybeReason) ->
            let
              mkError =
                do  expectedSrcType <- Type.toSrcType expected
                    actualSrcType <- Type.toSrcType actual
                    descExp <- UF.descriptor expected
                    copyExp <- UF.fresh descExp

                    desc <- UF.descriptor actual
                    copyActual <- UF.fresh desc
                    -- mergeHelp expected expected (Error copyExp)
                    --mergeHelp actual actual (Error copyActual)
                    let info = Error.MismatchInfo hint expectedSrcType actualSrcType maybeReason []
                    return (Error.Mismatch info)
            in
              TS.addError region =<< liftIO mkError
        Left (NoImplementation classref tp var expl) ->
          do
            liftIO $ do
              desc <- UF.descriptor var
              UF.setDescriptor var desc { _qualifiers = Set.empty }
              mergeHelp var var (Error (_content desc))

            TS.addError region (Error.NoImplementation classref tp expl)



-- UNIFICATION HELPERS


type Unify =
  ExceptT Mismatch TS.Solver


data Context = Context
    { _orientation :: Orientation
    , _first :: Variable
    , _firstDesc :: Descriptor
    , _second :: Variable
    , _secondDesc :: Descriptor
    }


data Orientation = ExpectedActual | ActualExpected


reorient :: Context -> Context
reorient (Context orientation var1 desc1 var2 desc2) =
  let
    otherOrientation =
      case orientation of
        ExpectedActual -> ActualExpected
        ActualExpected -> ExpectedActual
  in
    Context otherOrientation var2 desc2 var1 desc1



-- ERROR MESSAGES


data Mismatch
    = Mismatch Variable Variable (Maybe Error.Reason)
    | NoImplementation Var.Canonical T.Canonical' Variable (Maybe String)

noimplementation :: Var.Canonical -> T.Canonical' -> Variable -> Maybe String -> Unify ()
noimplementation classref t var expl = throwError $ NoImplementation classref t var expl

mismatch :: Context -> Maybe Error.Reason -> Unify a
mismatch (Context orientation first _ second _) maybeReason =
  let
    (expected, actual, orientedReason) =
        case orientation of
          ExpectedActual ->
              (first, second, maybeReason)

          ActualExpected ->
              (second, first, Error.flipReason <$> maybeReason)
  in
    throwError (Mismatch expected actual orientedReason)


badRigid :: Maybe String -> Error.Reason
badRigid maybeName =
  Error.BadVar (Just (Error.Rigid maybeName)) Nothing

badRigidQualifier :: Set.Set Var.Canonical -> Error.Reason
badRigidQualifier quals =
  Error.BadVar (Just (Error.RigidQualifier $ map Var.toString $ Set.toList quals)) Nothing


badSuper :: Super -> Error.Reason
badSuper super =
  Error.BadVar (Just (errorSuper super)) Nothing


doubleBad :: Error.VarType -> Error.VarType -> Error.Reason
doubleBad vt1 vt2 =
  Error.BadVar (Just vt1) (Just vt2)


errorSuper :: Super -> Error.VarType
errorSuper super =
  case super of
    Number ->
        Error.Number

    Comparable ->
        Error.Comparable

    Appendable ->
        Error.Appendable

    CompAppend ->
        Error.CompAppend



-- MERGE


merge :: Context -> Content -> Unify ()
merge context@(Context _ first firstDesc second secondDesc) content =
  let
    check rigidQuals otherQuals =
      do
        let diff = Set.difference otherQuals rigidQuals

        when (not $ Set.null $ diff) $
          mismatch context (Just (badRigidQualifier diff))
  in
    do
      case (_content firstDesc, _content secondDesc) of
        (Var Rigid _ _, _) -> check (_qualifiers firstDesc) (_qualifiers secondDesc)
        (_, Var Rigid _ _) -> check (_qualifiers secondDesc) (_qualifiers firstDesc)
        _ -> return ()


      liftIO $ mergeHelp first second content


mergeHelp :: Variable -> Variable -> Content -> IO ()
mergeHelp first second content =
  do
    descL <- UF.descriptor first
    descR <- UF.descriptor second
    let quals = Set.union (_qualifiers descL) (_qualifiers descR)
    let qualExpls = Map.union (_qualifierExplanations descL) (_qualifierExplanations descR)
    UF.modifyDescriptor first (\desc -> desc { _qualifiers = quals, _qualifierExplanations = qualExpls })
    UF.modifyDescriptor second (\desc -> desc { _qualifiers = quals, _qualifierExplanations = qualExpls })
    UF.union' first second $ \desc1 desc2 ->
      return $
        Descriptor
          { _content = content
          , _rank = min (_rank desc1) (_rank desc2)
          , _mark = noMark
          , _copy = Nothing
          , _qualifiers = quals
          , _qualifierExplanations = qualExpls
          , _typegraphid = Nothing
          , _typegraphCopyId = Nothing
          }


fresh :: Context -> Content -> Unify Variable
fresh (Context _ _ desc1 _ desc2) content =
  do  freshVariable <-
          liftIO $ UF.fresh $
            Descriptor
              { _content = content
              , _rank = min (_rank desc1) (_rank desc2)
              , _mark = noMark
              , _copy = Nothing
              , _qualifiers = Set.union (_qualifiers desc1) (_qualifiers desc2)
              , _qualifierExplanations = Map.union (_qualifierExplanations desc1) (_qualifierExplanations desc2)
              , _typegraphid = Nothing
              , _typegraphCopyId = Nothing
              }
      lift (TS.register freshVariable)



-- ACTUALLY UNIFY THINGS


guardedUnify :: Orientation -> Variable -> Variable -> Unify ()
guardedUnify orientation left right =
  do
      equivalent <- liftIO $ UF.equivalent left right
      if equivalent
        then
              return ()
        else
          do  leftDesc <- liftIO $ UF.descriptor left
              rightDesc <- liftIO $ UF.descriptor right
              actuallyUnify (Context orientation left leftDesc right rightDesc)


subUnify :: Context -> Variable -> Variable -> Unify ()
subUnify context var1 var2 =
  guardedUnify (_orientation context) var1 var2


actuallyUnify :: Context -> Unify ()
actuallyUnify context@(Context _ fvar firstDesc _ secondDesc) =
  let
    secondContent = _content secondDesc
  in
  case _content firstDesc of
    Error _ ->
        -- If there was an error, just pretend it is okay. This lets us avoid
        -- "cascading" errors where one problem manifests as multiple messages.
        return ()

    Var Flex Nothing _ ->
        unifyFlex context secondContent

    Var Flex (Just super) _ ->
        unifySuper context super secondContent

    Var Rigid maybeSuper maybeName ->
        unifyRigid context maybeSuper maybeName secondContent

    Atom name ->
        do
          unifyAtom context name secondContent

    Alias name args realVar ->
        unifyAlias context name args realVar secondContent

    Structure term -> -- TODO: context reduction + propagate down.
        unifyStructure context term secondContent


matchesType :: T.Canonical' -> T.Canonical' -> Bool
matchesType t impltype =
  case (t, impltype) of
      (T.App l r, T.App l' r') -> matchesType l l' && and (zipWith matchesType r r')
      (T.Lambda l r, T.Lambda l' r') -> matchesType l l' && matchesType r r'
      (tp, T.Var s) -> True
      (x, y) -> x == y

findImplementation
    :: [(Interface.CanonicalInterface, Interface.CanonicalImplementation)] -- all implementations
    -> Var.Canonical -- The class of the qualifier
    -> T.Canonical' -- the type being qualified
    -> Maybe (Interface.CanonicalInterface, Interface.CanonicalImplementation) -- a matching implementation
findImplementation impls classref t =
    listToMaybe
    [ imp
    | imp@(_, impl) <- impls
    , Interface.classref impl == classref
    , matchesType t (Interface.impltype impl)
    ]

propagateQualifierAtom :: Map.Map Var.Canonical String -> Var.Canonical -> Variable -> Var.Canonical -> Unify ()
propagateQualifierAtom explMap atomName var classref =
  do
    impls <- lift TS.getImplementations
    let tipe = T.Type atomName

    case findImplementation impls classref tipe of
      Just _ -> liftIO $ UF.modifyDescriptor var (\desc -> desc { _qualifiers = Set.empty })
      Nothing -> noimplementation classref tipe var (Map.lookup classref explMap)

children :: Variable -> Unify [Variable]
children var =
  do
      term <- liftIO $ _content <$> UF.descriptor var

      case term of
        Structure (App1 l r) -> (++ [r]) <$> children l
        Structure (Fun1 l r) -> return [l, r]
        _ -> return []


propagateDown :: Map.Map Var.Canonical String -> Interface.CanonicalImplementation -> Term1 Variable -> Variable -> T.Qualifier' Var.Canonical T.Canonical' -> Unify ()
propagateDown expls impl term var (T.Qualifier classref classvar) =
  let
      rec :: [T.Canonical'] -> [Variable] -> Unify ()
      rec [] _ = error $ "Type qualifier variable " ++ show classvar ++ " Not found in implementation type. That shouldn't happen."
      rec _ [] = error $ "The data type doesn't have enough children!"
      rec (implvar : implvars) (t : terms)
        | implvar == classvar =
            do
              desc <- liftIO $ UF.descriptor t
              propagateQualifiersHelp (_content desc) t [classref] expls
        | otherwise =
            rec implvars terms
  in
    case (Interface.impltype impl, term) of
      (T.App _ rs, App1 _ _) -> children var >>= rec rs
      (T.Lambda l _, Fun1 l' r') ->
          if classvar == l then
            (liftIO $ _content <$> UF.descriptor l') >>= (\c -> propagateQualifiersHelp c l' [classref] expls)
          else
            (liftIO $ _content <$> UF.descriptor r') >>= (\c -> propagateQualifiersHelp c r' [classref] expls)

propagateQualifierStructure :: Map.Map Var.Canonical String -> Variable -> Term1 Variable -> Var.Canonical -> Unify ()
propagateQualifierStructure explMap var term classref =
  do
    srctp <- liftIO $ toSrcType var
    impls <- lift TS.getImplementations
    let tipe = T.qtype srctp
    case findImplementation impls classref tipe of
      Nothing -> noimplementation classref tipe var (Map.lookup classref explMap)
      Just (_, impl) -> mapM_ (propagateDown explMap impl term var ) (Interface.implquals impl)

propagateQualifiersHelp :: Content -> Variable -> [Var.Canonical] -> Map.Map Var.Canonical String -> Unify ()
propagateQualifiersHelp content var qualifiers expls =
    case content of
        Atom name -> mapM_ (propagateQualifierAtom expls name var) qualifiers
        Structure term -> mapM_ (propagateQualifierStructure expls var term) qualifiers


propagateQualifiers :: Content -> Variable -> Variable -> Unify ()
propagateQualifiers content var1 var2 =
  do
    desc1 <- liftIO $ UF.descriptor var1
    desc2 <- liftIO $ UF.descriptor var2

    let qualifiers = Set.toList (_qualifiers desc1 `Set.union` _qualifiers desc2)
    let expls = _qualifierExplanations desc1 `Map.union` _qualifierExplanations desc2
    propagateQualifiersHelp content var1 qualifiers expls

-- UNIFY FLEXIBLE VARIABLES


unifyFlex :: Context -> Content -> Unify ()
unifyFlex context@(Context _ fvar firstDesc svar secondDesc) otherContent =
  case otherContent of
    Error _ ->
        return ()

    Var Flex _ _ ->
        merge context otherContent

    Var Rigid _ _ ->
        merge context otherContent

    Atom name ->
        merge context otherContent >>
        propagateQualifiers otherContent svar fvar

    Alias _ _ _ ->
        merge context otherContent

    Structure _ ->
        merge context otherContent >>
        propagateQualifiers otherContent svar fvar



-- UNIFY RIGID VARIABLES


unifyRigid :: Context -> Maybe Super -> Maybe String -> Content -> Unify ()
unifyRigid context maybeSuper maybeName otherContent =
  case otherContent of
    Error _ ->
        return ()

    Var Flex otherMaybeSuper _ ->
        case (maybeSuper, otherMaybeSuper) of
          (_, Nothing) ->
              merge context (Var Rigid maybeSuper maybeName)

          (Nothing, Just _) ->
              mismatch context (Just (badRigid maybeName))

          (Just super, Just otherSuper) ->
              case combineSupers super otherSuper of
                Right newSuper | newSuper == otherSuper ->
                    merge context otherContent

                _ ->
                    mismatch context (Just (badRigid maybeName))

    Var Rigid _ otherMaybeName ->
        mismatch context $ Just $
          doubleBad (Error.Rigid maybeName) (Error.Rigid otherMaybeName)

    Atom _ ->
        mismatch context (Just (badRigid maybeName))

    Alias _ _ _ ->
        mismatch context (Just (badRigid maybeName))

    Structure _ ->
        mismatch context (Just (badRigid maybeName))


-- UNIFY SUPER VARIABLES


unifySuper :: Context -> Super -> Content -> Unify ()
unifySuper context@(Context _ fvar firstDesc svar secondDesc) super otherContent =
  case otherContent of
    Structure term ->
        unifySuperStructure context super term >>
        propagateQualifiers otherContent svar fvar

    Atom name ->
        if atomMatchesSuper super name then
            merge context otherContent >>
            propagateQualifiers otherContent svar fvar
        else
            mismatch context (Just (badSuper super))

    Var Rigid Nothing maybeName ->
        mismatch context (Just (doubleBad (errorSuper super) (Error.Rigid maybeName)))

    Var Rigid (Just otherSuper) maybeName ->
        case combineSupers super otherSuper of
          Right newSuper | newSuper == super ->
              merge context otherContent

          _ ->
              mismatch context $ Just $
                doubleBad (errorSuper super) (Error.Rigid maybeName)

    Var Flex Nothing _ ->
        merge context (Var Flex (Just super) Nothing)

    Var Flex (Just otherSuper) _ ->
        case combineSupers super otherSuper of
          Left reason ->
              mismatch context (Just reason)

          Right newSuper ->
              merge context (Var Flex (Just newSuper) Nothing)

    Alias _ _ realVar ->
        subUnify context (_first context) realVar

    Error _ ->
        return ()


combineSupers :: Super -> Super -> Either Error.Reason Super
combineSupers firstSuper secondSuper =
  case (firstSuper, secondSuper) of
    (Number    , Number    ) -> Right Number
    (Comparable, Number    ) -> Right Number
    (Number    , Comparable) -> Right Number

    (Comparable, Comparable) -> Right Comparable
    (Appendable, Appendable) -> Right Appendable

    (Appendable, Comparable) -> Right CompAppend
    (Comparable, Appendable) -> Right CompAppend

    (CompAppend, CompAppend) -> Right CompAppend
    (CompAppend, Comparable) -> Right CompAppend
    (Comparable, CompAppend) -> Right CompAppend
    (CompAppend, Appendable) -> Right CompAppend
    (Appendable, CompAppend) -> Right CompAppend

    (_         , _         ) ->
        Left $ doubleBad (errorSuper firstSuper) (errorSuper secondSuper)


isPrimitiveFrom :: [String] -> Var.Canonical -> Bool
isPrimitiveFrom prims var =
  any (\p -> Var.isPrim p var) prims


atomMatchesSuper :: Super -> Var.Canonical -> Bool
atomMatchesSuper super name =
  case super of
    Number ->
        isPrimitiveFrom ["Int", "Float"] name

    Comparable ->
        isPrimitiveFrom ["Int", "Float", "Char", "String"] name

    Appendable ->
        Var.isPrim "String" name || Var.isText name

    CompAppend ->
        Var.isPrim "String" name


unifySuperStructure :: Context -> Super -> Term1 Variable -> Unify ()
unifySuperStructure context super term =
  do  appStructure <- liftIO (collectApps (Structure term))
      case appStructure of
        Other ->
            mismatch context (Just (badSuper super))

        List variable ->
            case super of
              Number ->
                  mismatch context (Just (badSuper super))

              Appendable ->
                  merge context (Structure term)

              Comparable ->
                  do  merge context (Structure term)
                      unifyComparableRecursive (_orientation context) variable

              CompAppend ->
                  do  merge context (Structure term)
                      unifyComparableRecursive (_orientation context) variable

        Tuple entries ->
            case super of
              Number ->
                  mismatch context (Just (badSuper super))

              Appendable ->
                  mismatch context (Just (badSuper super))

              Comparable ->
                  if length entries > 6 then
                      mismatch context (Just (Error.TooLongComparableTuple (length entries)))

                  else
                      do  merge context (Structure term)
                          mapM_ (unifyComparableRecursive (_orientation context)) entries

              CompAppend ->
                  mismatch context (Just (badSuper super))


unifyComparableRecursive :: Orientation -> Variable -> Unify ()
unifyComparableRecursive orientation var =
  do  compVar <-
          liftIO $
            do  desc <- UF.descriptor var
                UF.fresh $
                  Descriptor
                    { _content = Var Flex (Just Comparable) Nothing
                    , _rank = _rank desc
                    , _mark = noMark
                    , _qualifiers = _qualifiers desc
                    , _qualifierExplanations = _qualifierExplanations desc
                    , _copy = Nothing
                    , _typegraphid = Nothing
                    , _typegraphCopyId = Nothing
                    }

      guardedUnify orientation compVar var


data AppStructure
    = List Variable
    | Tuple [Variable]
    | Other


collectApps :: Content -> IO AppStructure
collectApps content =
    collectAppsHelp [] content


collectAppsHelp :: [Variable] -> Content -> IO AppStructure
collectAppsHelp args content =
  case (content, args) of
    (Structure (App1 func arg), _) ->
        collectAppsHelp (args ++ [arg]) =<< getContent func

    (Atom name, [arg]) | Var.isList name ->
        return (List arg)

    (Atom name, _) | Var.isTuple name ->
        return (Tuple args)

    _ ->
        return Other


getContent :: Variable -> IO Content
getContent variable =
  _content <$> UF.descriptor variable



-- UNIFY ATOMS


unifyAtom :: Context -> Var.Canonical -> Content -> Unify ()
unifyAtom context@(Context _ fvar firstDesc svar secondDesc) name otherContent =
  propagateQualifiers (_content firstDesc) fvar svar >>
  case otherContent of
    Error _ ->
        return ()

    Var Flex Nothing _ ->
        merge context (Atom name)

    Var Flex (Just super) _ ->
        if atomMatchesSuper super name then
            merge context (Atom name)

        else
            mismatch context (Just ((Error.flipReason (badSuper super))))

    Var Rigid _ maybeName ->
        mismatch context (Just (Error.flipReason (badRigid maybeName)))

    Atom otherName ->
        if name == otherName then
            merge context otherContent

        else
            mismatch context $
              if isIntFloat name otherName || isIntFloat otherName name then
                  Just Error.IntFloat
              else
                  Nothing

    Alias _ _ realVar ->
        subUnify context (_first context) realVar

    Structure _ ->
        mismatch context Nothing


isIntFloat :: Var.Canonical -> Var.Canonical -> Bool
isIntFloat name otherName =
  Var.isPrim "Int" name && Var.isPrim "Float" otherName


-- UNIFY ALIASES


unifyAlias :: Context -> Var.Canonical -> [(String, Variable)] -> Variable -> Content -> Unify ()
unifyAlias context name args realVar otherContent =
  case otherContent of
    Error _ ->
        return ()

    Var Flex Nothing _ ->
        merge context (Alias name args realVar)

    Var _ _ _ ->
        subUnify context realVar (_second context)

    Atom _ ->
        subUnify context realVar (_second context)


    Alias otherName otherArgs otherRealVar ->
        if name == otherName then
            do  merge context otherContent
                zipWithM_ (subUnify context) (map snd args) (map snd otherArgs)

        else
            subUnify context realVar otherRealVar

    Structure _ ->
        subUnify context realVar (_second context)



-- UNIFY STRUCTURES


unifyStructure :: Context -> Term1 Variable -> Content -> Unify ()
unifyStructure context@(Context _ fvar firstDesc svar secondDesc) term otherContent =
  propagateQualifiers (_content firstDesc) fvar svar >>
  case otherContent of
    Error _ ->
        return ()

    Var Flex Nothing _ ->
        merge context (Structure term)

    Var Flex (Just super) _ ->
        unifySuper (reorient context) super (Structure term)

    Var Rigid _ maybeName ->
        mismatch context (Just (Error.flipReason (badRigid maybeName)))

    Atom _ ->
        mismatch context Nothing

    Alias _ _ realVar ->
        subUnify context (_first context) realVar

    Structure otherTerm ->
        case (term, otherTerm) of
          (App1 func arg, App1 otherFunc otherArg) ->
              do  subUnify context func otherFunc
                  subUnify context arg otherArg
                  merge context otherContent

          (Fun1 arg result, Fun1 otherArg otherResult) ->
              do  subUnify context arg otherArg
                  subUnify context result otherResult
                  merge context otherContent

          (EmptyRecord1, EmptyRecord1) ->
              merge context otherContent

          (Record1 fields ext, EmptyRecord1) | Map.null fields ->
              subUnify context ext (_second context)

          (EmptyRecord1, Record1 fields ext) | Map.null fields ->
              subUnify context (_first context) ext

          (Record1 fields extension, Record1 otherFields otherExtension) ->
              do  firstStructure <- gatherFields context fields extension
                  secondStructure <- gatherFields context otherFields otherExtension
                  unifyRecord context firstStructure secondStructure

          _ ->
              mismatch context Nothing



-- UNIFY RECORDS


unifyRecord :: Context -> RecordStructure -> RecordStructure -> Unify ()
unifyRecord context firstStructure secondStructure =
  do  let (RecordStructure expFields expVar expStruct) = firstStructure
      let (RecordStructure actFields actVar actStruct) = secondStructure

      -- call after unifying extension, make sure record shape matches before
      -- looking into whether the particular field types match.
      let unifySharedFields otherFields ext =
            do  let sharedFields = Map.intersectionWith (,) expFields actFields
                _ <- traverse (uncurry (subUnify context)) sharedFields
                let allFields = Map.union (Map.map fst sharedFields) otherFields
                merge context (Structure (Record1 allFields ext))

      let uniqueExpFields = Map.difference expFields actFields
      let uniqueActFields = Map.difference actFields expFields

      case (expStruct, Map.null uniqueExpFields, actStruct, Map.null uniqueActFields) of
        (_, True, _, True) ->
            do  subUnify context expVar actVar
                unifySharedFields Map.empty expVar

        (Empty, _, _, False) ->
            mismatch context (Just (Error.MessyFields (Map.keys uniqueExpFields) (Map.keys uniqueActFields)))

        (_, False, Empty, _) ->
            mismatch context (Just (Error.MessyFields (Map.keys uniqueExpFields) (Map.keys uniqueActFields)))

        (_, False, _, True) ->
            do  subRecord <- fresh context (Structure (Record1 uniqueExpFields expVar))
                subUnify context subRecord actVar
                unifySharedFields Map.empty subRecord

        (_, True, _, False) ->
            do  subRecord <- fresh context (Structure (Record1 uniqueActFields actVar))
                subUnify context expVar subRecord
                unifySharedFields Map.empty subRecord

        (Extension, False, Extension, False) ->
            do  let subFields = Map.union uniqueExpFields uniqueActFields
                subExt <- fresh context (Var Flex Nothing Nothing)
                expRecord <- fresh context (Structure (Record1 uniqueActFields subExt))
                actRecord <- fresh context (Structure (Record1 uniqueExpFields subExt))
                subUnify context expVar expRecord
                subUnify context actRecord actVar
                unifySharedFields subFields subExt



-- GATHER RECORD STRUCTURE


data RecordStructure = RecordStructure
    { _fields :: Map.Map String Variable
    , _extVar :: Variable
    , _extStruct :: ExtensionStructure
    }


data ExtensionStructure
    = Empty
    | Extension
    deriving (Eq, Ord, Show)


gatherFields :: Context -> Map.Map String Variable -> Variable -> Unify RecordStructure
gatherFields context fields variable =
  do  desc <- liftIO (UF.descriptor variable)
      case _content desc of
        Structure (Record1 subFields subExt) ->
            gatherFields context (Map.union fields subFields) subExt

        Structure EmptyRecord1 ->
            return (RecordStructure fields variable Empty)

        Alias _ _ var ->
            -- TODO may be dropping useful alias info here
            gatherFields context fields var

        _ ->
            return (RecordStructure fields variable Extension)

