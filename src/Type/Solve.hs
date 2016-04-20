module Type.Solve (solve) where

import Control.Monad
import qualified AST.Module as Module
import Control.Monad.State (execStateT, liftIO)
import Control.Monad.Except (ExceptT, throwError)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Traversable as T
import qualified Data.UnionFind.IO as UF
import qualified Data.Set as S

import qualified Reporting.Annotation as A
import qualified Reporting.Error.Type as Error
import qualified Type.State as TS
import qualified Type.Graph.TypeGraph as TG
import qualified Type.Graph.Heuristics as TH
import Type.Type as Type
import Type.Unify
import qualified AST.Interface as Interface

import Debug.Trace

{-| Every variable has rank less than or equal to the maxRank of the pool.
This sorts variables into the young and old pools accordingly.
-}
generalize :: TS.Pool -> TS.Solver ()
generalize youngPool =
  do  youngMark <- TS.uniqueMark
      let youngRank = TS.maxRank youngPool
      let insert dict var =
            do  descriptor <- liftIO $ UF.descriptor var
                liftIO $ UF.modifyDescriptor var (\desc -> desc { _mark = youngMark })
                return $ Map.insertWith (++) (_rank descriptor) [var] dict

      -- Sort the youngPool variables by rank.
      rankDict <- foldM insert Map.empty (TS.inhabitants youngPool)

      -- get the ranks right for each entry.
      -- start at low ranks so that we only have to pass
      -- over the information once.
      visitedMark <- TS.uniqueMark
      forM (Map.toList rankDict) $ \(poolRank, vars) ->
          mapM (adjustRank youngMark visitedMark poolRank) vars

      -- For variables that have rank lowerer than youngRank, register them in
      -- the old pool if they are not redundant.
      let registerIfNotRedundant var =
            do  isRedundant <- liftIO $ UF.redundant var
                if isRedundant then return var else TS.register var

      let rankDict' = Map.delete youngRank rankDict
      T.traverse (mapM registerIfNotRedundant) rankDict'

      -- For variables with rank youngRank
      --   If rank < youngRank: register in oldPool
      --   otherwise generalize
      let registerIfLowerRank var = do
            isRedundant <- liftIO $ UF.redundant var
            case isRedundant of
              True -> return ()
              False -> do
                desc <- liftIO $ UF.descriptor var
                case _rank desc < youngRank of
                  True ->
                      TS.register var >> return ()
                  False ->
                      liftIO $ UF.setDescriptor var $ desc
                        { _rank = noRank
                        , _content = rigidify (_content desc)
                        }

      mapM_ registerIfLowerRank (Map.findWithDefault [] youngRank rankDict)


rigidify :: Content -> Content
rigidify content =
  case content of
    Var Flex maybeSuper _ ->
        Var Rigid maybeSuper Nothing

    _ ->
        content


-- adjust the ranks of variables such that ranks never increase as you
-- move deeper into a variable.
adjustRank :: Int -> Int -> Int -> Variable -> TS.Solver Int
adjustRank youngMark visitedMark groupRank var =
  do  descriptor <- liftIO $ UF.descriptor var
      adjustRankHelp youngMark visitedMark groupRank var descriptor


adjustRankHelp :: Int -> Int -> Int -> Variable -> Descriptor -> TS.Solver Int
adjustRankHelp youngMark visitedMark groupRank var descriptor =
  if _mark descriptor == youngMark then

      do  -- Set the variable as marked first because it may be cyclic.
          liftIO $ UF.modifyDescriptor var $ \desc ->
              desc { _mark = visitedMark }

          maxRank <-
              adjustRankContent youngMark visitedMark groupRank (_content descriptor)

          liftIO $ UF.modifyDescriptor var $ \desc ->
              desc { _rank = maxRank }

          return maxRank

  else if _mark descriptor /= visitedMark then

      do  let minRank = min groupRank (_rank descriptor)
          liftIO $ UF.setDescriptor var (descriptor { _mark = visitedMark, _rank = minRank })
          return minRank

  else

      return (_rank descriptor)


adjustRankContent :: Int -> Int -> Int -> Content -> TS.Solver Int
adjustRankContent youngMark visitedMark groupRank content =
  let
    go = adjustRank youngMark visitedMark groupRank
  in
    case content of
      Error _ ->
          return groupRank

      Atom _ ->
          return groupRank

      Var _ _ _ ->
          return groupRank

      Alias _ args realVar ->
          maximum <$> mapM go (realVar : map snd args)

      Structure (App1 func arg) ->
          max <$> go func <*> go arg

      Structure (Fun1 arg result) ->
          max <$> go arg <*> go result

      Structure EmptyRecord1 ->
          return outermostRank

      Structure (Record1 fields extension) ->
          maximum <$> mapM go (extension : Map.elems fields)



-- SOLVER


-- | Invokes the type graph if errors are found.
invokeTypeGraph :: TypeConstraint -> TS.Solver ()
invokeTypeGraph constraint =
  do
    errs <- TS.getError
    tgErrs <- TS.getTypeGraphErrors
    when (length errs > tgErrs) $ do
        oldEnv <- TS.getEnv

        graph <- TG.fromConstraint constraint
        TH.applyHeuristics graph

        TS.modifyEnv (const oldEnv)


solve :: TypeConstraint -> Module.Siblings -> [(Interface.CanonicalInterface, Interface.CanonicalImplementation)] -> ExceptT [A.Located Error.Error] IO TS.SolverState
solve constraint siblings impls =
  do
      state <-
          liftIO (execStateT (actuallySolve [] constraint) (TS.initialState siblings impls))
      case TS.sError state of
        [] ->
            return state
        errors ->
            throwError errors


-- | Decides whether a later constraint should be passed down
-- into the tree of an earlier constraint
-- This gives type graphs extra information to work with
shouldPassConstrDown :: TypeConstraint -> Bool
shouldPassConstrDown CEqual {} = True
shouldPassConstrDown (CLet _ CTrue) = True
shouldPassConstrDown _ = False

-- | Decides whether a later constraint should be passed to neighbors
shouldPassConstrForwards :: TypeConstraint -> Bool
shouldPassConstrForwards CEqual {} = True
shouldPassConstrForwards _ = False


actuallySolve :: [TypeConstraint] -> TypeConstraint -> TS.Solver ()
actuallySolve extraConstrs constraint =
  case constraint of
    CTrue ->
        return ()

    CSaveEnv ->
        TS.saveLocalEnv

    CEqual hint region term1 term2 _ ->
        do  t1 <- TS.flatten term1
            t2 <- TS.flatten term2
            trace ("\nCEQUAL!" ++ show hint ++ "\n" ++ show t1 ++ "\n\n" ++ show t2 ++ "\n\nTERMS:\n" ++ show term1 ++ "\n\n" ++ show term2) $ return ()
            unify hint region t1 t2

    CAnd [] -> return ()
    CAnd (c : cs) ->
        do
          let passDown = filter shouldPassConstrDown cs ++ extraConstrs
          actuallySolve passDown c

          let passFwd = if shouldPassConstrForwards c then (c:) else id

          actuallySolve (passFwd extraConstrs) (CAnd cs)

    CLet [Scheme [] fqs constraint' _] CTrue ->
        do  oldEnv <- TS.getEnv
            mapM TS.introduce fqs

            copy <- liftIO $ copyConstraint (CAnd $ constraint' : extraConstrs)
            actuallySolve extraConstrs constraint'
            invokeTypeGraph copy

            TS.modifyEnv (\_ -> oldEnv)

    CLet schemes constraint' ->
        do  oldEnv <- TS.getEnv
            headers <- Map.unions <$> mapM (solveScheme extraConstrs) schemes
            TS.modifyEnv $ \env -> Map.union headers env

            copy <- liftIO $ copyConstraint (CAnd $ constraint' : extraConstrs)
            actuallySolve extraConstrs constraint'
            mapM occurs $ Map.toList headers
            invokeTypeGraph copy

            TS.modifyEnv (\_ -> oldEnv)

    CInstance region name term _ ->
        do  env <- TS.getEnv

            freshCopy <-
                case Map.lookup name env of
                  Just (A.A _ tipe) ->
                      TS.makeInstance tipe

                  Nothing ->
                      if List.isPrefixOf "Native." name then
                          liftIO (mkVar Nothing)

                      else
                          error ("Could not find `" ++ name ++ "` when solving type constraints.")

            t <- TS.flatten term
            trace ("\n\nCINSTANCE! " ++ show name ++ "\nRIGHT: " ++ show t ++ "\n:TERM: " ++ show term ++ "\n;LEFT: " ++ show freshCopy) $ return ()
            unify (Error.Instance name) region freshCopy t
            trace ("\n\nAFTERCINSTANCE! " ++ show name ++ "\nRIGHT: " ++ show t ++ "\n:TERM: " ++ show term ++ "\n;LEFT: " ++ show freshCopy) $ return ()


solveScheme :: [TypeConstraint] -> TypeScheme -> TS.Solver (Map.Map String (A.Located Variable))
solveScheme extraConstrs scheme =
  let
    flatten (A.A region term) =
      A.A region <$> TS.flatten term
  in
  case scheme of
    Scheme [] [] constraint header ->
        do
            copy <- liftIO $ copyConstraint (CAnd $ constraint : extraConstrs)
            actuallySolve extraConstrs constraint
            invokeTypeGraph copy

            T.traverse flatten header

    Scheme rigidQuantifiers flexibleQuantifiers constraint header ->
        do  let quantifiers = rigidQuantifiers ++ flexibleQuantifiers
            oldPool <- TS.getPool

            -- fill in a new pool when working on this scheme's constraints
            freshPool <- TS.nextRankPool
            TS.switchToPool freshPool
            mapM TS.introduce quantifiers
            header' <- T.traverse flatten header


            copy <- liftIO $ copyConstraint (CAnd $ constraint : extraConstrs)
            actuallySolve extraConstrs constraint
            invokeTypeGraph copy

            allDistinct rigidQuantifiers
            youngPool <- TS.getPool
            TS.switchToPool oldPool
            generalize youngPool
            mapM isGeneric rigidQuantifiers
            return header'


-- ADDITIONAL CHECKS

-- Checks that all of the given variables belong to distinct equivalence classes.
-- Also checks that their structure is Nothing, so they represent a variable, not
-- a more complex term.
allDistinct :: [Variable] -> TS.Solver ()
allDistinct vars =
  do  seenMark <- TS.uniqueMark
      forM_ vars $ \var ->
        do  desc <- liftIO $ UF.descriptor var
            case _content desc of
              Structure _ ->
                  crash "Can only generalize type variables, not structures."

              Atom _ ->
                  crash "Can only generalize type variables, not structures."

              Alias _ _ _ ->
                  crash "Can only generalize type variables, not aliases."

              Error _ ->
                  crash "Can only generalize type variables, not error types."

              Var _ _ _ ->
                  if _mark desc == seenMark then
                      crash "Duplicate variable during generalization."

                  else
                      liftIO (UF.setDescriptor var (desc { _mark = seenMark }))


-- Check that a variable has rank == noRank, meaning that it can be generalized.
isGeneric :: Variable -> TS.Solver ()
isGeneric var =
  do  desc <- liftIO $ UF.descriptor var
      if _rank desc == noRank
        then return ()
        else crash "Unable to generalize a type variable. It is not unranked."


crash :: String -> a
crash msg =
  error $
    "It looks like something went wrong with the type inference algorithm.\n\n"
    ++ msg ++ "\n\n"
    ++ "Please create a minimal example that triggers this problem and report it to\n"
    ++ "<https://github.com/elm-lang/elm-compiler/issues>"



-- OCCURS CHECK


occurs :: (String, A.Located Variable) -> TS.Solver ()
occurs (name, A.A region variable) =
  do  isInfinite <- liftIO $ occursHelp [] variable
      case isInfinite of
        False ->
            return ()

        True ->
            do  overallType <- liftIO (Type.toSrcType variable)
                TS.addError region (Error.InfiniteType name overallType)


occursHelp :: [Variable] -> Variable -> IO Bool
occursHelp seen var =
  if elem var seen then
      do  infiniteDescriptor <- UF.descriptor var
          UF.setDescriptor var (infiniteDescriptor { _content = Error (_content infiniteDescriptor) })
          return True

  else
      do  desc <- UF.descriptor var
          case _content desc of
            Atom _ ->
                return False

            Var _ _ _ ->
                return False

            Error _ ->
                return False

            Alias _ args _ ->
                -- TODO is it okay to only check args?
                or <$> mapM (occursHelp (var:seen) . snd) args

            Structure term ->
                let
                  go = occursHelp (var:seen)
                in
                case term of
                  App1 a b ->
                      (||) <$> go a <*> go b

                  Fun1 a b ->
                      (||) <$> go a <*> go b

                  EmptyRecord1 ->
                      return False

                  Record1 fields ext ->
                      or <$> mapM go (ext : Map.elems fields)
