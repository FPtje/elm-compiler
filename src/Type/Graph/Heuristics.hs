module Type.Graph.Heuristics where

import qualified Type.State as TS
import qualified Type.Graph.Basics as BS
import qualified Type.Graph.TypeGraph as TG
import qualified Type.Graph.Siblings as SB
import qualified Type.Graph.Path as P
import qualified Reporting.Annotation as A
import qualified Reporting.Error.Type as Error
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Type.Type as T

import Data.List (sortBy)
import Data.Maybe (fromMaybe)
import Control.Monad (when)
import Control.Monad.Except (liftIO)

import Debug.Trace

-- | Counts how often Initial edges occur in a set of error paths
-- Returns the total amount of paths,
-- a mapping between edgeIds and the information they hold and
-- the count of Initial edges in each path
participationMap :: P.Path a -> (Integer, M.Map BS.EdgeId a, M.Map BS.EdgeId Integer)
participationMap path =
    case path of
        P.Empty ->
            (1, M.empty, M.empty)
        P.Fail ->
            (0, M.empty, M.empty)
        P.Step eid (P.Initial a) ->
            (1, M.singleton eid a, M.singleton eid 1)
        P.Step _ _ ->
            (1, M.empty, M.empty)
        p1 P.:+: p2 ->
            let
                (i1, mp1, fm1) = participationMap p1
                (i2, mp2, fm2) = participationMap p2
                fm1'      = M.map (*i2) fm1
                fm2'      = M.map (*i1) fm2
            in
                (i1 * i2, mp1 `M.union` mp2, M.unionWith (\j1 j2 -> j1 + j2 - ((j1*j2) `div` (i1*i2))) fm1' fm2')
        p1 P.:|: p2 ->
            let
                (i1, mp1, fm1) = participationMap p1
                (i2, mp2, fm2) = participationMap p2
            in
                (i1 + i2, mp1 `M.union` mp2, M.unionWith (+) fm1 fm2)

-- | Share in paths heuristic
-- When one constraint appears in all error paths, only that constraint is returned
-- Otherwise, all the constraints are returned, ordered by how often they occur
-- Limited by a minimum ratio.
typePathShare :: Double -> [P.Path T.TypeConstraint] -> [(T.TypeConstraint, Double)]
typePathShare _ [] = []
typePathShare minRatio paths =
    let
        mergedPaths :: P.Path T.TypeConstraint
        mergedPaths = foldl1 (P.:|:) paths

        nrOfPaths :: Integer
        edgeMap :: M.Map BS.EdgeId T.TypeConstraint
        counts :: M.Map BS.EdgeId Integer
        (nrOfPaths, edgeMap, counts) = participationMap mergedPaths

        countList :: [(BS.EdgeId, Integer)]
        countList = sortBy (\(_, l) (_, r) -> compare r l) . M.toList $ counts

        fNrOfPaths :: Double
        fNrOfPaths = fromInteger nrOfPaths

        ratios :: [(T.TypeConstraint, Double)]
        ratios = map (\(e, c) -> (findEdge e, fromInteger c / fNrOfPaths)) countList

        findEdge :: BS.EdgeId -> T.TypeConstraint
        findEdge e = M.findWithDefault (error "Could not find a thing I put in here myself") e edgeMap

        inThreshold :: [(T.TypeConstraint, Double)]
        inThreshold = takeWhile ((> minRatio) . snd) ratios
    in
        if null inThreshold then
            ratios
        else
            inThreshold

-- | Apply sibling error hints when applicable
applySiblings :: TG.TypeGraph T.TypeConstraint -> [P.Path T.TypeConstraint] -> TS.Solver ()
applySiblings grph inconsistentPaths =
    do
        sbs <- TS.getSiblings
        sibSuggestions <- mapM (\ip -> SB.investigateSiblings sbs ip grph) inconsistentPaths

        SB.addSiblingSuggestions . S.unions $ sibSuggestions

-- | Uses the trust factor assigned to constraints
-- to sort (and prune) constraints
trustFactor :: Int -> [T.TypeConstraint] -> [T.TypeConstraint]
trustFactor prune constrs =
    let
        cond :: T.TypeConstraint -> T.TypeConstraint -> Ordering
        cond l r =
            case (T.trustFactor l, T.trustFactor r) of
                (Nothing, Nothing) -> EQ
                (Nothing, _) -> LT
                (_, Nothing) -> GT
                (Just tl, Just tr) -> compare (T.trustValuation tl) (T.trustValuation tr)

        pruneCond :: T.TypeConstraint -> Bool
        pruneCond constr =
            let
                trust = T.trustFactor constr
            in
                fromMaybe True ((> prune) . T.trustValuation <$> trust)

        filtered :: [T.TypeConstraint]
        filtered = filter pruneCond constrs
    in
        if (null filtered) then
            sortBy cond constrs
        else
            sortBy cond filtered

-- | Find error thrown by normal unify based on the region
-- Region might not be valid, as multiple errors could have the same region
findError :: T.TypeConstraint -> [A.Located Error.Error] -> Maybe (A.Located Error.Error)
findError constr@(T.CEqual _ crg _ _ _) (err@(A.A rg _) : xs)
    | rg == crg = Just err
    | otherwise = findError constr xs
findError constr@(T.CInstance crg _ _ _) (err@(A.A rg _) : xs)
    | rg == crg = Just err
    | otherwise = findError constr xs
findError _ _ = Nothing

-- | Throw an error that is stored in a constraint
throwErrorFromConstraint :: [A.Located Error.Error] -> T.TypeConstraint -> TS.Solver ()
throwErrorFromConstraint errs constr =
    case (findError constr errs, constr) of
        (Just (A.A rg err), _) -> TS.addError rg err
        (Nothing, T.CEqual hint rg lt rt _) ->
            do
                flt <- TS.flatten lt
                frt <- TS.flatten rt
                srcl <- liftIO $ T.toSrcType flt
                srcr <- liftIO $ T.toSrcType frt
                let info = Error.MismatchInfo hint srcl srcr Nothing []
                TS.addError rg (Error.Mismatch info)
        (Nothing, T.CInstance _ _ _ _) ->
            error "Didn't expect to see an instance here" -- TODO

-- | Replace the error of this part of the program
-- with the ones given by the heuristics
replaceErrors :: [T.TypeConstraint] -> TS.Solver ()
replaceErrors constrs =
    do
        errs <- TS.getError
        tgErrs <- TS.getTypeGraphErrors
        let relevantErrs = drop tgErrs errs
        trace ("\n\nElm would have thrown these errors: \n" ++ show tgErrs ++ "\n" ++ show relevantErrs) $ return ()

        TS.removeErrors (length errs - tgErrs)

        mapM_ (throwErrorFromConstraint relevantErrs) constrs


applyHeuristics :: TG.TypeGraph T.TypeConstraint -> TS.Solver ()
applyHeuristics grph =
    do
        trace ("\n\nGRAPH:\n" ++ show grph) $ return ()
        let grphErrs = TG.getErrors grph

        trace ("\n\nERRORS IN GRAPH\n" ++ show grphErrs) $ return ()
        let inconsistentPaths = concatMap TG.inconsistentTypesPaths grphErrs

        trace ("\n\nInconsistent paths: \n" ++ show inconsistentPaths) $ return ()

        -- Apply filter heuristics
        let errorPathShare = map fst $ typePathShare 0 inconsistentPaths
        trace ("\n\nShare in error paths: \n" ++ show (typePathShare 0 inconsistentPaths)) $ return ()
        let sortTrusted = trustFactor 800 errorPathShare

        trace ("\n\nAfter trusted: \n" ++ show sortTrusted) $ return ()

        when (not . null $ sortTrusted) $ do
            -- The classic "eh just pick the first one" heuristic
            -- Called the "Constraint number heuristic" in Top.
            let throwable = head sortTrusted

            replaceErrors [throwable]



        applySiblings grph inconsistentPaths

