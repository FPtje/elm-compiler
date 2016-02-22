module Type.Graph.Heuristics where

import qualified Type.State as TS
import qualified Type.Graph.Basics as BS
import qualified Type.Graph.TypeGraph as TG
import qualified Type.Graph.Siblings as SB
import qualified Type.Graph.Path as P
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Type.Type as T

import Data.List (sortBy)
import Data.Maybe (fromMaybe)

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
        inThreshold = takeWhile ((> minRatio) . snd) (tail ratios)
    in
        -- Give only one constraint when it appears in every error path
        if snd (head countList) == nrOfPaths then
            takeWhile ((>= 0.999) . snd) (tail ratios)
        else
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

applyHeuristics :: TG.TypeGraph T.TypeConstraint -> TS.Solver ()
applyHeuristics grph =
    do
        let grphErrs = TG.getErrors grph
        let inconsistentPaths = concatMap TG.inconsistentTypesPaths grphErrs

        -- Apply filter
        let errorPathShare = map fst $ typePathShare 0.8 inconsistentPaths
        let sortTrusted = trustFactor 800 errorPathShare

        applySiblings grph inconsistentPaths

