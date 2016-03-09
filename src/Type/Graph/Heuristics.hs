{-# LANGUAGE ScopedTypeVariables #-}
module Type.Graph.Heuristics where

import qualified Type.State as TS
import qualified Type.Graph.Basics as BS
import qualified Type.Graph.TypeGraph as TG
import qualified Type.Graph.EQGroup as EG
import qualified Type.Graph.Siblings as SB
import qualified Type.Graph.Path as P
import qualified Reporting.Annotation as A
import qualified Reporting.Error.Type as Error
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Type.Type as T
import qualified AST.Type as AT

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
        -- Give only the constraints that appear in every error path
        -- when they exist
        if null inThreshold then
            ratios
        else
            if snd (head countList) == nrOfPaths then
                takeWhile ((>= 0.999) . snd) ratios
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

-- | Find the smallest set of nodes to remove to resolve an infinite type
infinitePathShare :: forall info . [TG.SubstitutionError info] -> [BS.VertexId]
infinitePathShare errs =
    let

        addCount :: P.Path info -> M.Map BS.VertexId Int -> M.Map BS.VertexId Int
        addCount (l P.:|: r) mp = M.unionWith (+) (addCount l mp) (addCount r mp)
        addCount (l P.:+: r) mp = M.unionWith (+) (addCount l mp) (addCount r mp)
        addCount (P.Step (BS.EdgeId l _) _) mp = M.insertWith (+) l 1 mp
        addCount _ mp = mp

        countMap :: M.Map BS.VertexId Int
        countMap = M.unionsWith (+) [addCount path M.empty | (TG.InfiniteType _ path) <- errs]

        sortCond :: (BS.VertexId, Int) -> (BS.VertexId, Int) -> Ordering
        sortCond (_, l) (_, r) = compare r l

        -- We're not interested in how often they really occur
        -- just which ones occur the most often
        sortedNodes :: [(BS.VertexId)]
        sortedNodes = map fst . sortBy sortCond . M.toList $ countMap

        pathSet :: P.Path info -> S.Set BS.VertexId
        pathSet (l P.:|: r) = pathSet l `S.union` pathSet r
        pathSet (l P.:+: r) = pathSet l `S.union` pathSet r
        pathSet (P.Step (BS.EdgeId l _) _) = S.insert l S.empty
        pathSet _ = S.empty

        pathSets :: [S.Set BS.VertexId]
        pathSets = filter (not . S.null) [pathSet path | (TG.InfiniteType _ path) <- errs]

        -- Ordered list of most occurring vertexIds
        -- The list of paths that haven't been removed
        -- Returns the list of vertices that need to be removed
        rec :: [BS.VertexId] -> [S.Set BS.VertexId] -> [BS.VertexId] -> [BS.VertexId]
        rec [] _ _ = []
        rec (vid : vids) paths accum =
            let
                filteredPaths :: [S.Set BS.VertexId]
                filteredPaths = filter (not . S.member vid) paths

                res :: [BS.VertexId]
                res = vid : accum
            in
                if null filteredPaths then
                    res
                else
                    rec vids filteredPaths res
    in
        -- The (heuristically defined) minimal amount of nodes that need to
        -- be replaced with an infinite type marker to solve all infinite types
        rec sortedNodes pathSets []

-- | Infinite paths always have a vertex that is the left side of a CInstance edge
-- When the infinite types are reconstructed, we'll know what variables they belong to
infinitePathRoots :: [TG.SubstitutionError T.TypeConstraint] -> TG.TypeGraph T.TypeConstraint -> [(BS.VertexId, A.Located T.SchemeName)]
infinitePathRoots errs grph =
    let
        vertexInstance :: BS.VertexId -> M.Map BS.VertexId (A.Located T.SchemeName)
        vertexInstance vid =
            let
                grp :: EG.EquivalenceGroup T.TypeConstraint
                grp = TG.getVertexGroup vid grph

                rightEdges :: [(BS.VertexId, A.Located T.SchemeName)]
                rightEdges = [(vid, A.A rg name) | (BS.EdgeId l _, T.CInstance rg name _ _) <- EG.edges grp, l == vid]
            in
                M.fromList rightEdges

        pathInstances :: P.Path T.TypeConstraint -> M.Map BS.VertexId (A.Located T.SchemeName)
        pathInstances (l P.:|: r) = pathInstances l `M.union` pathInstances r
        pathInstances (l P.:+: r) = pathInstances l `M.union` pathInstances r
        pathInstances (P.Step (BS.EdgeId l _) _) = vertexInstance l
        pathInstances _ = M.empty

        paths :: [P.Path T.TypeConstraint]
        paths = [path | (TG.InfiniteType _ path) <- errs]
    in
        M.toList . M.unions . map pathInstances $ paths

-- | Try to reconstruct as much of the infinite types as we can
reconstructInfiniteTypes :: S.Set BS.VertexId -> [(BS.VertexId, A.Located T.SchemeName)] -> TG.TypeGraph info -> [(A.Located T.SchemeName, AT.Canonical)]
reconstructInfiniteTypes infs roots grph =
        map (\(vid, nm) -> (nm, TG.reconstructInfiniteType vid infs grph)) roots

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

-- | Throw infinite type errors
throwErrorFromInfinite :: [(A.Located T.SchemeName, AT.Canonical)] -> TS.Solver ()
throwErrorFromInfinite errs =
    let
        throwErr :: (A.Located T.SchemeName, AT.Canonical) -> TS.Solver ()
        throwErr (A.A rg name, tp) = TS.addError rg (Error.InfiniteType name tp)
    in
        mapM_ throwErr errs

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
        let expandedPaths = map (TG.expandPath grph) inconsistentPaths

        trace ("\n\nInconsistent paths: \n" ++ show inconsistentPaths) $ return ()

        trace ("\n\n\nAND NOW FOR THE EXPANDED PATHS!!!\n" ++ show expandedPaths) $ return ()

        -- Apply filter heuristics
        let errorPathShare = map fst $ typePathShare 0.8 expandedPaths
        trace ("\n\nShare in error paths: \n" ++ show (typePathShare 0 expandedPaths)) $ return ()
        let sortTrusted = trustFactor 800 errorPathShare

        trace ("\n\nAfter trusted: \n" ++ show sortTrusted) $ return ()

        let infiniteRoots = infinitePathRoots grphErrs grph
        let infiniteShare = S.fromList $ infinitePathShare grphErrs
        trace ("\n\nINFINITE: PATH ROOTS\n" ++ show (infinitePathRoots grphErrs grph)) $ return ()
        trace ("\n\nINFINITE: REMOVE NODES \n" ++ show (infinitePathShare grphErrs)) $ return ()
        let reconstr = reconstructInfiniteTypes infiniteShare infiniteRoots grph
        trace ("\n\nINFINITE: RECONSTRUCTED: \n" ++ show reconstr) $ return ()



        when (not . null $ sortTrusted) $ do
            -- The classic "eh just pick the first one" heuristic
            -- Called the "Constraint number heuristic" in Top.
            let throwable = head sortTrusted

            replaceErrors [throwable]

        throwErrorFromInfinite reconstr

        applySiblings grph expandedPaths

