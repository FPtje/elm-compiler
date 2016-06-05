{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}

module Type.Graph.EQGroup where

import qualified Type.Graph.Clique as CLQ
import qualified Type.Graph.Basics as BS
import qualified Type.Graph.Path as P
import qualified Type.Type as T
import qualified AST.Variable as Var
import qualified Data.Map as M
import Data.List (partition, nub)
import Data.Maybe (listToMaybe, mapMaybe)
import Control.Applicative ((<|>))

-- | Equivalence groups
data EquivalenceGroup info = EQGroup
    { vertices                  :: [(BS.VertexId, BS.VertexInfo)]     -- ^ Vertices in this equivalence group
    , edges                     :: [(BS.EdgeId, info)]             -- ^ (Initial) edges in this equivalence group
    , cliques                   :: [CLQ.Clique]                 -- ^ (Implied) cliques in this equivalence group
    }


showMVar :: BS.VertexInfo -> String
showMVar (vid, Nothing) = "(" ++ show vid ++ ", " ++ "Nothing)"
showMVar (vid, Just x) = "(" ++ show vid ++ ", " ++ Var.name x ++ ")"

instance Show info => Show (EquivalenceGroup info) where

    show eg =
        showString "EquivalenceGroup { " .
        showString "\n    Vertices: " . shows (map (\(vid, inf) -> (vid, showMVar inf)) (vertices eg)) .
        showString "\n    Edges: " . shows (edges eg) . showString ", " .
        showString "\n    cliques: " . shows (cliques eg) .
        showString "\n}"
        $
        ""


-- | Empty equivalence group
empty :: EquivalenceGroup info
empty = EQGroup
    { vertices = []
    , edges = []
    , cliques = []
    }

-- | Combines two equivalence groups
combine :: EquivalenceGroup info -> EquivalenceGroup info -> EquivalenceGroup info
combine eqgroup1 eqgroup2 = EQGroup
    { vertices = vertices eqgroup1 ++ vertices eqgroup2
    , edges    = edges    eqgroup1 ++ edges    eqgroup2
    , cliques  = cliques  eqgroup1 `CLQ.combine` cliques  eqgroup2
    }

-- | Splits an equivalence group into <TODO>
-- Used as helper function for removing an edge in the type graph
split :: EquivalenceGroup info -> [EquivalenceGroup info]
split grp =
    let
        (vs, es, cs) = (vertices grp, edges grp, cliques grp)
        eqcs = map (\(a, b) -> insertVertex a b empty) vs

        addClique clique groups =
            let is         = CLQ.children clique
                (gs1, gs2) = partition (any ((`elem` is) . fst) . vertices) groups
            in insertClique clique (foldr combine empty gs1) : gs2

        addEdge (edge@(BS.EdgeId v1 v2), info) groups =
            let is         = [v1, v2]
                (gs1, gs2) = partition (any ((`elem` is) . fst) . vertices) groups
            in insertEdge edge info (foldr combine empty gs1) : gs2
    in
        foldr addEdge (foldr addClique eqcs cs) es

-- | Representative vertex of an equivalence group
representative :: EquivalenceGroup info -> BS.VertexId
representative = fst . head . vertices

-- | Returns the parent of a vertex
getParent :: BS.VertexId -> EquivalenceGroup info -> Maybe BS.VertexId
getParent v grp = listToMaybe . mapMaybe (CLQ.getParent v) $ (cliques grp)

-- | Inserts a vertex into an equivalence group
insertVertex :: BS.VertexId -> BS.VertexInfo -> EquivalenceGroup info -> EquivalenceGroup info
insertVertex vid vk grp =
    grp { vertices = (vid, vk) : vertices grp }

-- | Removes a vertex from an equivalence group
removeVertex :: BS.VertexId -> EquivalenceGroup info -> EquivalenceGroup info
removeVertex vid grp =
    grp { vertices = filter ((/= vid) . fst) $ vertices grp }

-- | Inserts an Edge into an equivalence group
insertEdge :: BS.EdgeId -> info -> EquivalenceGroup info -> EquivalenceGroup info
insertEdge eid info grp =
    grp { edges = (eid, info) : edges grp }

-- | Removes an Edge from an equivalence group
removeEdge :: BS.EdgeId -> EquivalenceGroup info -> EquivalenceGroup info
removeEdge eid grp = grp { edges = filter ((/= BS.undirected eid) . BS.undirected . fst) $ edges grp }

-- | Inserts a clique into an equivalence group
-- Merges the clique with potentially overlapping cliques
insertClique :: CLQ.Clique -> EquivalenceGroup info -> EquivalenceGroup info
insertClique cl grp =
    let
        merged = CLQ.merge (cl : overlapping)
        (disjoints, overlapping) = partition (CLQ.isDisjoint cl) (cliques grp)
    in
        grp { cliques = merged : disjoints }

-- | Removes a clique from an equivalence group
-- Specifically, removes all cliques that are a subset of the given clique
removeClique :: CLQ.Clique -> EquivalenceGroup info -> EquivalenceGroup info
removeClique cl grp =
    grp { cliques = filter (not . (`CLQ.isSubsetClique` cl)) (cliques grp) }


-- | Try to find a path of initial edges between two elements of the same EQGroup
initialEdgePath :: forall info . BS.EdgeId -> EquivalenceGroup info -> Maybe (P.Path info, M.Map BS.EdgeId (P.Path info))
initialEdgePath eid@(BS.EdgeId l r) grp =
    let
        edgeMap :: M.Map BS.VertexId [(BS.VertexId, BS.EdgeId, info)]
        edgeMap = M.fromListWith (++)
                    (  [(l', [(r', eid', inf)]) | (eid'@(BS.EdgeId l' r'), inf) <- edges grp]
                    ++ [(r', [(l', eid', inf)]) | (eid'@(BS.EdgeId l' r'), inf) <- edges grp])

        rec :: M.Map BS.VertexId [(BS.VertexId, BS.EdgeId, info)] -> BS.VertexId -> P.Path info -> Maybe (P.Path info)
        rec mp i p
            | i == r = Just p -- the path has been found
            | not (i `M.member` mp) = Nothing
            | otherwise =
                let
                    nextEdges :: [(BS.VertexId, BS.EdgeId, info)]
                    nextEdges = M.findWithDefault undefined i mp

                    -- make sure we don't loop edges
                    nextMap :: M.Map BS.VertexId [(BS.VertexId, BS.EdgeId, info)]
                    nextMap = M.delete i mp

                    nextSteps :: [P.Path info]
                    nextSteps = [p P.:+: (P.Step eid' (P.Initial inf)) | (_, eid', inf) <- nextEdges]

                    recCalls :: [Maybe (P.Path info)]
                    recCalls = zipWith (\(i', _, _) p' -> rec nextMap i' p') nextEdges nextSteps
                in
                    foldl1 (<|>) recCalls
    in
        do
            pth <- P.simplify <$> rec edgeMap l P.Empty
            return (pth, M.singleton eid pth)

-- | Returns the type of a group in the form in which it is stored
-- Will give the conflicting vertices when a type conflict is found
typeOfGroup :: EquivalenceGroup info -> Either [(BS.VertexId, BS.VertexId)] (BS.VertexId, BS.VertexInfo)
typeOfGroup eqgroup
    | not (null combinations)  =  Left combinations -- pairs of vertices with different base types
    | not (null allConstants)  =  Right . head $ allConstants
    | not (null allApplies)    =  Right . head $ allApplies
    | otherwise                =  Right reprVar

    where
        -- combine
        cmbn :: [BS.VertexId] -> [BS.VertexId] -> [(BS.VertexId, BS.VertexId)]
        cmbn l r = [(l', r') | l' <- l, r' <- r]

        pairs :: [a] -> [(a, a)]
        pairs [] = []
        pairs (_ : []) = []
        pairs (x : y : xs) = (x, y) : (pairs (x : xs) ++ pairs (y : xs))

        combinations :: [(BS.VertexId, BS.VertexId)]
        combinations = nub $
               BS.consistent allPredicates -- Consistency between predicates
            ++ concat [cmbn lgrp rgrp | (lgrp, rgrp) <- pairs conflictGroups] -- Inconsistent types
            ++ evidenceLackingCons -- Constructors that have no evidence for required predicates
            ++ recordEvidence -- Records with different sets of fields
            ++ rigidVarsConflicts -- Rigid variables containing different sets of predicates
            ++ flexRigidConflicts -- Predicates that are in flex variables but not on rigid variables


        insert :: M.Map BS.VertexKind [BS.VertexId]
            -> (BS.VertexId, BS.VertexInfo)
            -> M.Map BS.VertexKind [BS.VertexId]
        insert mp (vid, (knd, _)) = M.insertWith (++) knd [vid] mp

        groupMap :: M.Map BS.VertexKind [BS.VertexId]
        groupMap = foldl insert M.empty allConstants

        -- A representative type variable
        reprVar :: (BS.VertexId, BS.VertexInfo)
        reprVar = head [ (vid, (BS.VVar rigid preds, x)) | (vid, (BS.VVar rigid _, x)) <- allRigids ++ allFlex, let preds = nub $ concatMap snd allPredicates ]

        -- Conflicts between rigid variables containing different predicates
        rigidVarsConflicts :: [(BS.VertexId, BS.VertexId)]
        rigidVarsConflicts = [ (lid, rid) | (lid, (BS.VVar _ lpreds, _)) <- allRigids, (rid, (BS.VVar _ rpreds, _)) <- allRigids, lpreds /= rpreds ]

        -- All the groups of different type applications, rigid variables and constants
        conflictGroups :: [[BS.VertexId]]
        conflictGroups = map fst allRigids : map fst allApplies : (map snd . M.toList $ groupMap)

        -- Conflicts between the predicates of rigid and flex variables
        flexRigidConflicts :: [(BS.VertexId, BS.VertexId)]
        flexRigidConflicts = [ (rid, fid) | (rid, rpreds) <- rigidPredicates, (fid, fpreds) <- flexPredicates, not $ all (`elem` rpreds) fpreds ]

        flexPredicates :: [(BS.VertexId, [BS.Predicate])]
        flexPredicates = [(vid, preds) | (vid, (BS.VVar T.Flex preds, _)) <- vertices eqgroup]

        rigidPredicates :: [(BS.VertexId, [BS.Predicate])]
        rigidPredicates = [(vid, preds) | (vid, (BS.VVar T.Rigid preds, _)) <- vertices eqgroup]

        allPredicates :: [(BS.VertexId, [BS.Predicate])]
        allPredicates = filter (\(_, ps) -> not $ null ps) $ rigidPredicates ++ flexPredicates

        evidenceLackingCons :: [(BS.VertexId, BS.VertexId)]
        evidenceLackingCons = [(cId, vId) | (cId, (BS.VCon _ evidence, _)) <- allConstants, (vId, preds) <- allPredicates, not . null $ BS.matchEvidence preds evidence]

        recordEvidence :: [(BS.VertexId, BS.VertexId)]
        recordEvidence = [(c1Id, c2Id) | (c1Id, (BS.VCon "1Record" [ev1], _)) <- allConstants, (c2Id, (BS.VCon "1Record" [ev2], _)) <- allConstants, c1Id < c2Id, not $ BS.matchConsEvidence ev1 ev2]

        allConstants, allApplies, allRigids, allFlex :: [(BS.VertexId, BS.VertexInfo)]
        allConstants  = [c | c@(_, (BS.VCon _ _, _)) <- vertices eqgroup]
        allApplies    = [a | a@(_, (BS.VApp {}, _)) <- vertices eqgroup]
        allRigids     = [a | a@(_, (BS.VVar T.Rigid _, _)) <- vertices eqgroup]
        allFlex       = [a | a@(_, (BS.VVar T.Flex _, _)) <- vertices eqgroup]

-- | All equality paths between two vertices.
equalPaths :: BS.VertexId -> BS.VertexId -> EquivalenceGroup info -> P.Path info
equalPaths start target eqgroup = P.Step (BS.EdgeId start target) P.Implied
    -- let
    --     edgeList = edges eqgroup

    --     cliqueList :: [[CLQ.ParentChild]]
    --     cliqueList = map CLQ.unclique . cliques $ eqgroup

    --     rec :: BS.VertexId -> ([(BS.EdgeId, info)], [[CLQ.ParentChild]]) -> P.Path info
    --     rec v1 (es, cs)
    --         | v1 == target = P.Empty -- Path to itself is empty
    --         | otherwise =
    --             let
    --                 -- Edges from this vertex
    --                 (edgesFrom, es') = partition (\(BS.EdgeId a _, _) -> v1 == a) es
    --                 -- Edges to this vertex
    --                 (edgesTo, es'') = partition (\(BS.EdgeId _ a, _) -> v1 == a) es'

    --                 -- The neighboring cliques of which v1 is a member
    --                 (neighbourCliques, otherCliques) = partition ((v1 `elem`) . map CLQ.child) cs
    --                 rest = (es'', otherCliques)
    --             in
    --                 P.choice $

    --                 -- Add steps to all edges coming from this node
    --                 map (\(BS.EdgeId _ neighbour, info) ->
    --                     P.Step (BS.EdgeId v1 neighbour) (P.Initial info)
    --                     P.:+: rec neighbour rest) edgesFrom

    --                 -- Add steps to all edges going to this node
    --                 ++ map (\(BS.EdgeId neighbour _, info) ->
    --                     P.Step (BS.EdgeId neighbour v1) (P.Initial info)
    --                     P.:+: rec neighbour rest) edgesTo

    --                 -- Creates all implied edges
    --                 ++ concatMap (\list ->
    --                               let (sources, others) = partition ((v1==) . CLQ.child) list
    --                                   neighbours        = nub (map CLQ.child others)
    --                                   f neighbour       = P.Step (BS.EdgeId v1 neighbour) P.Implied P.:+: rec neighbour rest
    --                               in if null sources
    --                                    then []
    --                                    else map f neighbours) neighbourCliques
    -- in
    --     P.simplify $
    --     rec start (edgeList, cliqueList)
