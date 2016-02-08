{-# OPTIONS_GHC -Wall #-}

module Type.Graph.EQGroup where

import qualified Type.Graph.Clique as CLQ
import qualified Type.Graph.Basics as BS
import qualified Type.Graph.Path as P
import qualified AST.Variable as Var
import Data.List (partition, nub, nubBy)

-- | Equivalence groups, TODO
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

        addEdge (edge@(BS.EdgeId v1 v2 _), info) groups =
            let is         = [v1, v2]
                (gs1, gs2) = partition (any ((`elem` is) . fst) . vertices) groups
            in insertEdge edge info (foldr combine empty gs1) : gs2
    in
        foldr addEdge (foldr addClique eqcs cs) es

-- | Representative vertex of an equivalence group
representative :: EquivalenceGroup info -> BS.VertexId
representative = fst . head . vertices

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
removeEdge eid grp = grp { edges = filter ((/= eid) . fst) $ edges grp }

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

-- | Returns the type of a group in the form in which it is stored
-- Will give the conflicting vertices when a type conflict is found
typeOfGroup :: EquivalenceGroup info -> Either [BS.VertexId] (BS.VertexId, BS.VertexInfo)
typeOfGroup eqgroup
    | length allConstants > 1                           = Left $ map fst allConstants ++ map fst allApplies
    | not (null allConstants) && not (null allApplies)  = Left $ map fst allConstants ++ map fst allApplies
    -- TODO: Multiple different applications?

    | not (null allConstants)  =  Right . head $ allConstants
    | not (null allApplies)    =  Right . head $ allApplies
    | otherwise                =  Right . head . vertices $ eqgroup

    where
        cmp :: (BS.VertexId, BS.VertexInfo) -> (BS.VertexId, BS.VertexInfo) -> Bool
        cmp (_, (l, _)) (_, (r, _)) = l == r

        allConstants  = nubBy cmp [ c       |  c@(_, (BS.VCon _, _))    <- vertices eqgroup  ]
        allApplies    =           [ a       |  a@(_, (BS.VApp {}, _))   <- vertices eqgroup  ]

-- | All equality paths between two vertices.
equalPaths :: BS.VertexId -> BS.VertexId -> EquivalenceGroup info -> P.Path info
equalPaths start target eqgroup =
    let
        edgeList = edges eqgroup

        cliqueList :: [[CLQ.ParentChild]]
        cliqueList = map CLQ.unclique . cliques $ eqgroup

        rec :: BS.VertexId -> ([(BS.EdgeId, info)], [[CLQ.ParentChild]]) -> P.Path info
        rec v1 (es, cs)
            | v1 == target = P.Empty -- Path to itself is empty
            | otherwise =
                let
                    -- Edges from this vertex
                    (edgesFrom, es') = partition (\(BS.EdgeId a _ _, _) -> v1 == a) es
                    -- Edges to this vertex
                    (edgesTo, es'') = partition (\(BS.EdgeId _ a _, _) -> v1 == a) es'

                    -- The neighboring cliques of which v1 is a member
                    (neighbourCliques, otherCliques) = partition ((v1 `elem`) . map CLQ.child) cs
                    rest = (es'', otherCliques)
                in
                    P.concatPath $

                    -- Add steps to all edges coming from this node
                    map (\(BS.EdgeId _ neighbour edgeNr, info) ->
                        P.Step (BS.EdgeId v1 neighbour edgeNr) (P.Initial info)
                        P.:+: rec neighbour rest) edgesFrom

                    -- Add steps to all edges going to this node
                    ++ map (\(BS.EdgeId neighbour _ edgeNr, info) ->
                        P.Step (BS.EdgeId v1 neighbour edgeNr) (P.Initial info)
                        P.:+: rec neighbour rest) edgesTo

                    -- Creates all implied edges
                    ++ concatMap (\list ->
                                  let (sources, others) = partition ((v1==) . CLQ.child) list
                                      sourceParents     = map CLQ.parent sources
                                      neighbours        = nub (map CLQ.child others)
                                      f neighbour       = P.concatPath
                                         [ beginPath P.:+: restPath
                                         | pc <- others
                                         , CLQ.child pc == neighbour
                                         , let beginPath = P.concatPath1 (map g sourceParents)
                                               restPath = rec neighbour rest
                                               g sp = P.Step (BS.EdgeId v1 neighbour (-1)) (P.Implied (CLQ.childSide pc) sp (CLQ.parent pc))
                                         ]
                                  in if null sources
                                       then []
                                       else map f neighbours) neighbourCliques
    in
        P.simplify $
        rec start (edgeList, cliqueList)
