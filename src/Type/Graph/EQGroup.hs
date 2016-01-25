{-# OPTIONS_GHC -Wall #-}

module Type.Graph.EQGroup where

import qualified Type.Graph.Clique as CLQ
import qualified Type.Graph.Basics as BS
import qualified AST.Variable as Var
import Data.List (partition)


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
        showString "Vertices: " . shows (map (\(vid, inf) -> (vid, showMVar inf)) (vertices eg)) .
        showString "Edges: " . shows (edges eg) . showString ", " .
        showString "cliques: " . shows (cliques eg) .
        showString "}"
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


