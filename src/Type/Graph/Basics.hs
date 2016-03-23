{-# OPTIONS_GHC -Wall #-}

module Type.Graph.Basics where

import qualified AST.Variable as Var
import qualified Type.Type as T
import qualified Data.Map as M

-- | Identifies vertices in the type graph
newtype VertexId =
    VertexId Int
    deriving (Eq, Ord, Show)

unVertexId :: VertexId -> Int
unVertexId (VertexId i) = i

type VertexInfo = (VertexKind, Maybe Var.Canonical)

-- | The types that a vertex can contain
-- A simplification of the actual types
data VertexKind =
      VVar [Predicate]                                          -- ^ Type variable
    | VCon String [Evidence]                                    -- ^ Type constructor
    | VApp VertexId VertexId                                    -- ^ Type application
    deriving (Eq, Ord, Show)

-- | Identifies an edge in the type graph
data EdgeId = EdgeId VertexId VertexId
    deriving (Eq, Ord, Show)

undirected :: EdgeId -> EdgeId
undirected (EdgeId l r)
    | l < r = EdgeId l r
    | otherwise = EdgeId r l


-- Qualified types
data Predicate =
      Super T.Super -- To add later: type classes, whatever
    | RecordMembers (M.Map String VertexId)
    deriving (Eq, Ord, Show)

type Evidence = Predicate

isEvidence :: Predicate -> Evidence -> Bool
isEvidence (Super l) (Super r) = l == r


-- | Returns predicates unsatisfied by evidence
matchEvidence :: [Predicate] -> [Evidence] -> [Predicate]
matchEvidence (p : ps) es =
    if any (isEvidence p) es then
        matchEvidence ps es
    else
        p : (matchEvidence ps es)
matchEvidence [] _ = []

-- | Checks whether sets of predicates are consistent with one another
-- returns the inconsistent pairs by their identification
-- Doesn't check internal consistency
consistent :: [(a, [Predicate])] -> [(a, a)]
consistent ps =
    let
        -- Currently the only inconsistency can come from
        -- the super class of one thing being number, and
        -- that of another thing being Appendable
        numbers = [a | (a, pr) <- ps, Super T.Number `elem` pr]
        appendables = [a | (a, pr) <- ps, Super T.Appendable `elem` pr]
    in
        [(n, ap) | n <- numbers, ap <- appendables]
