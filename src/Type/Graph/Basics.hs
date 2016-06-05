{-# OPTIONS_GHC -Wall #-}

module Type.Graph.Basics where

import qualified AST.Variable as Var
import qualified Type.Type as T
import qualified Data.Map as M
import Type.Unify (ExtensionStructure (..))

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
      VVar T.Flex [Predicate]                                   -- ^ Type variable
    | VCon String [Evidence]                                    -- ^ Type constructor
    | VApp VertexId VertexId                                    -- ^ Type application
    deriving (Show)

-- Ignore predicates in VCons
instance Eq VertexKind where
    (VVar fl l) == (VVar fr r) = l == r && fl == fr
    (VCon l _) == (VCon r _) = l == r
    (VApp l r) == (VApp l' r') = l == l' && r == r'
    _ == _ = False

instance Ord VertexKind where
    compare (VVar fl l) (VVar fr r) =
        case compare fl fr of
            EQ -> compare l r
            x -> x
    compare (VCon l _) (VCon r _) = compare l r
    compare (VApp l r) (VApp l' r') =
        case compare l l' of
            EQ -> compare r r'
            x -> x
    compare (VVar _ _) (VCon _ _) = LT
    compare (VCon _ _) (VVar _ _) = GT
    compare (VVar _ _) (VApp _ _) = LT
    compare (VApp _ _) (VVar _ _) = GT
    compare (VCon _ _) (VApp _ _) = LT
    compare (VApp _ _) (VCon _ _) = LT

-- | Identifies an edge in the type graph
data EdgeId = EdgeId VertexId VertexId
    deriving (Eq, Ord, Show)

undirected :: EdgeId -> EdgeId
undirected (EdgeId l r)
    | l < r = EdgeId l r
    | otherwise = EdgeId r l


-- Qualified types
data Predicate =
      Super T.Super
    | RecordMembers ExtensionStructure (M.Map String VertexId)
    | PInterface Var.Canonical (Maybe String)
    deriving (Eq, Ord, Show)

type Evidence = Predicate

isEvidence :: Predicate -> Evidence -> Bool
isEvidence (Super l) (Super r) = l == r
isEvidence _ _ = True


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

-- | Checks for matching evidence between constructors
-- Currently only applies to records
matchConsEvidence :: Evidence -> Evidence -> Bool
matchConsEvidence (RecordMembers str1 mp1) (RecordMembers str2 mp2) =
    let
        sameKeysL :: Bool
        sameKeysL = M.null (M.difference mp1 mp2)

        -- elements of the right map not appearing in the left
        sameKeysR :: Bool
        sameKeysR = M.null (M.difference mp2 mp1)

        anus a b = trace (a ++ show b) b
    in
        -- If the left record contains things that the right record doesn't
        -- AND the right record is not polymorphic in extra members
        -- OR otherwise, it's false.
        case (sameKeysL, sameKeysR, str1, str2) of
            (False, _, _, Empty) -> False
            (_, False, Empty, _) -> False
            _ -> True
