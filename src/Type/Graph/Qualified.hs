-- | Qualified types (ad hoc polymorphism) in type graphs
module Type.Graph.Qualified where

import qualified Type.Type as T

data Predicate =
    Super T.Super -- To add later: record member, type classes, whatever
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
