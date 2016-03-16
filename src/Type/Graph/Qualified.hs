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
