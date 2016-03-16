-- | Qualified types (ad hoc polymorphism) in type graphs
module Type.Graph.Qualified where

import qualified Type.Type as T

data Predicate =
    Super T.Super -- To add later: record member, type classes, whatever
    deriving (Eq, Ord, Show)

type Evidence = Predicate
