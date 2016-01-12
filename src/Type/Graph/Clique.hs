{-# OPTIONS_GHC -Wall #-}

module Type.Graph.Clique where

import qualified Type.Graph.Basics as BS
import Data.List (partition)

-- | Indicates whether a child is the left or right child of a parent
data ChildSide =
      LeftChild
    | RightChild
    deriving (Eq, Show)

-- | Describes the parent-child relationship
-- Used in composite types (functions, data structures, etc.)
data ParentChild = ParentChild
    { parent                    :: BS.VertexId                  -- ^ Vertex id of the parent
    , child                     :: BS.VertexId                  -- ^ Vertex id of the child
    , childSide                 :: ChildSide                    -- ^ On which side the child resides
    }
   deriving (Eq, Show)

instance Ord ParentChild where
   compare pc1 pc2 = compare (child pc1, parent pc1) (child pc2, parent pc2)

-- | A clique is a set of vertices that are equivalent because their parents are equal
-- See page 124 of Heeren's thesis
-- Invariant: a clique cannot be empty
-- Invariant: The ParentChild list is always sorted
newtype Clique =
    Clique { unclique :: [ParentChild] }
    deriving (Eq, Ord, Show)


children :: Clique -> [BS.VertexId]
children = map child . unclique

-- | Returns true when the first clique is a subset of the second
isSubsetClique :: Clique -> Clique -> Bool
isSubsetClique (Clique as) (Clique bs) =
    let
        op [] _ = True
        op _ [] = False
        op a@(x:xs) (y:ys)
            | x == y    = op xs ys
            | x > y     = op a ys
            | otherwise = False
    in
        op as bs

-- | Returns true when two cliques do NOT refer to the same implicit relationship
isDisjoint :: Clique -> Clique -> Bool
isDisjoint (Clique as) (Clique bs) =
    let
        op [] _ = True
        op _ [] = True
        op a@(x:xs) b@(y:ys)
            | x == y    = False
            | x > y     = op a ys
            | otherwise = op xs b
    in
        op as bs

-- | Merges a list of cliques into a single clique
-- Implies that all cliques refer to the same implicit relationship
merge :: [Clique] -> Clique
merge list = Clique (foldr op [] [ xs | Clique xs <- list ])
 where
    op xs [] = xs
    op [] ys = ys
    op a@(x:xs) b@(y:ys)
        | x < y     = x : op xs b
        | x == y    = x : op xs ys
        | otherwise = y : op a ys

-- | Combine two lists of cliques
combine :: [Clique] -> [Clique] -> [Clique]
combine [] ys = ys
combine (x:xs) ys =
    let
        (disjoint, overlapping) = partition (isDisjoint x) ys
    in
        merge (x : overlapping) : combine xs disjoint
