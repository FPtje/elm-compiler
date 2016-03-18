{-# OPTIONS_GHC -Wall #-}

module Type.Graph.Clique where

import qualified Type.Graph.Basics as BS
import Control.Applicative ((<|>))
import Data.List (partition, sort, find)
import Data.Maybe (catMaybes, listToMaybe)

import Debug.Trace

-- | Indicates whether a child is the left or right child of a parent
data ChildSide =
      LeftChild
    | RightChild
    deriving (Eq)

instance Show ChildSide where
    show LeftChild = "L"
    show RightChild = "R"

-- | Describes the parent-child relationship
-- Used in composite types (functions, data structures, etc.)
data ParentChild = ParentChild
    { parent                    :: BS.VertexId                  -- ^ Vertex id of the parent
    , child                     :: BS.VertexId                  -- ^ Vertex id of the child
    , childSide                 :: ChildSide                    -- ^ On which side the child resides
    }
   deriving (Eq)

instance Show ParentChild where
    show pc = show (BS.unVertexId . parent $ pc) ++ show (childSide pc) ++ show (BS.unVertexId . child $ pc)

instance Ord ParentChild where
   compare pc1 pc2 = compare (child pc1, parent pc1) (child pc2, parent pc2)

-- | A clique is a set of vertices that are equivalent because their parents are equal
-- See page 124 of Heeren's thesis
-- Invariant: a clique cannot be empty
-- Invariant: The ParentChild list is always sorted
newtype Clique =
    Clique { unclique :: [ParentChild] }
    deriving (Eq, Ord, Show)


-- | Make a Clique from ParentChild values
makeClique :: [ParentChild] -> Clique
makeClique list
   | length set < 2 = error "makeClique: incorrect clique"
   | otherwise      = Clique set
 where
   set = sort list

children :: Clique -> [BS.VertexId]
children = map child . unclique

-- | The representative VertexId of a clique
representative :: Clique -> BS.VertexId
representative (Clique xs) =
   case xs of
      []  -> error "cliqueRepresentative: A clique cannot be empty"
      x:_ -> child x

-- | Get the parent of a vertex that lives in this clique
getParent :: BS.VertexId -> Clique -> Maybe BS.VertexId
getParent v clq = getParentChild v clq >>= return . parent

-- | Get the clique in which this
getParentChild :: BS.VertexId -> Clique -> Maybe ParentChild
getParentChild v (Clique pcs) = find (\pc -> child pc == v) pcs


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

-- | Try to find a parent implicit edge from a given implicit edge
edgeParentSingle :: BS.EdgeId -> Clique -> Maybe (BS.EdgeId, ChildSide)
edgeParentSingle (BS.EdgeId l r) clq = do
    lpc <- getParentChild l clq
    rpc <- getParentChild r clq
    return (BS.EdgeId (parent lpc) (parent rpc), childSide rpc)

-- | Try to find a parent implicit edge from a given implicit edge
edgeParent :: BS.EdgeId -> [Clique] -> Maybe (BS.EdgeId, ChildSide)
edgeParent eid = foldl1 (<|>) . map (edgeParentSingle eid)


-- | Returns the clique of a vertex
cliqueOf :: BS.VertexId -> [Clique] -> Maybe Clique
cliqueOf _ [] = Nothing
cliqueOf vid (c : cqs) =
    case getParentChild vid c of
        Just _ -> Just c
        Nothing -> cliqueOf vid cqs

-- | For two vertices a and b, this function gives all the vertices that both a and b have in the same clique
commonInClique :: BS.VertexId -> BS.VertexId -> [Clique] -> [BS.VertexId]
commonInClique a b clqs =
    case (cliqueOf a clqs, cliqueOf b clqs) of
        (Just aClq, Just bClq) ->
            [ child aPc
            | aPc <- unclique aClq
            , bPc <- unclique bClq
            , child aPc /= a
            , child bPc /= b
            , child aPc == child bPc
            ]
        _ -> []

