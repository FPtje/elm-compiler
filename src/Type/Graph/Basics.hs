{-# OPTIONS_GHC -Wall #-}

module Type.Graph.Basics where

import qualified AST.Variable as Var
import qualified Type.Graph.Qualified as Q

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
      VVar [Q.Predicate]                                        -- ^ Type variable
    | VCon String [Q.Evidence]                                  -- ^ Type constructor
    | VApp VertexId VertexId                                    -- ^ Type application
    deriving (Eq, Ord, Show)

-- | Identifies an edge in the type graph
data EdgeId = EdgeId VertexId VertexId
    deriving (Eq, Ord, Show)

undirected :: EdgeId -> EdgeId
undirected (EdgeId l r)
    | l < r = EdgeId l r
    | otherwise = EdgeId r l
