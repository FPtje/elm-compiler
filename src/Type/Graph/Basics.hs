{-# OPTIONS_GHC -Wall #-}

module Type.Graph.Basics where

import qualified AST.Variable as Var

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
      VVar                                                      -- ^ Type variable
    | VCon String                                               -- ^ Type constructor
    | VApp VertexId VertexId                                    -- ^ Type application
    deriving (Eq, Ord, Show)

-- | Identifies an edge in the type graph
data EdgeId = EdgeId VertexId VertexId
    deriving (Eq, Show)
