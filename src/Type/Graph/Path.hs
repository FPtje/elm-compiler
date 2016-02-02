{-# OPTIONS_GHC -Wall #-}

module Type.Graph.Path where

import qualified Type.Graph.Basics as BS
import qualified Type.Graph.Clique as CLQ

-- | Describes the path of constraints between two equal (sub) types
data Path info =
      Path info :|: Path info
    | Path info :+: Path info
    | Step BS.EdgeId (Step info)
    | Fail
    | Empty

-- | Describes one step in a path
data Step info =
      Initial info
    | Implied CLQ.ChildSide BS.VertexId BS.VertexId
    | Child CLQ.ChildSide

-- | Combine lists of paths into a single path object
-- altList and altList1 in Top
concatPath, concatPath1 :: [Path a] -> Path a
concatPath  = foldr  (:|:) Fail
concatPath1 = foldr1 (:|:)
