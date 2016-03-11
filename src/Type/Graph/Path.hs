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
    deriving (Eq, Show)

-- | Describes one step in a path
data Step info =
      Initial info
    | Implied
    | Child CLQ.ChildSide
    | Parent CLQ.ChildSide
    deriving (Eq, Show)



-- | Combine lists of paths into a single path object
-- altList and altList1 in Top
choice, choice1 :: [Path a] -> Path a
choice  = foldr  (:|:) Fail
choice1 = foldr1 (:|:)

-- | Simplifies a path
-- called simplifyPath in TOP
simplify :: Path a -> Path a
simplify path =
    case path of
        x :|: y ->
            case (simplify x, simplify y) of
                (Empty, _    ) -> Empty
                (_    , Empty) -> Empty
                (Fail , p2   ) -> p2
                (p1   , Fail ) -> p1
                (p1   , p2   ) -> p1 :|: p2
        x :+: y ->
            case (simplify x, simplify y) of
                (Fail , _    ) -> Fail
                (_    , Fail ) -> Fail
                (Empty, p1   ) -> p1
                (p2   , Empty) -> p2
                (p1   , p2   ) -> p1 :+: p2
        _ -> path

contains :: Eq info => info -> Path info -> Bool
contains info (l :|: r) = contains info l && contains info r
contains info (l :+: r) = contains info l || contains info r
contains info (Step _ (Initial info')) = info == info'
contains _ _ = False
