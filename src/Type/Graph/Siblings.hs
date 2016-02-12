module Type.Graph.Siblings where

import qualified Type.Graph.TypeGraph as TG
import qualified Type.Graph.Path as P
import qualified Data.Map as M
import qualified Data.Set as S

type Sibling = String
type Siblings = M.Map Sibling (S.Set Sibling)

-- | Adds a sibling
-- Note: Asymmetrical, the first function will be a sibling
-- of the second one
addSibling :: Sibling -> Sibling -> Siblings -> Siblings
addSibling sibl siblOf mp =
    M.insert siblOf (sibl `S.insert` M.findWithDefault S.empty siblOf mp) mp

-- | Add a sibling symmetrically
addSymmSib :: Sibling -> Sibling -> Siblings -> Siblings
addSymmSib l r =
      addSibling l r
    . addSibling r l


emptySiblings :: Siblings
emptySiblings = M.empty

-- Testing siblings
defaultSiblings :: Siblings
defaultSiblings =
      addSymmSib "Basics.|>" "Basics.<|"
    .  addSibling "Debug.crash" "Basics.not"
    . addSibling "Date.fromString" "Basics.not"
    $ emptySiblings


