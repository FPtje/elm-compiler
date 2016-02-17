module Type.Graph.Heuristics where

import qualified Type.State as TS
import qualified Type.Graph.TypeGraph as TG
import qualified Type.Graph.Siblings as SB
import qualified Data.Set as S
import qualified Type.Type as T


applyHeuristics :: TG.TypeGraph T.TypeConstraint -> TS.Solver ()
applyHeuristics grph =
    do
        let grphErrs = TG.getErrors grph
        let inconsistentPaths = concatMap TG.inconsistentTypesPaths grphErrs

        sbs <- TS.getSiblings
        sibSuggestions <- mapM (\ip -> SB.investigateSiblings sbs ip grph) inconsistentPaths

        SB.addSiblingSuggestions . S.unions $ sibSuggestions
