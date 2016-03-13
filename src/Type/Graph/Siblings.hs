module Type.Graph.Siblings where

import qualified AST.Module as Module
import qualified Type.Type as T
import qualified Type.Graph.TypeGraph as TG
import qualified Type.Graph.Basics as BS
import qualified Type.Graph.Path as P
import qualified Type.State as TS
import qualified Reporting.Annotation as A
import qualified Reporting.Error.Type as Error
import qualified AST.Variable as V
import qualified Data.Map as M
import qualified Data.Set as S

import Data.Maybe (isJust, fromJust)

import Control.Monad (filterM)

siblingSolvesError :: T.TypeConstraint -> BS.EdgeId -> TG.TypeGraph T.TypeConstraint -> Module.Sibling -> TS.Solver Bool
siblingSolvesError constr eid@(BS.EdgeId _ r) grph sib =
    do
        let removedEdge = TG.deleteEdge eid grph
        let sibName = V.toString sib

        env <- TS.getEnv
        freshCopy <-
            case M.lookup sibName env of
              Just (A.A _ tipe) ->
                  TS.makeInstance tipe

              Nothing ->
                  error ("Could not find `" ++ sibName ++ "` when trying out siblings.")

        (vidl, grphl) <- TG.addTermGraph freshCopy Nothing removedEdge
        let updatedGrph = TG.addNewEdge (vidl, r) constr grphl

        let grphErrs = TG.getErrors updatedGrph
        let inconsistentPaths = concatMap TG.inconsistentTypesPaths grphErrs
        let expandedPaths = map (TG.expandPath updatedGrph) inconsistentPaths
        -- This sibling does NOT solve the error if its CInstance
        -- constraint remains present in any of the expanded error paths
        let constrPresent = or . map (P.contains eid) $ expandedPaths

        return . not $ constrPresent

checkForSibling :: Module.Siblings -> BS.EdgeId -> T.TypeConstraint -> TG.TypeGraph T.TypeConstraint -> TS.Solver (S.Set (Module.Sibling, Module.Sibling))
checkForSibling sbs eid constr@(T.CInstance _ name _ _) grph =
    let
        varM :: Maybe V.Canonical
        varM = M.lookup name . TG.funcMap $ grph

        var :: V.Canonical
        var = fromJust varM

        siblings :: [Module.Sibling]
        siblings = S.toList $ M.findWithDefault S.empty var (snd sbs)

        workingSiblings :: TS.Solver [Module.Sibling]
        workingSiblings = filterM (siblingSolvesError constr eid grph) siblings
    in
        if isJust varM then
            workingSiblings >>= return . S.fromList . zip (repeat var)
        else
            return S.empty

checkForSibling _ _ _ _ = return S.empty


-- | Gives a set of siblings that would resolve the type error
investigateSiblings :: Module.Siblings -> P.Path T.TypeConstraint -> TG.TypeGraph T.TypeConstraint -> TS.Solver (S.Set (Module.Sibling, Module.Sibling))
investigateSiblings sbs (l P.:|: r) grph =
    do
        lsibs <- investigateSiblings sbs l grph
        rsibs <- investigateSiblings sbs r grph
        return $ lsibs `S.union` rsibs
investigateSiblings sbs (l P.:+: r) grph =
    do
        lsibs <- investigateSiblings sbs l grph
        rsibs <- investigateSiblings sbs r grph
        return $ lsibs `S.union` rsibs
investigateSiblings sbs (P.Step eid (P.Initial constr@(T.CInstance {}))) grph =
    checkForSibling sbs eid constr grph
investigateSiblings _ _ _ = return S.empty


addHintToError :: [(Module.Sibling, Module.Sibling)] -> Error.Error -> Error.Error
addHintToError sibs (Error.Mismatch mism) = Error.Mismatch mism { Error._siblings = sibs }
addHintToError _ x = x

addHintToErrors :: [A.Located Error.Error] -> [(Module.Sibling, Module.Sibling)] -> [A.Located Error.Error]
addHintToErrors [] _ = []
addHintToErrors ((A.A rg err) : xs) sibs = A.A rg (addHintToError sibs err) : addHintToErrors xs sibs
addHintToErrors (x : xs) sibs = x : addHintToErrors xs sibs
