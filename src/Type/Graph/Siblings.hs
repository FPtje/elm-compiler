module Type.Graph.Siblings where

import qualified AST.Module as Module
import qualified Type.Type as T
import qualified Type.Graph.TypeGraph as TG
import qualified Type.Graph.EQGroup as EG
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


        return $ null grphErrs



searchSiblings :: Module.Siblings -> BS.VertexId -> TG.TypeGraph T.TypeConstraint -> TS.Solver (S.Set (Module.Sibling, Module.Sibling))
searchSiblings sbs vid grph =
    let
        root :: BS.VertexId
        root = TG.findRoot vid grph

        rootEdges :: [(BS.EdgeId, T.TypeConstraint)]
        rootEdges = EG.edges . TG.getVertexGroup root $ grph

        isCInstance :: (BS.EdgeId, T.TypeConstraint) -> Bool
        isCInstance (_, T.CInstance {}) = True
        isCInstance _ = False

        cInstanceEdges :: [(BS.EdgeId, T.TypeConstraint)]
        cInstanceEdges = filter isCInstance rootEdges

        cInstanceNames :: [(BS.EdgeId, Module.Sibling, T.TypeConstraint)]
        cInstanceNames =
            [ (eid, fromJust var, c)
            | (eid, c@(T.CInstance _ name _ _)) <- cInstanceEdges
            ,  let var = M.lookup name (TG.funcMap grph)
            , isJust var
            ]

        siblings :: Module.Sibling -> S.Set Module.Sibling
        siblings var = M.findWithDefault S.empty var (snd sbs)

        sibConstraints :: [(Module.Sibling, Module.Sibling, BS.EdgeId, T.TypeConstraint)] -- (T.CInstance rg name _)
        sibConstraints = [(var, sib, eid, constr) | (eid, var, constr) <- cInstanceNames, sib <- S.toList (siblings var)]

        sibFits :: (Module.Sibling, Module.Sibling, BS.EdgeId, T.TypeConstraint) -> TS.Solver Bool
        sibFits (_, sib, eid, constr) = siblingSolvesError constr eid grph sib

        workingSiblings :: TS.Solver [(Module.Sibling, Module.Sibling, BS.EdgeId, T.TypeConstraint)]
        workingSiblings = filterM sibFits sibConstraints

        fst2 :: (a, b, c, d) -> (a, b)
        fst2 (a, b, _, _) = (a, b)
    in
        do
            workingSibs <- workingSiblings
            return . S.fromList . map fst2 $ workingSibs


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
investigateSiblings sbs (P.Step (BS.EdgeId l r) _) grph =
    do
        leftSibs <- searchSiblings sbs l grph
        rightSibs <- searchSiblings sbs r grph
        return $ leftSibs `S.union` rightSibs
investigateSiblings _ _ _ = return S.empty


addHintToError :: [A.Located Error.Error] -> [(Module.Sibling, Module.Sibling)] -> [A.Located Error.Error]
addHintToError [] _ = []
addHintToError ((A.A rg (Error.Mismatch mism)) : xs) sibs =
    A.A rg (Error.Mismatch mism { Error._siblings = sibs }) : addHintToError xs sibs
addHintToError (x : xs) sibs = x : addHintToError xs sibs

-- | Add sibling suggestions to the errors that have been thrown by the original unify algorithm
addSiblingSuggestions :: S.Set (Module.Sibling, Module.Sibling) -> TS.Solver ()
addSiblingSuggestions sibs =
    do
        let sibList = S.toList sibs

        errs <- TS.getError
        tgErrs <- TS.getTypeGraphErrors
        let (otherErrs, neededErrs) = splitAt tgErrs errs

        TS.setError $ otherErrs ++ (addHintToError neededErrs sibList)

        return ()
