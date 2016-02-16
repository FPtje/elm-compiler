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

import Control.Monad (filterM)

siblingSolvesError :: T.TypeConstraint -> BS.EdgeId -> TG.TypeGraph T.TypeConstraint -> Module.Sibling -> TS.Solver Bool
siblingSolvesError constr eid@(BS.EdgeId _ r _) grph sib =
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

        (_, vidl, grphl) <- TG.addTermGraph (TG.uniqueVertexId removedEdge) freshCopy Nothing removedEdge
        let updatedGrph = TG.addNewEdge (vidl, r) constr grphl

        let grphErrs = TG.getErrors updatedGrph


        return $ null grphErrs



searchSiblings :: Module.Siblings -> Module.Sibling -> BS.VertexId -> TG.TypeGraph T.TypeConstraint -> TS.Solver (S.Set (Module.Sibling, Module.Sibling))
searchSiblings sbs funcName vid grph =
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

        siblings :: S.Set Module.Sibling
        siblings = M.findWithDefault S.empty funcName sbs

        sibConstraints :: [(Module.Sibling, BS.EdgeId, T.TypeConstraint)] -- (T.CInstance rg name _)
        sibConstraints = [(sib, eid, constr) | sib <- S.toList siblings, (eid, constr) <- cInstanceEdges]

        sibFits :: (Module.Sibling, BS.EdgeId, T.TypeConstraint) -> TS.Solver Bool
        sibFits (sib, eid, constr) = siblingSolvesError constr eid grph sib

        workingSiblings :: TS.Solver [(Module.Sibling, BS.EdgeId, T.TypeConstraint)]
        workingSiblings = filterM sibFits sibConstraints

        fst3 :: (a, b, c) -> a
        fst3 (a, _, _) = a
    in
        do
            workingSibs <- workingSiblings
            return . S.fromList . map ((,) funcName . fst3) $ workingSibs


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
investigateSiblings sbs (P.Step eid@(BS.EdgeId l r _) (P.Initial constr)) grph =
    -- An initial edge in the error path mentions a function
    -- Check whether there is a sibling of that function
    -- then check whether that function applies.
    case constr of
        T.CEqual (Error.BinopLeft v _) _ _ _ ->
            do
                leftSibs <- searchSiblings sbs v l grph
                rightSibs <- searchSiblings sbs v r grph
                return $ leftSibs `S.union` rightSibs
        T.CEqual (Error.BinopRight v _) _ _ _ ->
            do
                leftSibs <- searchSiblings sbs v l grph
                rightSibs <- searchSiblings sbs v r grph
                return $ leftSibs `S.union` rightSibs
        T.CEqual (Error.UnexpectedArg (Just v) _ _ _) _ _ _ ->
            do
                leftSibs <- searchSiblings sbs v l grph
                rightSibs <- searchSiblings sbs v r grph
                return $ leftSibs `S.union` rightSibs
        T.CEqual (Error.FunctionArity (Just v) _ _ _) _ _ _ ->
            do
                leftSibs <- searchSiblings sbs v l grph
                rightSibs <- searchSiblings sbs v r grph
                return $ leftSibs `S.union` rightSibs
        T.CEqual (Error.Function (Just v)) _ _ _ ->
            do
                leftSibs <- searchSiblings sbs v l grph
                rightSibs <- searchSiblings sbs v r grph
                return $ leftSibs `S.union` rightSibs
        --T.CInstance _ funcName _ ->
        --    do
        --        let sibList = S.toList (M.findWithDefault S.empty funcName sbs)
        --        solvingSibs <- filterM (siblingSolvesError constr eid grph) sibList
        --        return . S.fromList . map ((,) funcName) $ solvingSibs
        _ -> return S.empty
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
