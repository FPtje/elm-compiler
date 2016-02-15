module Type.Graph.Siblings where

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
    .  addSymmSib "Basics.fst" "Basics.snd"
    .  addSymmSib "Basics.>>" "Basics.<<"
    .  addSymmSib "Basics.curry" "Basics.uncurry"
    .  addSymmSib "Basics.sqrt" "Basics.not"
    . addSibling "Date.fromString" "Basics.not"
    $ emptySiblings

siblingSolvesError :: T.TypeConstraint -> BS.EdgeId -> TG.TypeGraph T.TypeConstraint -> Sibling -> TS.Solver Bool
siblingSolvesError constr eid@(BS.EdgeId _ r _) grph sib =
    do
        let removedEdge = TG.deleteEdge eid grph

        env <- TS.getEnv
        freshCopy <-
            case M.lookup sib env of
              Just (A.A _ tipe) ->
                  TS.makeInstance tipe

              Nothing ->
                  error ("Could not find `" ++ sib ++ "` when trying out siblings.")

        (_, vidl, grphl) <- TG.addTermGraph (TG.uniqueVertexId removedEdge) freshCopy Nothing removedEdge
        let updatedGrph = TG.addNewEdge (vidl, r) constr grphl

        let grphErrs = TG.getErrors updatedGrph


        return $ null grphErrs



searchSiblings :: Siblings -> Sibling -> BS.VertexId -> TG.TypeGraph T.TypeConstraint -> TS.Solver (S.Set Sibling)
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

        siblings :: S.Set Sibling
        siblings = M.findWithDefault S.empty funcName sbs

        sibConstraints :: [(Sibling, BS.EdgeId, T.TypeConstraint)] -- (T.CInstance rg name _)
        sibConstraints = [(sib, eid, constr) | sib <- S.toList siblings, (eid, constr) <- cInstanceEdges]

        sibFits :: (Sibling, BS.EdgeId, T.TypeConstraint) -> TS.Solver Bool
        sibFits (sib, eid, constr) = siblingSolvesError constr eid grph sib

        workingSiblings :: TS.Solver [(Sibling, BS.EdgeId, T.TypeConstraint)]
        workingSiblings = filterM sibFits sibConstraints

        fst3 :: (a, b, c) -> a
        fst3 (a, _, _) = a
    in
        do
            workingSibs <- workingSiblings
            return . S.fromList . map fst3 $ workingSibs


-- | Gives a set of siblings that would resolve the type error
suggestSiblings :: Siblings -> P.Path T.TypeConstraint -> TG.TypeGraph T.TypeConstraint -> TS.Solver (S.Set Sibling)
suggestSiblings sbs (l P.:|: r) grph =
    do
        lsibs <- suggestSiblings sbs l grph
        rsibs <- suggestSiblings sbs r grph
        return $ lsibs `S.union` rsibs
suggestSiblings sbs (l P.:+: r) grph =
    do
        lsibs <- suggestSiblings sbs l grph
        rsibs <- suggestSiblings sbs r grph
        return $ lsibs `S.union` rsibs
suggestSiblings sbs (P.Step eid@(BS.EdgeId l r _) (P.Initial constr)) grph =
    -- An initial edge in the error path mentions a function
    -- Check whether there is a sibling of that function
    -- then check whether that function applies.
    case constr of
        T.CEqual (Error.BinopLeft v _) _ _ _ ->
            do
                leftSibs <- searchSiblings sbs (V.toString v) l grph
                rightSibs <- searchSiblings sbs (V.toString v) r grph
                return $ leftSibs `S.union` rightSibs
        T.CEqual (Error.BinopRight v _) _ _ _ ->
            do
                leftSibs <- searchSiblings sbs (V.toString v) l grph
                rightSibs <- searchSiblings sbs (V.toString v) r grph
                return $ leftSibs `S.union` rightSibs
        T.CEqual (Error.UnexpectedArg (Just v) _ _ _) _ _ _ ->
            do
                leftSibs <- searchSiblings sbs (V.toString v) l grph
                rightSibs <- searchSiblings sbs (V.toString v) r grph
                return $ leftSibs `S.union` rightSibs
        T.CEqual (Error.FunctionArity (Just v) _ _ _) _ _ _ ->
            do
                leftSibs <- searchSiblings sbs (V.toString v) l grph
                rightSibs <- searchSiblings sbs (V.toString v) r grph
                return $ leftSibs `S.union` rightSibs
        T.CInstance _ funcName _ ->
            do
                let sibList = S.toList (M.findWithDefault S.empty funcName sbs)
                solvingSibs <- filterM (siblingSolvesError constr eid grph) sibList
                return $ S.fromList solvingSibs
        _ -> return S.empty
suggestSiblings _ _ _ = return S.empty
