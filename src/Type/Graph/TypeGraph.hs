{-# OPTIONS_GHC -Wall #-}

module Type.Graph.TypeGraph where

import qualified Type.Graph.Basics as BS
import qualified Type.Graph.EQGroup as EG
import qualified Type.Graph.Clique as CLQ
import qualified AST.Variable as Var
import qualified Type.Type as T
import qualified Type.State as TS
import qualified Data.Map as M
import qualified Data.UnionFind.IO as UF
import qualified Data.List as List
import qualified Reporting.Annotation as A
import Control.Monad.State (liftIO)
import Data.List (nub)

import Data.Maybe (fromMaybe, maybeToList, isJust)


-- | Representation of a type graph
data TypeGraph info = TypeGraph
   { referenceMap               :: M.Map BS.VertexId Int{- group number -}
   , equivalenceGroupMap        :: M.Map Int (EG.EquivalenceGroup info)
   , equivalenceGroupCounter    :: Int
   , possibleErrors             :: [BS.VertexId]
   , constraintNumber           :: Int
   , varNumber                  :: Int
   }
   deriving (Show)

-- | Empty type graph
empty :: TypeGraph info
empty = TypeGraph
    { referenceMap            = M.empty
    , equivalenceGroupMap     = M.empty
    , equivalenceGroupCounter = 0
    , possibleErrors          = []
    , constraintNumber        = 0
    , varNumber               = 0
    }

-- | Adds the given vertex to the list of possible errors.
addPossibleInconsistentGroup :: BS.VertexId -> TypeGraph info -> TypeGraph info
addPossibleInconsistentGroup vid stg = stg { possibleErrors = vid : possibleErrors stg }

-- | All VertexIds that are in the given vertex' group.
-- Includes the given vertex
verticesInGroupOf :: BS.VertexId -> TypeGraph info -> [(BS.VertexId, BS.VertexInfo)]
verticesInGroupOf i =
      EG.vertices . fromMaybe (error $ "verticesInGroupOf: vertexId does not exist: " ++ show i) . getGroupOf i


-- | The representative of the equivalence group in which the given VertexId resides
representativeInGroupOf :: BS.VertexId -> TypeGraph info -> BS.VertexId
representativeInGroupOf i graph =
      case verticesInGroupOf i graph of
         (vid, _):_ -> vid
         _ -> error "representativeInGroupOf: unexpected empty equivalence group"

-- | In Top: combineClasses
--  Alters the typegraph in such way that all the vertices given in the
-- first parameter become members of the same equivalence group.
combineEQGroups :: [BS.VertexId] -> TypeGraph info -> TypeGraph info
combineEQGroups is grph =
    case nub (map (`representativeInGroupOf` grph) is) of
        list@(i:_:_) ->
            let
                eqgroups = map (fromMaybe (error "combineEQGroups: Unexpected non-existing VertexId") . flip getGroupOf grph) list
                newGroup = foldr EG.combine EG.empty eqgroups
            in
                addPossibleInconsistentGroup i . createGroup newGroup . foldr removeGroup grph $ eqgroups
        _ -> grph

-- | Add an equivalence group to the type graph
createGroup :: EG.EquivalenceGroup info -> TypeGraph info -> TypeGraph info
createGroup grp grph =
    let
        newGroupNumber = equivalenceGroupCounter grph
        list = [(i, newGroupNumber) | (i, _) <- EG.vertices grp]
    in
        if null list then
            error "cannot create an empty equivalence group"
        else
            grph
                { referenceMap             = referenceMap grph `M.union` M.fromList list
                , equivalenceGroupMap      = M.insert newGroupNumber grp (equivalenceGroupMap grph)
                , equivalenceGroupCounter  = newGroupNumber + 1
                }

-- | Removes an equivalence group from a type graph
removeGroup :: EG.EquivalenceGroup info -> TypeGraph info -> TypeGraph info
removeGroup eqgroup grph =
    let
        vertexIds   = map fst (EG.vertices eqgroup)
        oldGroupNr  = maybeToList (M.lookup (head vertexIds) (referenceMap grph))
    in
        grph
            { referenceMap        = foldr M.delete (referenceMap grph) vertexIds
            , equivalenceGroupMap = foldr M.delete (equivalenceGroupMap grph) oldGroupNr
            }

-- | Creates a type graph from a single group
fromGroup :: EG.EquivalenceGroup info -> TypeGraph info
fromGroup = flip createGroup empty

-- | Gets the equivalence group that contains the given VertexId
getGroupOf :: BS.VertexId -> TypeGraph info -> Maybe (EG.EquivalenceGroup info)
getGroupOf vid grph =
    do
        eqnr <- M.lookup vid (referenceMap grph)
        M.lookup eqnr (equivalenceGroupMap grph)

-- | Updates the equivalence group that contains a given VertexId
-- Throws error when the VertexId doesn't exist
updateGroupOf :: BS.VertexId -> (EG.EquivalenceGroup info -> EG.EquivalenceGroup info) -> TypeGraph info -> TypeGraph info
updateGroupOf vid f grph =
    let
        eqgrp = getGroupOf vid grph
        err  = error ("error in lookup map: " ++ show vid)
        eqnr = M.findWithDefault err vid (referenceMap grph)
    in
        grph { equivalenceGroupMap = M.insert eqnr (f (fromMaybe err eqgrp)) (equivalenceGroupMap grph) }

-- | In Top: splitClass
-- Splits the equivalence groups in the type graph
-- Used when propagating the removal of edges.
-- returns the representative VertexIds and the altered type graph
splitEQGroups ::  BS.VertexId -> TypeGraph info -> ([BS.VertexId], TypeGraph info)
splitEQGroups vid grph =
    let
        eqgroup   = fromMaybe (error "splitEQGroups: non-existing VertexId") $ getGroupOf vid grph
        newGroups = EG.split eqgroup
        results   = [ vid2 | (vid2, _):_ <- map EG.vertices newGroups ]
        newGraph
            | length newGroups > 1 = foldr createGroup (removeGroup eqgroup grph) newGroups
            | otherwise = grph
    in
        (results, newGraph)


addTermGraph :: Int -> T.Variable -> Maybe Var.Canonical -> TypeGraph info -> TS.Solver (Int, BS.VertexId, TypeGraph info)
addTermGraph unique var alias grph = do
    desc <- liftIO $ UF.descriptor var
    let content = T._content desc
    let mark = T._mark desc

    case content of
        T.Structure t -> addTermGraphStructure unique t alias grph
        T.Atom name ->
            do -- Add con here
                let vid = BS.VertexId unique
                return (unique + 1, vid, addVertex vid (BS.VCon (Var.toString name), alias) grph)

        T.Var flex msuper mname -> do -- TODO: check mark for duplicate/zeroes/-1 values
            --let idf = varNumber grph
            let vid = BS.VertexId mark
            --let updGrph = grph {
            --    varNumber = mark + 1
            --}
            return (unique, vid, if vertexExists vid grph then grph else addVertex vid (BS.VVar, alias) grph)
        T.Alias als _ realtype -> addTermGraph unique realtype (Just als) grph
        T.Error -> error "Error constructor in addTermGraph"

-- | Add a recursive structure type to the type graph
addTermGraphStructure :: Int -> T.Term1 T.Variable -> Maybe Var.Canonical -> TypeGraph info -> TS.Solver (Int, BS.VertexId, TypeGraph info)
addTermGraphStructure unique (T.App1 l r) alias grph = do
    (uql, vidl, gphl) <- addTermGraph unique l Nothing grph
    (uqr, vidr, gphr) <- addTermGraph uql r Nothing gphl

    let vid = BS.VertexId uqr
    let updGrph = addVertex vid (BS.VApp vidl vidr, alias) gphr

    return (uqr + 1, BS.VertexId uqr, updGrph)

addTermGraphStructure unique (T.Fun1 l r) alias grph = do
    -- Add the function constructor to the graph
    let vid = BS.VertexId unique
    let (uq', vid', grph') = (unique + 1, vid, addVertex vid (BS.VCon "Function", Nothing) grph)

    -- Add the left type's subgraph
    (uql, vidl, gphl) <- addTermGraph uq' l Nothing grph'

    -- Add the application of the function to the left's type
    let appLVid = BS.VertexId uql
    let updGrphL = addVertex appLVid (BS.VApp vid' vidl, Nothing) gphl
    let (uqAppL, vidAppL) = (uql + 1, BS.VertexId uql)

    -- Add the right type's subgraph
    (uqr, vidr, gphr) <- addTermGraph uqAppL r Nothing updGrphL

    -- Add the application of (VApp function l) to the right's type
    let appRVid = BS.VertexId uqr
    let updGrphR = addVertex appRVid (BS.VApp vidAppL vidr, alias) gphr

    return (uqr + 1, BS.VertexId uqr, updGrphR)

addTermGraphStructure unique T.EmptyRecord1 alias grph = error "Records not implemented"
addTermGraphStructure unique T.Record1 {} alias grph = error "Records not implemented"


-- | Unify two types in the type graph
-- i.e. state that two types must be equal
unifyTypes :: info -> T.Type -> T.Type -> Int -> TypeGraph info -> TS.Solver (Int, TypeGraph info)
unifyTypes info terml termr i grph = do
    tl <- TS.flatten terml
    tr <- TS.flatten termr

    unifyTypeVars info tl tr i grph


-- | Unify two types in the type graph
-- i.e. state that two types must be equal
unifyTypeVars :: info -> T.Variable -> T.Variable -> Int -> TypeGraph info -> TS.Solver (Int, TypeGraph info)
unifyTypeVars info terml termr i grph = do
    (uql, vidl, grphl)  <- addTermGraph i terml Nothing grph
    (uqr, vidr, grphr)  <- addTermGraph uql termr Nothing grphl

    return (uqr, addNewEdge (vidl, vidr) info grphr)

-- | Generate a type graph from a constraint
-- TODO: solve type schemes, environments and shit
fromConstraint :: T.TypeConstraint -> Int -> TypeGraph Int{-T.TypeConstraint-} -> TS.Solver (Int, TypeGraph Int{-T.TypeConstraint-})
fromConstraint T.CTrue i grph = return (i, grph)
fromConstraint T.CSaveEnv i grph = return (i, grph)
fromConstraint constr@(T.CEqual _ _ l r) i grph = unifyTypes 0{-constr-} l r i grph
fromConstraint (T.CAnd constrs) i grph = helper constrs i grph
    where
        helper [] i' grph' = return (i', grph')
        helper (c : cs) i' grph' = do
            (i'', grph'') <- fromConstraint c i' grph'
            helper cs i'' grph''
fromConstraint (T.CLet schemes constr) i grph = do
    -- TODO: Somehow pass type scheme vars and links
    fromConstraint constr i grph

fromConstraint constr@(T.CInstance _ name term) i grph = do
    env <- TS.getEnv

    -- Get the type of the thing of which the term is an instance
    freshCopy <-
        case M.lookup name env of
          Just (A.A _ tipe) ->
              TS.makeInstance tipe

          Nothing ->
              if "Native." `List.isPrefixOf` name then
                  liftIO (T.mkVar Nothing)

              else
                  error ("Could not find `" ++ name ++ "` when solving type constraints.")

    t <- TS.flatten term
    unifyTypeVars 0{-constr-} freshCopy t i grph


-- | Add a vertex to the type graph
addVertex :: BS.VertexId -> BS.VertexInfo -> TypeGraph info -> TypeGraph info
addVertex v info =
      createGroup (EG.insertVertex v info EG.empty)

-- | Whether a vertex exists in the type graph
vertexExists :: BS.VertexId -> TypeGraph info -> Bool
vertexExists vid = isJust . M.lookup vid . referenceMap


-- | Add an edge to the type graph
addEdge :: BS.EdgeId -> info -> TypeGraph info -> TypeGraph info
addEdge edge@(BS.EdgeId v1 v2 _) info =
 propagateEquality v1 . updateGroupOf v1 (EG.insertEdge edge info) . combineEQGroups [v1, v2]

-- | Adds an edge to the type graph based on vertices
addNewEdge :: (BS.VertexId, BS.VertexId) -> info -> TypeGraph info -> TypeGraph info
addNewEdge (v1, v2) info stg =
 let
    cnr = constraintNumber stg
 in
    addEdge (BS.EdgeId v1 v2 cnr) info (stg { constraintNumber = cnr + 1})

--deleteEdge edge@(BS.EdgeId v1 _ _) =
-- propagateRemoval v1 . updateGroupOf v1 (EG.removeEdge edge)

-- | addClique in TOP
insertClique :: CLQ.Clique -> TypeGraph info -> TypeGraph info
insertClique clq =
    updateGroupOf (CLQ.representative clq) (EG.insertClique clq) . combineEQGroups (CLQ.children clq)

-- | deleteClique in TOP
removeClique :: CLQ.Clique -> TypeGraph info -> TypeGraph info
removeClique clique =
   updateGroupOf (CLQ.representative clique) (EG.removeClique clique)

-- | When an equality edge is inserted, the equality trickles down to subtypes
-- that's what this function applies
propagateEquality :: BS.VertexId -> TypeGraph info -> TypeGraph info
propagateEquality vid stg =
   let (listLeft, listRight) = childrenInGroupOf vid stg
       left  = map (flip representativeInGroupOf stg . CLQ.child) listLeft
       right = map (flip representativeInGroupOf stg . CLQ.child) listRight
   in (if length (nub right) > 1
         then propagateEquality (head right)
         else id)
    . (if length (nub left) > 1
         then propagateEquality (head left)
         else id)
    . (if length listLeft > 1
         then insertClique (CLQ.makeClique listRight) . insertClique (CLQ.makeClique listLeft)
         else id)
    $ stg

propagateRemoval :: BS.VertexId -> TypeGraph info -> TypeGraph info
propagateRemoval i stg =
    let
        (is, new) = splitEQGroups i stg
        ts = map (`childrenInGroupOf` new) is

        (leftList, rightList) = unzip ts
        cliqueLeft  = CLQ.makeClique (concat leftList)
        cliqueRight = CLQ.makeClique (concat rightList)
        newCliques  = [ CLQ.makeClique list | list <- leftList ++ rightList, length list > 1 ]
        children    = [ CLQ.child pc | pc:_ <- leftList ++ rightList ]
    in
        if length (filter (not . null) leftList) > 1 then
            flip (foldr propagateRemoval) children
            . flip (foldr insertClique) newCliques
            . removeClique cliqueRight
            . removeClique cliqueLeft
            $ new
        else
            new

-- | Finds all the children in the equivalence group that contains the given VertexId
childrenInGroupOf :: BS.VertexId -> TypeGraph info -> ([CLQ.ParentChild], [CLQ.ParentChild])
childrenInGroupOf i graph =
      unzip [ ( CLQ.ParentChild { CLQ.parent = p, CLQ.child = t1, CLQ.childSide = CLQ.LeftChild  }
              , CLQ.ParentChild { CLQ.parent = p, CLQ.child = t2, CLQ.childSide = CLQ.RightChild }
              )
            | (p, (BS.VApp t1 t2, _)) <- verticesInGroupOf i graph
            ]