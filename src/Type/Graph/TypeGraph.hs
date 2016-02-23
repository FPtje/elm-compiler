{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}

module Type.Graph.TypeGraph where

import qualified Type.Graph.Basics as BS
import qualified Type.Graph.EQGroup as EG
import qualified Type.Graph.Clique as CLQ
import qualified Reporting.Error.Type as Error
import qualified Type.Graph.Path as P
import qualified AST.Variable as Var
import qualified Type.Type as T
import qualified Type.State as TS
import qualified Data.Map as M
import qualified Data.UnionFind.IO as UF
import qualified Data.List as List
import qualified Reporting.Annotation as A
import qualified Data.Set as S
import Control.Monad.State (liftIO)
import Control.Monad (foldM)
import Data.List (nub)
import Data.Either (lefts)

import Data.Maybe (fromMaybe, maybeToList, isJust)

import Debug.Trace


-- | Representation of a type graph
data TypeGraph info = TypeGraph
   { referenceMap               :: M.Map BS.VertexId Int{- group number -}
   , equivalenceGroupMap        :: M.Map Int (EG.EquivalenceGroup info)
   , equivalenceGroupCounter    :: Int
   , varNumber                  :: Int
   , funcMap                    :: M.Map String Var.Canonical
   }
   deriving (Show)

-- | Empty type graph
empty :: TypeGraph info
empty = TypeGraph
    { referenceMap            = M.empty
    , equivalenceGroupMap     = M.empty
    , equivalenceGroupCounter = 0
    , varNumber               = 0
    , funcMap                 = M.empty
    }

-- | Increase the unique counter for type graph variables
incVarNumber :: TypeGraph info -> TypeGraph info
incVarNumber grph = grph { varNumber = varNumber grph + 1 }

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
        list@(_:_:_) ->
            let
                eqgroups = map (fromMaybe (error "combineEQGroups: Unexpected non-existing VertexId") . flip getGroupOf grph) list
                newGroup = foldr EG.combine EG.empty eqgroups
            in
                createGroup newGroup . foldr removeGroup grph $ eqgroups
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
-- equivalenceGroupOf in TOP
getGroupOf :: BS.VertexId -> TypeGraph info -> Maybe (EG.EquivalenceGroup info)
getGroupOf vid grph =
    do
        eqnr <- M.lookup vid (referenceMap grph)
        M.lookup eqnr (equivalenceGroupMap grph)

-- | Same as getGroupOf, but errors when the vertex oes not exist
getVertexGroup :: BS.VertexId -> TypeGraph info -> EG.EquivalenceGroup info
getVertexGroup vi grph = fromMaybe (error "substituteVariable: Vertex has no group!") $ getGroupOf vi grph

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

-- | Create a type graph from a single term
addTermGraph :: T.Variable -> Maybe Var.Canonical -> TypeGraph info -> TS.Solver (BS.VertexId, TypeGraph info)
addTermGraph var alias grph = do
    let unique = varNumber grph
    desc <- liftIO $ UF.descriptor var
    let content = T._content desc

    -- Get the vertex id in the representative of this variable
    repr <- liftIO $ UF.repr var
    reprDesc <- liftIO $ UF.descriptor repr
    let vertexId = fromMaybe unique (T._typegraphid reprDesc)

    case content of
        T.Structure t ->
            if vertexExists (BS.VertexId vertexId) grph then
                return (BS.VertexId vertexId, grph)
            else
                do
                    (vid, grph') <- addTermGraphStructure (T._typegraphid reprDesc) t alias grph
                    liftIO $ UF.modifyDescriptor repr (\d -> d { T._typegraphid = Just (BS.unVertexId vid) })
                    return (vid, grph')
        T.Atom name ->
            do
                let vid = BS.VertexId unique
                return (vid, incVarNumber . addVertex vid (BS.VCon (Var.toString name), alias) $ grph)

        T.Var _ _ _ -> do
            let vid = BS.VertexId vertexId
            liftIO $ UF.modifyDescriptor repr (\d -> d { T._typegraphid = Just vertexId })
            let exists = vertexExists vid grph

            return (vid, if exists then grph else incVarNumber . addVertex vid (BS.VVar, alias) $ grph)
        T.Alias als _ realtype -> addTermGraph realtype (Just als) grph
        -- pretend there is no error here, the type graph may come to a different conclusion as to where the error is
        T.Error actual -> addTermGraph actual alias grph

-- | Add a recursive structure type to the type graph
-- The first parameter is a unique counter, the second parameter a possible reference to a vertexID that already exists in the graph
addTermGraphStructure :: Maybe Int -> T.Term1 T.Variable -> Maybe Var.Canonical -> TypeGraph info -> TS.Solver (BS.VertexId, TypeGraph info)
addTermGraphStructure vertexId (T.App1 l r) alias grph = do
    (vidl, gphl) <- addTermGraph l Nothing grph
    (vidr, gphr) <- addTermGraph r Nothing gphl

    let vid = BS.VertexId (fromMaybe (varNumber gphr) vertexId)
    let updGrph = addVertex vid (BS.VApp vidl vidr, alias) $ gphr

    return (vid, if isJust vertexId then updGrph else incVarNumber updGrph)

addTermGraphStructure vertexId (T.Fun1 l r) alias grph = do
    -- Add the function constructor to the graph
    let vid = BS.VertexId (varNumber grph)
    let grph' = incVarNumber . addVertex vid (BS.VCon "Function", Nothing) $ grph

    -- Add the left type's subgraph
    (vidl, gphl) <- addTermGraph l Nothing grph'

    -- Add the application of the function to the left's type
    let appLVid = BS.VertexId (varNumber gphl)
    let updGrphL = incVarNumber . addVertex appLVid (BS.VApp vid vidl, Nothing) $ gphl

    -- Add the right type's subgraph
    (vidr, gphr) <- addTermGraph r Nothing updGrphL

    -- Add the application of (VApp function l) to the right's type
    let appRVid = BS.VertexId (fromMaybe (varNumber gphr) vertexId)
    let updGrphR = addVertex appRVid (BS.VApp appLVid vidr, alias) gphr
    let doInc = if isJust vertexId then id else incVarNumber

    return (appRVid, doInc updGrphR)

addTermGraphStructure vertexId T.EmptyRecord1 alias grph = error "Records not implemented"
addTermGraphStructure vertexId T.Record1 {} alias grph = error "Records not implemented"


-- | Unify two types in the type graph
-- i.e. state that two types must be equal
unifyTypes :: info -> T.Type -> T.Type -> TypeGraph info -> TS.Solver (TypeGraph info)
unifyTypes info terml termr grph = do
    tl <- TS.flatten terml
    tr <- TS.flatten termr

    unifyTypeVars info tl tr grph


-- | Unify two types in the type graph
-- i.e. state that two types must be equal
unifyTypeVars :: info -> T.Variable -> T.Variable -> TypeGraph info -> TS.Solver (TypeGraph info)
unifyTypeVars info terml termr grph = do
    (vidl, grphl)  <- addTermGraph terml Nothing grph
    (vidr, grphr)  <- addTermGraph termr Nothing grphl

    return $ addNewEdge (vidl, vidr) info grphr


-- | Generate type graph from a single scheme
fromScheme :: T.TypeScheme -> TypeGraph T.TypeConstraint -> TS.Solver (TypeGraph T.TypeConstraint)
fromScheme scheme grph = fromConstraintHelper (T._constraint scheme) grph

-- | Generate type graph from type scheme
-- Note: only simple type schmemes
fromSchemes :: [T.TypeScheme] -> TypeGraph T.TypeConstraint -> TS.Solver (TypeGraph T.TypeConstraint)
fromSchemes [] grph = return grph
fromSchemes (s : ss) grph =
    do
        grph' <- fromSchemes ss grph
        fromScheme s grph'

updateFuncMap :: Var.Canonical -> TypeGraph a -> TypeGraph a
updateFuncMap var grph = grph {funcMap = M.insert (Var.toString var) var (funcMap grph)}

updatefuncMapHint :: Error.Hint -> TypeGraph a -> TypeGraph a
updatefuncMapHint (Error.BinopLeft v _) grph = updateFuncMap v grph
updatefuncMapHint (Error.BinopRight v _) grph = updateFuncMap v grph
updatefuncMapHint (Error.UnexpectedArg (Just v) _ _ _) grph = updateFuncMap v grph
updatefuncMapHint (Error.FunctionArity (Just v) _ _ _) grph = updateFuncMap v grph
updatefuncMapHint (Error.Function (Just v)) grph = updateFuncMap v grph
updatefuncMapHint _ grph = grph

-- | Generate a type graph from a constraint
fromConstraint :: T.TypeConstraint -> TS.Solver (TypeGraph T.TypeConstraint)
fromConstraint cnstr = fromConstraintHelper cnstr empty

fromConstraintHelper :: T.TypeConstraint -> TypeGraph T.TypeConstraint -> TS.Solver (TypeGraph T.TypeConstraint)
fromConstraintHelper T.CTrue grph = return grph
fromConstraintHelper T.CSaveEnv grph = return grph
fromConstraintHelper constr@(T.CEqual err _ l r _) grph = unifyTypes constr l r . updatefuncMapHint err $ grph
fromConstraintHelper (T.CAnd constrs) grph = foldM (flip fromConstraintHelper) grph constrs
fromConstraintHelper (T.CLet schemes constr) grph =
    do
        grph' <- fromSchemes schemes grph
        fromConstraintHelper constr grph'

fromConstraintHelper constr@(T.CInstance _ name term _) grph = do
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
    unifyTypeVars constr freshCopy t grph

-- | Find the root of a vertex in a type graph
findRoot :: BS.VertexId -> TypeGraph info -> BS.VertexId
findRoot v grph =
    case EG.getParent v (getVertexGroup v grph) of
        Just parent -> findRoot parent grph
        Nothing -> v


-- | Add a vertex to the type graph
addVertex :: BS.VertexId -> BS.VertexInfo -> TypeGraph info -> TypeGraph info
addVertex v info =
      createGroup (EG.insertVertex v info EG.empty)

-- | Whether a vertex exists in the type graph
vertexExists :: BS.VertexId -> TypeGraph info -> Bool
vertexExists vid = isJust . M.lookup vid . referenceMap


-- Receives a vertex from the type graph
getVertex :: BS.VertexId -> TypeGraph info -> Maybe BS.VertexInfo
getVertex vid grph =
    do
        grpId <- M.lookup vid (referenceMap grph)
        eg <- M.lookup grpId (equivalenceGroupMap grph)
        lookup vid (EG.vertices eg)

-- | Add an edge to the type graph
addEdge :: BS.EdgeId -> info -> TypeGraph info -> TypeGraph info
addEdge edge@(BS.EdgeId v1 v2) info =
 propagateEquality v1 . updateGroupOf v1 (EG.insertEdge edge info) . combineEQGroups [v1, v2]

-- | Adds an edge to the type graph based on vertices
addNewEdge :: (BS.VertexId, BS.VertexId) -> info -> TypeGraph info -> TypeGraph info
addNewEdge (v1, v2) info grph = addEdge (BS.EdgeId v1 v2) info grph

-- | Deletes an edge from the graph
deleteEdge :: BS.EdgeId -> TypeGraph info -> TypeGraph info
deleteEdge edge@(BS.EdgeId v1 _) =
    propagateRemoval v1 . updateGroupOf v1 (EG.removeEdge edge)

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
propagateEquality vid grph =
   let (listLeft, listRight) = childrenInGroupOf vid grph
       left  = map (flip representativeInGroupOf grph . CLQ.child) listLeft
       right = map (flip representativeInGroupOf grph . CLQ.child) listRight
   in (if length (nub right) > 1
         then propagateEquality (head right)
         else id)
    . (if length (nub left) > 1
         then propagateEquality (head left)
         else id)
    . (if length listLeft > 1
         then insertClique (CLQ.makeClique listRight) . insertClique (CLQ.makeClique listLeft)
         else id)
    $ grph

-- | Used in removing an edge. Propagates the removal of a single vertex.
propagateRemoval :: BS.VertexId -> TypeGraph info -> TypeGraph info
propagateRemoval i grph =
    let
        (is, new) = splitEQGroups i grph
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

data SubstitutionError info =
      InfiniteType BS.VertexId
    | InconsistentType (EG.EquivalenceGroup info) [(BS.VertexId, BS.VertexId)]
    deriving (Show)

-- | Gives the type graph inferred type of a vertex that contains a type variable
substituteVariable :: forall info . BS.VertexId -> TypeGraph info -> Either (SubstitutionError info) BS.VertexInfo
substituteVariable vid grph =
    let
        -- Recursive variable substitution
        -- Keeps track of which type variables have been seen before (occurs check)
        rec :: S.Set BS.VertexId -> BS.VertexId -> BS.VertexInfo -> Either (SubstitutionError info) (BS.VertexId, BS.VertexInfo)
        rec history vi (BS.VVar, _)
            | vi `S.member` history = Left (InfiniteType vi)
            | otherwise =
                do
                    let eg = getVertexGroup vid grph
                    let present = S.insert vi history

                    case EG.typeOfGroup eg of
                        Right (vi', vinfo@(BS.VVar, _)) -> if vi == vi' then Right (vi, vinfo) else rec present vi' vinfo
                        Right (_, tp) -> Right (vi, tp)
                        Left conflicts -> Left (InconsistentType eg conflicts)

        rec _ vi inf@(BS.VCon _, _) =
            let
                eg = getVertexGroup vid grph
            in
                case EG.typeOfGroup eg of
                    Right _ -> Right (vi, inf)
                    Left conflicts -> Left (InconsistentType eg conflicts)

        rec history vi (BS.VApp l r, alias) =
            do
                let lVinf = fromMaybe (error "substituteVariable: left app does not exist!") $ getVertex l grph
                (lVId, _) <- rec history l lVinf

                let rVinf = fromMaybe (error "substituteVariable: left app does not exist!") $ getVertex r grph
                (rVId, _) <- rec history r rVinf

                let eg = getVertexGroup vid grph

                case EG.typeOfGroup eg of
                    Right _ -> Right (vi, (BS.VApp lVId rVId, alias))
                    Left conflicts -> Left (InconsistentType eg conflicts)

        vertexInfo :: BS.VertexInfo
        vertexInfo = fromMaybe (error "substituteVariable: Vertex does not exist") (getVertex vid grph)
    in
        do
            res <- rec S.empty vid vertexInfo
            return (snd res)

-- | Gets all the errors in the type graph
getErrors :: forall info . TypeGraph info -> [SubstitutionError info]
getErrors grph =
    let
        eGroups :: [EG.EquivalenceGroup info]
        eGroups = map snd . M.toList . equivalenceGroupMap $ grph

        reprs :: [BS.VertexId]
        reprs = map EG.representative eGroups

        substVars :: [Either (SubstitutionError info) BS.VertexInfo]
        substVars = map (`substituteVariable` grph) reprs
    in
        lefts substVars

-- | All equivalence paths from one vertex to another
allPaths :: BS.VertexId -> BS.VertexId -> TypeGraph info -> Maybe (P.Path info)
allPaths l r grph = EG.equalPaths l r <$> getGroupOf l grph

-- | Get the equality paths between inconsistent types
inconsistentTypesPaths :: SubstitutionError info -> [P.Path info]
inconsistentTypesPaths (InfiniteType vid) = trace ("inconsistentTypesPaths: InfiniteType given. Not supported. " ++ show vid) []
inconsistentTypesPaths (InconsistentType grp vids) = [EG.equalPaths l r grp | (l, r) <- vids]
