{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}

module Type.Graph.TypeGraph where

import qualified Type.Graph.Basics as BS
import qualified Type.Graph.EQGroup as EG
import qualified Type.Graph.Clique as CLQ
import qualified Type.Graph.Path as P
import qualified Reporting.Error.Type as Error
import qualified Reporting.Region as R
import qualified AST.Variable as Var
import qualified AST.Type as AT
import qualified AST.Interface as Interface
import qualified Type.Type as T
import qualified Type.State as TS
import qualified Type.Unify as U
import qualified Data.Map as M
import qualified Data.UnionFind.IO as UF
import qualified Data.List as List
import qualified Reporting.Annotation as A
import qualified Data.Set as S
import qualified Data.Traversable as TR
import Control.Monad.State (State, liftIO, evalState)
import Control.Monad (foldM)
import Data.List (nub, sort)
import Control.Applicative ((<|>))
import Type.Unify (ExtensionStructure (..))

import Data.Maybe (fromMaybe, fromJust, maybeToList, isJust, listToMaybe, catMaybes)



-- | Representation of a type graph
data TypeGraph info = TypeGraph
   { referenceMap               :: M.Map BS.VertexId Int{- group number -}
   , equivalenceGroupMap        :: M.Map Int (EG.EquivalenceGroup info)
   , equivalenceGroupCounter    :: Int
   , varNumber                  :: Int
   , funcMap                    :: M.Map String Var.Canonical
   , implementations            :: [(Interface.CanonicalInterface, Interface.CanonicalImplementation)]
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
    , implementations         = []
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
getVertexGroup vi grph = fromMaybe (error "getVertexGroup: Vertex has no group!") $ getGroupOf vi grph

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

-- | Get the best fitting region for an error
bestVertexRegion :: TypeGraph T.TypeConstraint -> BS.VertexId -> R.Region
bestVertexRegion grph vid =
    let
        grp :: EG.EquivalenceGroup T.TypeConstraint
        grp = fromJust $ getGroupOf vid grph

        regionFromConstraint :: T.TypeConstraint -> R.Region
        regionFromConstraint (T.CEqual _ rg _ _ _) = rg
        regionFromConstraint (T.CInstance rg _ _ _) = rg

        edges :: [R.Region]
        edges = [ regionFromConstraint cnstr | (BS.EdgeId l _, cnstr) <- EG.edges grp, l == vid ]

        parent :: Maybe BS.VertexId
        parent = EG.getParent vid grp
    in
        case (edges, parent) of
            ((rg : _), _) -> rg
            ([], Just p) -> bestVertexRegion grph p
            (_, Nothing) -> error "Seriously, this thing has nothing to do with constraints whatsoever"

-- | Create a type graph from a single term
addTermGraph :: T.Variable -> Maybe Var.Canonical -> TypeGraph info -> TS.Solver (BS.VertexId, TypeGraph info)
addTermGraph var alias grph = do
    desc <- liftIO $ UF.descriptor var
    let content = T._content desc

    -- Get the vertex id in the representative of this variable
    repr <- liftIO $ UF.repr var
    addContentGraph repr content alias grph


-- | Create a type graph based on a variable's content
addContentGraph :: T.Variable -> T.Content -> Maybe Var.Canonical -> TypeGraph info -> TS.Solver (BS.VertexId, TypeGraph info)
addContentGraph var content alias grph =
    do
        desc <- liftIO $ UF.descriptor var
        let unique = varNumber grph
        let vertexId = fromMaybe unique (T._typegraphid desc)
        let qualExplMap = T._qualifierExplanations desc
        let quals = map (\v -> BS.PInterface v (M.lookup v qualExplMap)) . S.toList . T._qualifiers $ desc

        case content of
            T.Structure t ->
                if isJust (T._typegraphid desc) then
                    return (BS.VertexId vertexId, grph)
                else
                    do
                        -- the vertexId given to the top of this structure
                        liftIO $ UF.modifyDescriptor var (\d -> d { T._typegraphid = Just unique })

                        (vid, grph') <- addTermGraphStructure unique t alias (incVarNumber grph)

                        return (vid, grph')
            T.Atom name ->
                do
                    let vid = BS.VertexId unique
                    let evidence = [BS.Super super | super <- [T.Number, T.Comparable, T.Appendable, T.CompAppend], U.atomMatchesSuper super name] ++ quals
                    return (vid, incVarNumber . addVertex vid (BS.VCon (Var.toString name) evidence, alias) . updateFuncMap name $ grph)

            T.Var flex msuper _ -> do
                let vid = BS.VertexId vertexId
                liftIO $ UF.modifyDescriptor var (\d -> d { T._typegraphid = Just vertexId })
                let exists = vertexExists vid grph
                let predicates = sort $ maybe [] ((:[]) . BS.Super) msuper ++ quals

                return (vid, if exists then grph else incVarNumber . addVertex vid (BS.VVar flex predicates, alias) $ grph)
            T.Alias als _ realtype -> addTermGraph realtype (Just als) grph
            -- pretend there is no error here, the type graph may come to a different conclusion as to where the error is
            T.Error original -> addContentGraph var original alias grph

-- | Add a recursive structure type to the type graph
-- The first parameter is a unique counter, the second parameter a possible reference to a vertexID that already exists in the graph
addTermGraphStructure :: Int -> T.Term1 T.Variable -> Maybe Var.Canonical -> TypeGraph info -> TS.Solver (BS.VertexId, TypeGraph info)
addTermGraphStructure vertexId (T.App1 l r) alias grph = do
    (vidl, gphl) <- addTermGraph l Nothing grph
    (vidr, gphr) <- addTermGraph r Nothing gphl

    let vid = BS.VertexId vertexId
    let updGrph = addVertex vid (BS.VApp vidl vidr, alias) $ gphr

    return (vid, updGrph)

addTermGraphStructure vertexId (T.Fun1 l r) alias grph = do
    -- Add the function constructor to the graph
    let vid = BS.VertexId (varNumber grph)
    let grph' = incVarNumber . addVertex vid (BS.VCon "Function" [], Nothing) $ grph

    -- Add the left type's subgraph
    (vidl, gphl) <- addTermGraph l Nothing grph'

    -- Add the application of the function to the left's type
    let appLVid = BS.VertexId (varNumber gphl)
    let updGrphL = incVarNumber . addVertex appLVid (BS.VApp vid vidl, Nothing) $ gphl

    -- Add the right type's subgraph
    (vidr, gphr) <- addTermGraph r Nothing updGrphL

    -- Add the application of (VApp function l) to the right's type
    let appRVid = BS.VertexId vertexId
    let updGrphR = addVertex appRVid (BS.VApp appLVid vidr, alias) gphr

    return (appRVid, updGrphR)

addTermGraphStructure vertexId T.EmptyRecord1 alias grph =
    return (BS.VertexId vertexId, addVertex (BS.VertexId vertexId) (BS.VCon "1EmptyRecord" [], alias) grph)

addTermGraphStructure vertexId (T.Record1 members extends) alias grph = do
    let recordVid = BS.VertexId vertexId

    -- Add the record members
    (memberMap, grph1) <- addRecordraph (M.toList members) grph

    -- Add the record that this record extends
    (vid, grph2) <- addTermGraph extends alias grph1

    -- Grab the members of the record this record extends
    let extInfo = getVertex vid grph2

    let finalMembers =
            case extInfo of
                Just (BS.VCon "1Record" ((BS.RecordMembers str mbs) : _), _) -> BS.RecordMembers str (M.union mbs memberMap)
                Just (BS.VCon "1EmptyRecord" _, _) -> BS.RecordMembers Empty memberMap

                -- TODO: Alias
                _ -> BS.RecordMembers Extension memberMap

    let extendsEvidence = BS.RecordExtends vid

    -- Add record constructor
    let grph3 = addVertex recordVid (BS.VCon "1Record" [finalMembers, extendsEvidence], Nothing) $ grph2

    return (recordVid, grph3)

-- | Add the members of a record to the graph
addRecordraph :: [(String, T.Variable)] -> TypeGraph info -> TS.Solver (M.Map String BS.VertexId, TypeGraph info)
addRecordraph [] grph = return (M.empty, grph)
addRecordraph ((nm, var) : vars) grph =
    do
        (vid, grph1) <- addTermGraph var Nothing grph
        (memberMap, grph2) <- addRecordraph vars grph1

        return (M.insert nm vid memberMap, grph2)


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


    let grpht = trickleDownRecordEquality vidl vidr info grphr

    return $ addNewEdge (vidl, vidr) info grpht

-- | When there's an (implicit) edge between two records, trickle down the equality
trickleDownRecordEquality :: BS.VertexId -> BS.VertexId -> info -> TypeGraph info -> TypeGraph info
trickleDownRecordEquality l r info grph =
    let
        lval = getGroupOf l grph
        rval = getGroupOf r grph
    in
        case (lval, rval) of
            (Just lgrp, Just rgrp) ->
                let
                    lrecs = M.unions [members | (_, (BS.VCon "1Record" ((BS.RecordMembers _ members) : _), _)) <- EG.vertices lgrp]
                    rrecs = M.unions [members | (_, (BS.VCon "1Record" ((BS.RecordMembers _ members) : _), _)) <- EG.vertices rgrp]
                in
                    linkQualifiers lrecs rrecs info grph
            _ -> error "trickleDownRecordEquality: Error in finding groups I just added"


-- | Connect the members of records with edges
linkQualifiers :: forall info . M.Map String BS.VertexId -> M.Map String BS.VertexId -> info -> TypeGraph info -> TypeGraph info
linkQualifiers lquals rquals info grph =
    let
        lList, rList :: [(String, BS.VertexId)]
        lList = M.toList lquals
        rList = M.toList rquals

        customZip :: [(String, BS.VertexId)] -> [(String, BS.VertexId)] -> [(BS.VertexId, BS.VertexId)]
        customZip [] _ = []
        customZip _ [] = []
        customZip lls@((lname, lid) : ls) rrs@((rname, rid) : rs) =
            case compare lname rname of
                LT -> customZip ls rrs
                EQ -> (lid, rid) : customZip ls rs
                GT -> customZip lls rs

        edgeList :: [(BS.VertexId, BS.VertexId)]
        edgeList = customZip lList rList

        insEdge :: TypeGraph info -> (BS.VertexId, BS.VertexId) -> TypeGraph info
        insEdge g eid = addNewEdge eid info g

    in
        foldl insEdge grph edgeList



-- | Generate type graph from a single scheme
fromScheme :: T.TypeScheme -> TypeGraph T.TypeConstraint -> TS.Solver (TypeGraph T.TypeConstraint)
fromScheme scheme grph =
    do
        -- Update the headers
        let flatten (A.A region term) = A.A region <$> TS.flatten term
        updHeaders <- TR.traverse flatten (T._header scheme)
        TS.modifyEnv $ \env -> M.union updHeaders env

        -- Build nested constraints into type graph
        fromConstraintHelper (T._constraint scheme) grph

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
updatefuncMapHint (Error.UnexpectedArg (Just v) _ _ _ _) grph = updateFuncMap v grph
updatefuncMapHint (Error.FunctionArity (Just v) _ _ _) grph = updateFuncMap v grph
updatefuncMapHint (Error.Function (Just v) _) grph = updateFuncMap v grph
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



-- | Replace implicit edges with their sets of children edges
expandPath :: forall info . Show info => TypeGraph info -> P.Path info -> P.Path info
expandPath grph (l P.:|: r) = expandPath grph l P.:|: expandPath grph r
expandPath grph (l P.:+: r) = expandPath grph l P.:+: expandPath grph r
expandPath grph st@(P.Step (BS.EdgeId strt finish) P.Implied) =
    let
        ei = EI { start = strt, treeStack = [], path = P.Empty, lastSeen = BS.VertexId (-1), seenParents = S.empty }
    in
        fromMaybe st $ expandStep grph ei finish -- fst . fromMaybe (st, undefined) $ expandStep grph eid S.empty
expandPath _     x = x


-- try 2:
data ExpansionIteration info =
    EI
    { start :: BS.VertexId
    , treeStack :: [CLQ.ChildSide]
    , seenParents :: S.Set BS.EdgeId
    , lastSeen :: BS.VertexId
    , path :: P.Path info
    }

instance Show (ExpansionIteration info) where
    show ei = "Start: " ++ show (start ei) ++ ", stack: " ++ show (treeStack ei)

expandStep :: forall info . Show info => TypeGraph info -> ExpansionIteration info -> BS.VertexId -> Maybe (P.Path info)
expandStep grph e finish
    | start e == finish = Just P.Empty
    | otherwise =

    let
        grp ei = fromJust $ getGroupOf (start ei) grph
        edges ei = EG.edges (grp ei)

        initialEdgeSteps :: ExpansionIteration info -> [ExpansionIteration info]
        initialEdgeSteps ei =
            [ ei
                { start = b
                , path = path ei P.:+: (P.Step eid (P.Initial inf))
                , lastSeen = start ei
                }
            |
                (eid@(BS.EdgeId a b), inf) <- edges ei,
                a == start ei,

                lastSeen ei /= b
            ]
            ++
            [ ei
                { start = a
                , path = path ei P.:+: P.Step eid (P.Initial inf)
                , lastSeen = start ei
                }
            |
                (eid@(BS.EdgeId a b), inf) <- edges ei,
                b == start ei,

                lastSeen ei /= a
            ]

        parentEdgeSteps :: ExpansionIteration info -> [ExpansionIteration info]
        parentEdgeSteps ei =

            [ ei
                { start = CLQ.parent pc
                , treeStack = CLQ.childSide pc : treeStack ei
                , path = path ei P.:+: P.Step (BS.EdgeId (CLQ.child pc) (CLQ.parent pc)) (P.Parent (CLQ.childSide pc))
                , lastSeen = start ei
                , seenParents = S.insert edge $ seenParents ei
                }
            |
                -- Look for parents
                clq <- EG.cliques (grp ei),
                let mPc = CLQ.getParentChild (start ei) clq,
                isJust mPc,
                let pc = fromJust mPc,
                let edge = BS.EdgeId (CLQ.child pc) (CLQ.parent pc),

                lastSeen ei /= CLQ.parent pc,
                not $ edge `S.member` seenParents ei
            ]

        childEdgeSteps :: ExpansionIteration info -> [ExpansionIteration info]
        childEdgeSteps ei =
            case (treeStack ei, getVertex (start ei) grph) of
                (side : restStack, Just (BS.VApp l r, _)) ->
                    [ ei
                        { start = child
                        , treeStack = restStack
                        , path = path ei P.:+: P.Step (BS.EdgeId (start ei) child) (P.Child side)
                        , lastSeen = start ei
                        }
                    |
                        let child =
                                case side of
                                    CLQ.LeftChild -> l
                                    CLQ.RightChild -> r,

                        lastSeen ei /= child
                    ]

                _ -> []


        rec :: [ExpansionIteration info] -> Maybe (P.Path info)
        rec eis =
            let
                nextIteration =
                    concatMap initialEdgeSteps eis ++
                    concatMap parentEdgeSteps eis ++
                    concatMap childEdgeSteps eis

                -- A path has been found when the finish has been reached and
                -- the stack of times gone up the tree is empty
                anySuccess =
                    filter (\ei -> start ei == finish && null (treeStack ei)) nextIteration
            in
                case (anySuccess, nextIteration) of
                    (_, []) -> Nothing -- No path exists
                    ([], _) -> rec nextIteration
                    (xs, _) -> Just $ foldl1 (P.:|:) $ map path xs

    in
        rec [e]


-- | Finds all the children in the equivalence group that contains the given VertexId
childrenInGroupOf :: BS.VertexId -> TypeGraph info -> ([CLQ.ParentChild], [CLQ.ParentChild])
childrenInGroupOf i graph =
      unzip [ ( CLQ.ParentChild { CLQ.parent = p, CLQ.child = t1, CLQ.childSide = CLQ.LeftChild  }
              , CLQ.ParentChild { CLQ.parent = p, CLQ.child = t2, CLQ.childSide = CLQ.RightChild }
              )
            | (p, (BS.VApp t1 t2, _)) <- verticesInGroupOf i graph
            ]

data SubstitutionError info =
      InfiniteType BS.VertexId (P.Path info)
    | InconsistentType (EG.EquivalenceGroup info) [(BS.VertexId, BS.VertexId)]
    | MissingImplementation BS.VertexId Var.Canonical AT.Canonical' (Maybe String)
    deriving (Show)

findInfiniteTypes :: forall info . TypeGraph info -> [SubstitutionError info]
findInfiniteTypes grph =
    let
        eqgroups :: [EG.EquivalenceGroup info]
        eqgroups = map snd . M.toList . equivalenceGroupMap $ grph

        -- All type applications
        apps :: [(BS.VertexId, BS.VertexInfo)]
        apps = [app | grp <- eqgroups, app <- [app | app@(_, (BS.VApp _ _, _)) <- EG.vertices grp]]

        --
        rec :: BS.VertexId -> (BS.VertexId, BS.VertexInfo) -> S.Set BS.VertexId -> P.Path info -> [SubstitutionError info]
        rec start (vid, (BS.VApp l r, _)) history pth
            -- Only find infinite paths in which the start vertex is the minimum
            -- Prevents duplicate infinite paths that each start at a different vertex of the cycle
            | vid > start = []
            | vid `S.member` history =
                [InfiniteType vid pth | vid == start]
            | otherwise =
                let
                    present :: S.Set BS.VertexId
                    present = S.insert vid history

                    leftPath :: P.Path info
                    leftPath = pth P.:+: (P.Step (BS.EdgeId vid l) (P.Child CLQ.LeftChild))

                    rightPath :: P.Path info
                    rightPath = pth P.:+: (P.Step (BS.EdgeId vid r) (P.Child CLQ.RightChild))

                    egl :: EG.EquivalenceGroup info
                    egl = getVertexGroup l grph

                    egr :: EG.EquivalenceGroup info
                    egr = getVertexGroup r grph

                    linf = fromJust . lookup l . EG.vertices $ egl
                    rinf = fromJust . lookup r . EG.vertices $ egr
                in
                    case (linf, rinf) of
                        ((BS.VApp _ _, _), (BS.VApp _ _, _)) ->
                            rec start (l, linf) present leftPath ++
                            rec start (r, rinf) present rightPath
                        ((BS.VApp _ _, _), _) -> rec start (l, linf) present leftPath
                        (_, (BS.VApp _ _, _)) -> rec start (r, rinf) present rightPath
                        _ -> []
    in
        concat [rec vid app S.empty P.Empty | app@(vid, _) <- apps]

-- | Try to reconstruct an infinite type to the best of the type graph's ability
reconstructInfiniteType :: BS.VertexId -> S.Set BS.VertexId -> TypeGraph info -> AT.Canonical
reconstructInfiniteType vid infs grph = evalState (reconstructInfiniteType' vid infs grph) (T.makeNameState S.empty)

-- | Try to reconstruct an infinite type to the best of the type graph's ability
reconstructInfiniteType' :: forall info . BS.VertexId -> S.Set BS.VertexId -> TypeGraph info -> State T.NameState AT.Canonical
reconstructInfiniteType' vid infs grph =
    let
        eg :: EG.EquivalenceGroup info
        eg = getVertexGroup vid grph

        rec :: BS.VertexId -> State T.NameState AT.Canonical
        rec vid' =
            if vid' `S.member` infs then
                return $ AT.unqualified $ AT.Var "∞"
            else
                reconstructInfiniteType' vid' (S.insert vid' infs) grph
    in
        case lookup vid (EG.vertices eg) of
            Just (BS.VApp l r, _) ->
                do
                    (AT.QT lquals lt) <- rec l
                    (AT.QT rquals rt) <- rec r

                    return $ AT.QT (lquals ++ rquals) $ flattenGraphType $ AT.App lt [rt]
            Just (BS.VCon "Function" _, _) -> return $ AT.unqualified $ AT.Var "Function"
            Just (BS.VCon "1EmptyRecord" _, _) -> return $ AT.unqualified $ AT.Record [] Nothing
            Just (BS.VCon "1Record" evidence, _) ->
                do
                    let members = head [ ms | (BS.RecordMembers _ ms) <- evidence ]
                    let (memNames, memVertices) = unzip $ M.toList members
                    memTypes <- mapM (\v -> reconstructInfiniteType' v infs grph) memVertices
                    let memTypes' = map AT.qtype memTypes
                    let memQuals = concatMap AT.qualifiers memTypes

                    let extends = head [ v | (BS.RecordExtends v) <- evidence ]
                    extends' <- reconstructInfiniteType' extends infs grph
                    let extendsTp =
                            case AT.qtype extends' of
                                AT.Var _ -> Nothing
                                x -> Just x

                    return $ AT.QT memQuals $ AT.Record (zip memNames memTypes') extendsTp
            Just (BS.VCon name _, _) -> return $ maybe (AT.unqualified $ AT.Var name) (AT.unqualified . AT.Type) (M.lookup name . funcMap $ grph)
            Just (BS.VVar _ preds', originalName) ->
                case EG.typeOfGroup eg of
                    Right (vid', (BS.VVar _ preds, _)) ->
                        do
                            let super = listToMaybe [ s | BS.Super s <- preds ]
                            varName <- T.getVertexName (BS.unVertexId vid') super -- AT.Var $ "a" ++ show (BS.unVertexId vid)
                            let varName' =
                                    case originalName of
                                        Just x -> AT.Var $ Var.toString x
                                        Nothing -> AT.Var varName

                            let quals = [ AT.Qualifier nm varName' | BS.PInterface nm _ <- preds ]

                            if vid' == vid then
                                return $ AT.QT quals varName'
                             else
                                rec vid'
                    Right (vid', _) -> rec vid'
                    Left _ ->
                        do
                            let super = listToMaybe [ s | BS.Super s <- preds' ]
                            varName <- T.getVertexName (BS.unVertexId vid) super
                            let varName' =
                                    case originalName of
                                        Just x -> AT.Var $ Var.toString x
                                        Nothing -> AT.Var varName
                            return $ AT.QT [] varName' -- ("a" ++ show (BS.unVertexId vid))
            Nothing -> return $ AT.unqualified $ AT.Var "?"

-- | Flattens the type created by reconstructing the type of something in the type graph
flattenGraphType :: AT.Canonical' -> AT.Canonical'
flattenGraphType (AT.App (AT.App (AT.Var "Function") [l]) [r]) = AT.Lambda (flattenGraphType l) (flattenGraphType r)
flattenGraphType (AT.App l [r]) =
    case flattenGraphType l of
        t@(AT.Type _) -> AT.App t [flattenGraphType r]
        t@(AT.Var _) -> AT.App t [flattenGraphType r]
        AT.App l' r' -> AT.App l' (r' ++ [flattenGraphType r])
flattenGraphType x = x

-- | Gives the type graph inferred type of a vertex that contains a type variable
-- TODO: Qualified types?
substituteVariable :: forall info . Show info => BS.VertexId -> TypeGraph info -> Either (SubstitutionError info) BS.VertexInfo
substituteVariable vid grph =
    let
        -- Recursive variable substitution
        -- Keeps track of which type variables have been seen before (occurs check)
        rec :: S.Set BS.VertexId -> BS.VertexId -> BS.VertexInfo -> Either (SubstitutionError info) (BS.VertexId, BS.VertexInfo)
        rec _ vi inf@(BS.VVar T.Rigid _, _) = Right (vi, inf)
        rec history vi (BS.VVar _ _, _)
            | vi `S.member` history = Left (InfiniteType vi P.Fail)
            | otherwise =
                do
                    let eg = getVertexGroup vi grph
                    let present = S.insert vi history

                    case EG.typeOfGroup eg of
                        Right (vi', vinfo@(BS.VVar _ _, _)) -> if vi == vi' then Right (vi, vinfo) else rec present vi' vinfo
                        Right (_, tp) -> Right (vi, tp)
                        Left conflicts -> Left (InconsistentType eg conflicts)

        rec _ vi inf@(BS.VCon _ _, _) =
            let
                eg = getVertexGroup vi grph
            in
                case EG.typeOfGroup eg of
                    Right _ -> Right (vi, inf)
                    Left conflicts -> Left (InconsistentType eg conflicts)

        rec history vi (BS.VApp l r, alias)
            | vi `S.member` history = Left (InfiniteType vi P.Fail)
            | otherwise =
                do
                    let present = S.insert vi history
                    let lVinf = fromMaybe (error "substituteVariable: left app does not exist!") $ getVertex l grph
                    (lVId, _) <- rec present l lVinf

                    let rVinf = fromMaybe (error "substituteVariable: left app does not exist!") $ getVertex r grph
                    (rVId, _) <- rec present r rVinf

                    let eg = getVertexGroup vi grph

                    case EG.typeOfGroup eg of
                        Right _ -> Right (vi, (BS.VApp lVId rVId, alias))
                        Left conflicts -> Left (InconsistentType eg conflicts)

        vertexInfo :: BS.VertexInfo
        vertexInfo = fromMaybe (error "substituteVariable: Vertex does not exist") (getVertex vid grph)
    in
        do
            res <- rec S.empty vid vertexInfo
            return (snd res)

-- | Figure out whether there are any missing implementations for qualified types
findMissingImplementations :: forall info . TypeGraph info -> [SubstitutionError info]
findMissingImplementations grph =
    let
        groups :: [EG.EquivalenceGroup info]
        groups = M.elems $ equivalenceGroupMap grph

        impls :: [(Interface.CanonicalInterface, Interface.CanonicalImplementation)]
        impls = implementations grph

        -- The implementation predicates that live within a certain group
        predicates :: EG.EquivalenceGroup info -> [BS.Predicate]
        predicates grp = [ p | (_, (BS.VVar _ ps, _)) <- EG.vertices grp, p@(BS.PInterface _ _) <- ps ]

        propagateDown :: BS.VertexId -> AT.Canonical' -> (BS.VertexId, BS.VertexInfo) -> Maybe String -> AT.Qualifier' Var.Canonical AT.Canonical' -> [SubstitutionError info]
        propagateDown root tp vrtx@(_, (inf, _)) expl qual@(AT.Qualifier classref classvar)
            | tp == classvar = checkPredicate root vrtx (BS.PInterface classref expl)
            | otherwise =
                case (tp, inf) of
                    -- One application left
                    (AT.App _ [vr], BS.VApp _ r) -> propagateDown root vr (r, fromJust $ getVertex r grph) expl qual
                    (AT.App _ [vr], _) -> propagateDown root vr vrtx expl qual
                    -- multiple applications
                    (AT.App x rs, BS.VApp l r) ->
                        let
                            linf :: BS.VertexInfo
                            linf = fromJust $ getVertex l grph

                            rinf :: BS.VertexInfo
                            rinf = fromJust $ getVertex r grph
                        in
                            propagateDown root (AT.App x (init rs)) (l, linf) expl qual ++ propagateDown root (AT.App x [last rs]) (r, rinf) expl qual
                    (_, _) -> [] -- TODO: functions or something haha

        -- | Root being the root of the app tree where it started propagating down the qualifiers
        checkPredicate :: BS.VertexId -> (BS.VertexId, BS.VertexInfo) -> BS.Predicate -> [SubstitutionError info]
        checkPredicate root vrtx@(vid, (inf, _)) (BS.PInterface pdc expl) =
            case inf of
                BS.VVar _ _ -> []
                BS.VCon nm _ ->
                    case U.findImplementation impls pdc (AT.Type . fromJust . M.lookup nm $ funcMap grph) of
                        Just _ -> []
                        Nothing -> [MissingImplementation root pdc (AT.Type . fromJust . M.lookup nm $ funcMap grph) expl]
                BS.VApp l r ->
                    let
                        tp :: AT.Canonical'
                        tp = AT.qtype $ reconstructInfiniteType vid S.empty grph
                    in
                        case U.findImplementation impls pdc tp of
                            Just (_, impl) -> concatMap (propagateDown root (Interface.impltype impl) vrtx expl) (Interface.implquals impl)
                            Nothing -> [MissingImplementation root pdc tp expl]

        findInGroup :: EG.EquivalenceGroup info -> [SubstitutionError info]
        findInGroup grp =
                concat [ checkPredicate vid vrtc p | vrtc@(vid, _) <- EG.vertices grp, p <- predicates grp ]
    in
        concatMap findInGroup groups

-- | Gets all the errors in the type graph
getErrors :: forall info . Show info => TypeGraph info -> [SubstitutionError info]
getErrors grph =
    let
        eGroups :: [EG.EquivalenceGroup info]
        eGroups = map snd . M.toList . equivalenceGroupMap $ grph

        grpTypes :: [Either [(BS.VertexId, BS.VertexId)] (BS.VertexId, BS.VertexInfo)]
        grpTypes = map EG.typeOfGroup eGroups

        errTypes :: [SubstitutionError info]
        errTypes = [InconsistentType eg errs | (eg, Left errs) <- zip eGroups grpTypes]

        infiniteErrors :: [SubstitutionError info]
        infiniteErrors = findInfiniteTypes grph

        missingImplementations :: [SubstitutionError info]
        missingImplementations = findMissingImplementations grph
    in
        infiniteErrors ++ errTypes ++ missingImplementations

-- | All equivalence paths from one vertex to another
allPaths :: BS.VertexId -> BS.VertexId -> TypeGraph info -> Maybe (P.Path info)
allPaths l r grph = EG.equalPaths l r <$> getGroupOf l grph

-- | Get the equality paths between inconsistent types
inconsistentTypesPaths :: SubstitutionError info -> [P.Path info]
inconsistentTypesPaths (InfiniteType _ p) = [p]
inconsistentTypesPaths (MissingImplementation {}) = []
inconsistentTypesPaths (InconsistentType grp vids) = [EG.equalPaths l r grp | (l, r) <- vids]
