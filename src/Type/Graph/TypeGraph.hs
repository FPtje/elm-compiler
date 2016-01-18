{-# OPTIONS_GHC -Wall #-}

module Type.Graph.TypeGraph where

import qualified Type.Graph.Basics as BS
import qualified Type.Graph.EQGroup as EG
import qualified Type.Graph.Clique as CLQ
import qualified AST.Variable as Var
import qualified Type.Type as T
import qualified Data.Map as M
import qualified Data.UnionFind.IO as UF
import Data.List (nub)

import Data.Maybe (fromMaybe, maybeToList)


-- | Representation of a type graph
data TypeGraph info = TypeGraph
   { referenceMap               :: M.Map BS.VertexId Int{- group number -}
   , equivalenceGroupMap        :: M.Map Int (EG.EquivalenceGroup info)
   , equivalenceGroupCounter    :: Int
   , possibleErrors             :: [BS.VertexId]
   , constraintNumber           :: Int
   , varNumber                  :: Int
   }

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

addTermGraph :: Int -> T.Type -> TypeGraph info -> IO (Int, BS.VertexId, TypeGraph info)
addTermGraph unique (T.AliasN name _ realtype) grph = doAddTermGraph unique realtype grph (Just name)
addTermGraph unique tp grph = doAddTermGraph unique tp grph Nothing

-- TODO
doAddTermGraph :: Int -> T.Type -> TypeGraph info -> Maybe Var.Canonical -> IO (Int, BS.VertexId, TypeGraph info)
doAddTermGraph _ (T.PlaceHolder _) _ _ = error "doAddTermGraph PlaceHolder should have been flattened by now."
-- Type Variables, also contain atoms (var or con)
doAddTermGraph unique (T.VarN uc) grph mName = do
    desc <- UF.descriptor uc

    case T._content desc of
        T.Structure _ -> error "doAddTermGraph: Structure should not appear here"
        T.Alias {} -> error "doAddTermGraph: Alias should not appear here"
        T.Error -> error "doAddTermGraph: Error should not appear here. That's the constructor 'Type.Type.Error', not this actual error message."
        T.Atom name -> do -- Add con here
            let vid = BS.VertexId unique
            return (unique + 1, vid, addVertex vid (BS.VCon (Var.toString name), mName) grph)

        -- TODO: Check for existing variables?
        -- TODO: Super constraints (Number, Appendable, Comparable, CompAppend)
        T.Var {} -> do -- Add var here
            let idf = varNumber grph
            let vid = BS.VertexId idf
            let updGrph = grph {
                varNumber = idf + 1
            }
            return (unique, vid, {-if vertexExists vid stg then stg else-} addVertex vid (BS.VVar, mName) updGrph)



-- Type application (app)
doAddTermGraph unique (T.TermN (T.App1 l r)) grph mName = do
    (uql, vidl, gphl) <- addTermGraph unique l grph
    (uqr, vidr, gphr) <- addTermGraph uql r gphl

    let vid = BS.VertexId uqr
    let updGrph = addVertex vid (BS.VApp vidl vidr, mName) gphr

    return (uqr + 1, BS.VertexId uqr, updGrph)

-- Lambda function (con + app)
doAddTermGraph unique (T.TermN (T.Fun1 l r)) grph mName = do
    -- Add the function constructor to the graph
    let vid = BS.VertexId unique
    let (uq', vid', grph') = (unique + 1, vid, addVertex vid (BS.VCon "Function", mName) grph)

    -- Add the left type's subgraph
    (uql, vidl, gphl) <- addTermGraph uq' l grph'

    -- Add the application of the function to the left's type
    let appLVid = BS.VertexId uql
    let updGrphL = addVertex appLVid (BS.VApp vid' vidl, Nothing) gphl -- (Is it right to set the alias to Nothing?)
    let (uqAppL, vidAppL) = (uql + 1, BS.VertexId uql)

    -- Add the right type's subgraph
    (uqr, vidr, gphr) <- addTermGraph uqAppL r updGrphL

    -- Add the application of (VApp function l) to the right's type
    let appRVid = BS.VertexId uqr
    let updGrphR = addVertex appRVid (BS.VApp vidAppL vidr, Nothing) gphr -- (Is it right to set the alias to Nothing?)

    return (uqr + 1, BS.VertexId uqr, updGrphR)

-- Empty record (con)
doAddTermGraph unique (T.TermN T.EmptyRecord1) grph mName = do
    let vid = BS.VertexId unique
    return (unique + 1, vid, addVertex vid (BS.VCon "EmptyRecord", mName) grph)

-- Non-empty record, (con + app)
doAddTermGraph unique (T.TermN (T.Record1 subtypes emptyrecordType)) grph mName = undefined


-- | Add a vertex to the type graph
addVertex :: BS.VertexId -> BS.VertexInfo -> TypeGraph info -> TypeGraph info
addVertex v info =
      createGroup (EG.insertVertex v info EG.empty)


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

-- | Finds all the children in the equivalence group that contains the given VertexId
childrenInGroupOf :: BS.VertexId -> TypeGraph info -> ([CLQ.ParentChild], [CLQ.ParentChild])
childrenInGroupOf i graph =
      unzip [ ( CLQ.ParentChild { CLQ.parent = p, CLQ.child = t1, CLQ.childSide = CLQ.LeftChild  }
              , CLQ.ParentChild { CLQ.parent = p, CLQ.child = t2, CLQ.childSide = CLQ.RightChild }
              )
            | (p, (BS.VApp t1 t2, _)) <- verticesInGroupOf i graph
            ]
