module Type.Inference where

import Control.Arrow (first, second)
import Control.Monad.Except (Except, forM, liftIO, runExceptT, throwError)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as Traverse

import qualified AST.Interface as Interface
import AST.Module as Module
import qualified AST.Module.Name as ModuleName
import qualified AST.Type as Type
import qualified AST.Variable as Var
import qualified AST.Expression.Canonical as Canonical
import qualified Reporting.Annotation as A
import qualified Reporting.Error.Type as Error
import qualified Reporting.Region as R
import qualified Type.Constrain.Expression as TcExpr
import qualified Type.Environment as Env
import qualified Type.Solve as Solve
import qualified Type.State as TS
import qualified Type.Type as T
import Control.Monad.Except (ExceptT)

import System.IO.Unsafe
    -- Maybe possible to switch over to ST instead of IO.
    -- I don't think that'd be worthwhile though.


infer
    :: Module.Interfaces
    -> Module.CanonicalModule
    -> Except [A.Located Error.Error] (Map.Map String Type.Canonical)
infer interfaces modul =
  either throwError return $ unsafePerformIO $ runExceptT $
    do  (header, constraint) <-
            liftIO (genConstraints interfaces modul)

        let sibs = Module.siblings . Module.body $ modul
        state <- Solve.solve constraint sibs (Module.implementations . Module.body $ modul)

        let header' = Map.delete "::" header
        let types = Map.map A.drop (Map.difference (TS.sSavedEnv state) header')

        typeMap <- liftIO (Traverse.traverse T.toSrcType (Map.map A.drop (TS.sSavedEnv state)))

        checkSiblings typeMap sibs

        liftIO (Traverse.traverse T.toSrcType types)

-- | When creating a sibling that states that function f is similar to function g,
-- f and g cannot have the exact same type. After all, if f is involved in a type error,
-- you can be sure that g won't fix that type error if it has the exact same type
checkSiblings :: Map.Map String Type.Canonical -> Module.Siblings -> ExceptT [A.Located Error.Error] IO ()
checkSiblings typeMap sibs =
  let
    sibList :: [(Module.Sibling, [Module.Sibling])]
    sibList = Map.toList (Map.map Set.toList (snd sibs))
  in
    mapM_ (uncurry (checkSibling typeMap (fst sibs))) sibList

checkSibling :: Map.Map String Type.Canonical -> Map.Map (Sibling, Sibling) R.Region -> Module.Sibling -> [Module.Sibling] -> ExceptT [A.Located Error.Error] IO ()
checkSibling typeMap rgs sib sibs =
  mapM_ (checkSiblingHelper typeMap rgs sib) sibs

checkSiblingHelper :: Map.Map String Type.Canonical -> Map.Map (Sibling, Sibling) R.Region -> Module.Sibling -> Module.Sibling -> ExceptT [A.Located Error.Error] IO ()
checkSiblingHelper typeMap rgs left right =
  do
    let leftVar = Var.toString left
    let rightVar = Var.toString right
    let leftType = Map.findWithDefault (error "checkSiblingHelper: existence check already passed") leftVar typeMap
    let rightType = Map.findWithDefault (error "checkSiblingHelper: existence check already passed") rightVar typeMap
    let sibRegion = Map.findWithDefault (error "Could not find sibling location") (left, right) rgs

    if (leftType == rightType)
      then throwError [A.A sibRegion (Error.SameTypeSibling sibRegion left right)]
      else return ()

genConstraints
    :: Module.Interfaces
    -> Module.CanonicalModule
    -> IO (Map.Map String T.Type, T.TypeConstraint)
genConstraints interfaces modul =
  do  env <- Env.initialize (canonicalizeAdts interfaces modul)

      ctors <-
          forM (Env.ctorNames env) $ \name ->
            do  (_, vars, args, result) <- Env.freshDataScheme env name
                return (name, (vars, Type.unqualified $ foldr (T.==>|) result args))

      importedVars <-
          mapM (canonicalizeValues env) (Map.toList interfaces)

      let allTypes = concat (ctors : importedVars)
      let vars = concatMap (fst . snd) allTypes
      let header = Map.map snd (Map.fromList allTypes)
      let environ = T.CLet [ T.Scheme vars [] T.CTrue (Map.map (A.A undefined) header) ]

      fvar <- T.mkVar Nothing

      constraint <-
          TcExpr.constrain env (program (body modul)) (Type.unqualified $ T.VarN fvar)

      return (header, environ constraint)

canonicalizeValues
    :: Env.Environment
    -> (ModuleName.Canonical, Interface)
    -> IO [(String, ([T.Variable], T.Type))]
canonicalizeValues env (moduleName, iface) =
    forM (Map.toList (iTypes iface)) $ \(name,tipe) ->
        do  tipe' <- Env.instantiateType env tipe Map.empty
            return
              ( ModuleName.canonicalToString moduleName ++ "." ++ name
              , tipe'
              )


canonicalizeAdts :: Module.Interfaces -> Module.CanonicalModule -> [CanonicalAdt]
canonicalizeAdts interfaces modul =
    localAdts ++ importedAdts
  where
    localAdts :: [CanonicalAdt]
    localAdts =
      format (Module.name modul, datatypes (body modul))

    importedAdts :: [CanonicalAdt]
    importedAdts =
      concatMap (format . second iAdts) (Map.toList interfaces)


format :: (ModuleName.Canonical, Module.ADTs) -> [CanonicalAdt]
format (home, adts) =
    map canonical (Map.toList adts)
  where
    canonical :: (String, AdtInfo String) -> CanonicalAdt
    canonical (name, (tvars, ctors)) =
        ( toVar name
        , (tvars, map (first toVar) ctors)
        )

    toVar :: String -> Var.Canonical
    toVar name =
        Var.fromModule home name
