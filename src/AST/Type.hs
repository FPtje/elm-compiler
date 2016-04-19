module AST.Type
    ( Raw, Raw', Raw''(..)
    , Qualifier'(..)
    , Canonical, Canonical'(..), Aliased(..)
    , QualifiedType(..)
    , Port(..), getPortType
    , deepDealias, iteratedDealias, dealias
    , collectLambdas, collectLambdas'
    , tuple
    , substitute, substitute'
    , unqualified
    , addQualifiers
    ) where

import Control.Arrow (second)
import Data.Binary
import qualified Data.Map as Map

import qualified AST.Variable as Var
import qualified Reporting.Annotation as A
import qualified Reporting.Region as R



-- DEFINITION

type Raw =
    QualifiedType (A.Located String) String Raw'

type Raw' =
    A.Located Raw''

data QualifiedType classref var tipe
    = QT
      { qualifiers :: [Qualifier' classref var]
      , qtype :: tipe
      }
    deriving (Eq, Ord, Show)

data Raw''
    = RLambda Raw' Raw'
    | RVar String
    | RType Var.Raw
    | RApp Raw' [Raw']
    | RRecord [(String, Raw')] (Maybe Raw')
    deriving (Eq, Ord)


type Canonical =
    QualifiedType Var.Canonical Canonical' Canonical'

data Canonical'
    = Lambda Canonical' Canonical'
    | Var String
    | Type Var.Canonical
    | App Canonical' [Canonical']
    | Record [(String, Canonical')] (Maybe Canonical')
    | Aliased Var.Canonical [(String, Canonical')] (Aliased Canonical')
    deriving (Eq, Ord, Show)

data Qualifier' classref var
    = Qualifier classref var
    deriving (Eq, Ord, Show)

data Aliased t
    = Holey t
    | Filled t
    deriving (Eq, Ord, Show)


data Port t
    = Normal t
    | Signal { root :: t, arg :: t }
    deriving (Eq)

instance Functor (QualifiedType classref var) where
  fmap f (QT quals tipe) = QT quals (f tipe)


getPortType :: Port tipe -> tipe
getPortType portType =
  case portType of
    Normal tipe -> tipe
    Signal tipe _ -> tipe

addQualifiers :: QualifiedType classref var tp -> [Qualifier' classref var] -> QualifiedType classref var tp
addQualifiers (QT qs tp) moreqs = QT (moreqs ++ qs) tp

tuple :: R.Region -> [Raw'] -> Raw'
tuple region types =
  let name = Var.Raw ("_Tuple" ++ show (length types))
  in
      A.A region (RApp (A.A region (RType name)) types)


unqualified :: tipe -> QualifiedType classref var tipe
unqualified = QT []

-- DEALIASING

deepDealias :: Canonical -> Canonical
deepDealias = fmap deepDealiasHelp

deepDealiasHelp :: Canonical' -> Canonical'
deepDealiasHelp tipe =
  case tipe of
    Lambda a b ->
          Lambda (deepDealiasHelp a) (deepDealiasHelp b)

    Var _ ->
        tipe

    Record fields ext ->
        Record (map (second deepDealiasHelp) fields) (fmap deepDealiasHelp ext)

    Aliased _name args tipe' ->
        deepDealiasHelp (dealias args tipe')

    Type _ ->
        tipe

    App f args ->
        App (deepDealiasHelp f) (map deepDealiasHelp args)



iteratedDealias :: Canonical -> Canonical
iteratedDealias = fmap iteratedDealiasHelp

iteratedDealiasHelp :: Canonical' -> Canonical'
iteratedDealiasHelp tipe =
  case tipe of
    Aliased _ args realType ->
        iteratedDealiasHelp (dealias args realType)

    _ ->
        tipe


dealias :: [(String, Canonical')] -> Aliased Canonical' -> Canonical'
dealias args aliasType =
  case aliasType of
    Holey tipe ->
        dealiasHelp (Map.fromList args) tipe

    Filled tipe ->
        tipe


dealiasHelp :: Map.Map String Canonical' -> Canonical' -> Canonical'
dealiasHelp typeTable tipe =
    let go = dealiasHelp typeTable in
    case tipe of
      Lambda a b ->
          Lambda (go a) (go b)

      Var x ->
          Map.findWithDefault tipe x typeTable

      Record fields ext ->
          Record (map (second go) fields) (fmap go ext)

      Aliased original args t' ->
          Aliased original (map (second go) args) t'

      Type _ ->
          tipe

      App f args ->
          App (go f) (map go args)

-- only substitutes variables for now
substitute :: Canonical' -> Canonical' -> Canonical -> Canonical
substitute v withThis (QT quals inThis) =
    QT quals $ substitute' v withThis inThis

substitute' :: Canonical' -> Canonical' -> Canonical' -> Canonical'
substitute' v@(Var thing) withThis inThis =
  let
    rec = substitute' v withThis
    maprec = map (second rec)
  in

    case inThis of
      Lambda from to -> Lambda (rec from) (rec to)
      Var name -> if name == thing then withThis else Var name
      Type name -> Type name
      App func args -> App (rec func) (map rec args)
      Record members baseRecord -> Record (maprec members) (fmap rec baseRecord)
      Aliased name things (Holey base) -> Aliased name (maprec things) (Holey (rec base))
      Aliased name things (Filled base) -> Aliased name (maprec things) (Filled (rec base))
substitute' _ _ _ = error "Substitution for non-Vars not implemented"

-- COLLECT LAMBDAS


collectLambdas :: Canonical -> [Canonical']
collectLambdas = collectLambdas' . qtype

collectLambdas' :: Canonical' -> [Canonical']
collectLambdas' tipe =
  case tipe of
    Lambda arg result ->
        arg : collectLambdas' result

    _ ->
        [tipe]



-- BINARY

instance (Binary classref, Binary var) => Binary (Qualifier' classref var) where
  put (Qualifier classref var) = put classref >> put var

  get = Qualifier <$> get <*> get

instance (Binary classref, Binary var, Binary tipe) => Binary (QualifiedType classref var tipe) where
  put (QT qs qtp) = put qs >> put qtp
  get = QT <$> get <*> get


instance Binary Canonical' where
  put tipe =
      case tipe of
        Lambda t1 t2 ->
            putWord8 0 >> put t1 >> put t2

        Var x ->
            putWord8 1 >> put x

        Type name ->
            putWord8 2 >> put name

        App t1 t2 ->
            putWord8 3 >> put t1 >> put t2

        Record fs ext ->
            putWord8 4 >> put fs >> put ext

        Aliased var args t ->
            putWord8 5 >> put var >> put args >> put t

  get = do
      n <- getWord8
      case n of
        0 -> Lambda <$> get <*> get
        1 -> Var <$> get
        2 -> Type <$> get
        3 -> App <$> get <*> get
        4 -> Record <$> get <*> get
        5 -> Aliased <$> get <*> get <*> get
        _ -> error "Error reading a valid type from serialized string"


instance Binary t => Binary (Aliased t) where
  put aliasType =
      case aliasType of
        Holey tipe ->
            putWord8 0 >> put tipe

        Filled tipe ->
            putWord8 1 >> put tipe

  get = do
      n <- getWord8
      case n of
        0 -> Holey <$> get
        1 -> Filled <$> get
        _ -> error "Error reading a valid type from serialized string"
