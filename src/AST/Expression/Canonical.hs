{-# OPTIONS_GHC -Wall #-}
module AST.Expression.Canonical where

import qualified AST.Expression.General as General
import qualified AST.Pattern as Pattern
import qualified AST.Type as Type
import qualified AST.Rule as Rule
import qualified AST.Variable as Var
import qualified Reporting.Annotation as A
import qualified Reporting.Region as R
import qualified Data.Map as Map


{-| Canonicalized expressions. All variables are fully resolved to the module
they came from.
-}
type Expr =
  General.Expr R.Region Def Var.Canonical Type.Canonical'


type Expr' =
  General.Expr' R.Region Def Var.Canonical Type.Canonical'

data TypeRule = TypeRule [Pattern.CanonicalPattern] [Rule.CanonicalRule] (Map.Map String Int)
    deriving (Show)

data Def
    = Definition Facts Pattern.CanonicalPattern Expr (Maybe (A.Located Type.Canonical)) (Maybe (A.Located Type.Canonical)) [TypeRule]
    deriving (Show)


data Facts = Facts
    { dependencies :: [Var.TopLevel]
    }

instance Show Facts where
    show _ = "Facts"

data InterfaceFunction = InterfaceFunction Var.Canonical (A.Located Type.Canonical)
    deriving (Show)

dummyFacts :: Facts
dummyFacts =
  Facts (error "This should be set by Canonicalize.Sort")

