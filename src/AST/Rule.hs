module AST.Rule where
import qualified AST.Type as Type
import qualified AST.Variable as Var

import qualified Reporting.Annotation as A

data TypeRule' classref qualtipe var tp
    = SubRule var
    | Constraint { lhs :: var, rhs :: tp, explanation :: Maybe String }
    | Qualifier { rqual :: Type.Qualifier' classref qualtipe, explanation :: Maybe String }
    deriving (Show)

type TypeRule classref qualtipe var tp = A.Located (TypeRule' classref qualtipe var tp)

type SourceRule = TypeRule (A.Located String) String String Type.Raw
type SourceRule' = TypeRule' (A.Located String) String String Type.Raw

type ValidRule = TypeRule (A.Located Var.Raw) Var.Raw Var.Raw Type.Raw
type ValidRule' = TypeRule' (A.Located Var.Raw) Var.Raw Var.Raw Type.Raw

type CanonicalRule = TypeRule Var.Canonical Type.Canonical' Var.Canonical Type.Canonical
type CanonicalRule' = TypeRule' Var.Canonical Type.Canonical' Var.Canonical Type.Canonical
