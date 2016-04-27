module AST.Rule where
import qualified AST.Type as Type
import qualified AST.Variable as Var

import qualified Reporting.Annotation as A

data TypeRule' var tp
    = SubRule var
    | Constraint { lhs :: var, rhs :: tp, explanation :: String }

type TypeRule var tp = A.Located (TypeRule' var tp)

type SourceRule = TypeRule String Type.Raw'

type ValidRule = TypeRule Var.Raw Type.Raw'

type CanonicalRule = TypeRule Var.Canonical Type.Canonical'
