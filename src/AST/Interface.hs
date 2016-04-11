module AST.Interface where

import qualified AST.Type as Type
import qualified AST.Expression.Source as Source
import qualified AST.Variable as Var
import qualified AST.Expression.Canonical as Canonical

data Interface' classref var decl
    = Interface [Type.Qualifier' classref var] classref var [decl]

data Implementation' classref var tipe def
    = Implementation [Type.Qualifier' classref var] classref tipe [def]

type SourceInterface
    = Interface' String String Source.Def'

type SourceImplementation
    = Implementation' String String Type.Raw Source.Def'

type CanonicalInterface
    = Interface' Var.Canonical Type.Canonical Canonical.InterfaceFunction

type CanonicalImplementation
    = Implementation' Var.Canonical Type.Canonical Type.Canonical Canonical.Def
