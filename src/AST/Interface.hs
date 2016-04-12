module AST.Interface where

import qualified AST.Type as Type
import qualified AST.Expression.Source as Source
import qualified AST.Variable as Var
import qualified AST.Expression.Canonical as Canonical

data Interface' classref var decl
    = Interface
        { ifquals :: [Type.Qualifier' classref var]
        , classname :: classref
        , interfacevar :: var
        , decls :: [decl]
        }

data Implementation' classref var tipe def
    = Implementation
        { implquals :: [Type.Qualifier' classref var]
        , classref :: classref
        , impltype :: tipe
        , implementations :: [def]
        }

type SourceInterface
    = Interface' String String Source.Def'

type SourceImplementation
    = Implementation' String String Type.Raw Source.Def'

type CanonicalInterface
    = Interface' Var.Canonical Type.Canonical Canonical.InterfaceFunction

type CanonicalImplementation
    = Implementation' Var.Canonical Type.Canonical Type.Canonical Canonical.Def
