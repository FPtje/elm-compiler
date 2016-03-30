{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
module Parse.Declaration where

import Text.Parsec ( (<|>), (<?>), choice, digit, optionMaybe, string, try, many, option )

import qualified AST.Declaration as D
import qualified AST.Type as T
import qualified AST.Interface as IF
import qualified Parse.Expression as Expr
import Parse.Helpers as Help
import qualified Parse.Type as Type
import qualified Text.Parsec.Indent as Indent

import Control.Monad (when)


declaration :: IParser D.SourceDecl
declaration =
  choice
    [ D.Comment <$> Help.docComment
    , D.Decl <$> addLocation (implementation <|> interface <|> typeDecl <|> infixDecl <|> port <|> sibling <|> definition)
    ]


-- TYPE ANNOTATIONS and DEFINITIONS

definition :: IParser D.SourceDecl'
definition =
  D.Definition
    <$> (Expr.typeAnnotation <|> Expr.definition)
    <?> "a value definition"


-- TYPE ALIAS and UNION TYPES

typeDecl :: IParser D.SourceDecl'
typeDecl =
  do  try (reserved "type") <?> "a type declaration"
      forcedWS
      isAlias <- optionMaybe (string "alias" >> forcedWS)

      name <- capVar
      args <- spacePrefix lowVar
      padded equals

      case isAlias of
        Just _ ->
            do  tipe <- Type.expr <?> "a type"
                return (D.TypeAlias name args tipe)

        Nothing ->
            do  tcs <- pipeSep1 Type.constructor <?> "a constructor for a union type"
                return $ D.Datatype name args tcs


-- INFIX

infixDecl :: IParser D.SourceDecl'
infixDecl =
  expecting "an infix declaration" $
  do  assoc <-
          choice
            [ try (reserved "infixl") >> return D.L
            , try (reserved "infixr") >> return D.R
            , try (reserved "infix")  >> return D.N
            ]
      forcedWS
      n <- digit
      forcedWS
      D.Fixity assoc (read [n]) <$> anyOp


-- PORT

port :: IParser D.SourceDecl'
port =
  expecting "a port declaration" $
  do  try (reserved "port")
      whitespace
      name <- lowVar
      whitespace
      choice [ portAnnotation name, portDefinition name ]
  where
    portAnnotation name =
      do  try hasType
          whitespace
          tipe <- Type.expr <?> "a type"
          return (D.Port (D.PortAnnotation name tipe))

    portDefinition name =
      do  try equals
          whitespace
          expr <- Expr.expr
          return (D.Port (D.PortDefinition name expr))

sibling :: IParser D.SourceDecl'
sibling =
  expecting "a sibling declaration" $
  do  try (reserved "sibling")
      forcedWS
      from <- (anyOp <|> qualifiedVar)
      forcedWS
      reserved "resembles"
      forcedWS
      to <- (anyOp <|> qualifiedVar)
      return $ D.Sibling from to

qualifier :: IParser (T.Qualifier' String String)
qualifier =
  expecting "an interface predicate" $ try $
  do  classnm <- capVar
      forcedWS
      vr <- lowVar
      return $ T.Qualifier classnm vr

interface :: IParser D.SourceDecl'
interface =
  expecting "an interface definition" $
  do  try (reserved "interface")
      forcedWS
      quals <- commaSep qualifier
      whitespace

      when (not . null $ quals) $ do
        rightDoubleArrow
        whitespace
        return ()

      ifName <- capVar

      forcedWS
      vr <- lowVar
      forcedWS
      reserved "describes"
      forcedWS

      Indent.withPos $
        do
          firstTp <- Expr.typeAnnotation
          otherTps <-
              many $ do
                try (whitespace >> Indent.checkIndent)
                Expr.typeAnnotation

          return . D.IFace $ IF.Interface quals ifName vr (firstTp : otherTps)

implementation :: IParser D.SourceDecl'
implementation =
  expecting "an implementation of an interface" $
  do  try (reserved "implement")
      forcedWS

      ifName <- capVar
      forcedWS

      reserved "for"
      forcedWS

      tp <- Type.expr
      forcedWS

      quals <- option [] $
        do try (reserved "assuming")
           forcedWS
           q <- commaSep1 qualifier
           forcedWS
           return q


      reserved "where"
      forcedWS

      Indent.withPos $
        do
          firstDcl <- Expr.definition
          otherDcls <-
              many $ do
                try (whitespace >> Indent.checkIndent)
                Expr.definition

          return . D.Impl $ IF.Implementation quals ifName tp (firstDcl : otherDcls)
