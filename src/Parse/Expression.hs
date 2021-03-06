module Parse.Expression (term, typeAnnotation, definition, expr, typerule) where

import qualified Data.List as List
import Text.Parsec hiding (newline, spaces)
import qualified Text.Parsec.Indent as Indent

import qualified Parse.Binop as Binop
import Parse.Helpers
import qualified Parse.Helpers as Help
import qualified Parse.Literal as Literal
import qualified Parse.Pattern as Pattern
import qualified Parse.Type as Type

import qualified AST.Expression.General as E
import qualified AST.Expression.Source as Source
import qualified AST.Literal as L
import qualified AST.Pattern as P
import qualified AST.Rule as R
import qualified AST.Variable as Var
import qualified Reporting.Annotation as A


--------  Basic Terms  --------

varTerm :: IParser Source.Expr'
varTerm =
  toVar <$> var


toVar :: String -> Source.Expr'
toVar v =
  case v of
    "True" ->
        E.Literal (L.Boolean True)

    "False" ->
        E.Literal (L.Boolean False)

    _ ->
        E.rawVar v


accessor :: IParser Source.Expr'
accessor =
  do  (start, lbl, end) <- located (try (string "." >> rLabel))

      let ann value =
            A.at start end value

      return $
        E.Lambda
            (ann (P.Var "_"))
            (ann (E.Access (ann (E.rawVar "_")) lbl))


negative :: IParser Source.Expr'
negative =
  do  (start, nTerm, end) <-
          located $ try $
            do  char '-'
                notFollowedBy (char '.' <|> char '-')
                term

      let ann e =
            A.at start end e

      return $
        E.Binop
          (Var.Raw "-")
          (ann (E.Literal (L.IntNum 0)))
          nTerm


--------  Complex Terms  --------

listTerm :: IParser Source.Expr'
listTerm =
    shader' <|> braces (try range <|> E.ExplicitList <$> commaSep expr)
  where
    range =
      do  lo <- expr
          padded (string "..")
          E.Range lo <$> expr

    shader' =
      do  pos <- getPosition
          let uid = show (sourceLine pos) ++ ":" ++ show (sourceColumn pos)
          (rawSrc, tipe) <- Help.shader
          return $ E.GLShader uid (filter (/='\r') rawSrc) tipe


parensTerm :: IParser Source.Expr
parensTerm =
  let
    mkFunc args realBody start end =
      foldr
        (\arg body -> A.at start end (E.Lambda (A.at start end (P.Var arg)) body))
        (A.at start end (realBody (A.at start end . E.rawVar)))
        args

    mkBinop op =
      mkFunc ["x","y"] (\var -> E.Binop (Var.Raw op) (var "x") (var "y"))

    tupleFn =
      do  commas <- many1 comma
          let args = map (('v':) . show) [ 0 .. length commas ]
          return $ mkFunc args (\var -> E.tuple (map var args))

    parenedExpr =
      do  expressions <- padded (commaSep expr)
          return $ \start end ->
              case expressions of
                [expression] ->
                    expression
                _ ->
                    A.at start end (E.tuple expressions)
  in
    do  (start, mkExpr, end) <-
          located $ choice $
            [ mkBinop <$> try (parens symOp)
            , parens (tupleFn <|> parenedExpr)
            ]
        return (mkExpr start end)



recordTerm :: IParser Source.Expr
recordTerm =
  addLocation $ brackets $ choice $
    [ do  starter <- try (addLocation rLabel)
          whitespace
          choice
            [ update starter
            , literal starter
            ]
    , return (E.Record [])
    ]
  where
    update (A.A ann starter) =
      do  try (string "|")
          whitespace
          fields <- commaSep1 field
          return (E.Update (A.A ann (E.rawVar starter)) fields)

    literal (A.A _ starter) =
      do  try equals
          whitespace
          value <- expr
          whitespace
          choice
            [ do  try comma
                  whitespace
                  fields <- commaSep field
                  return (E.Record ((starter, value) : fields))
            , return (E.Record [(starter, value)])
            ]

    field =
      do  key <- rLabel
          padded equals
          value <- expr
          return (key, value)


term :: IParser Source.Expr
term =
  addLocation (choice [ E.Literal <$> Literal.literal, listTerm, accessor, negative ])
    <|> accessible (addLocation varTerm <|> parensTerm <|> recordTerm)
    <?> "an expression"


--------  Applications  --------

appExpr :: IParser Source.Expr
appExpr =
  expecting "an expression" $
  do  t <- term
      ts <- constrainedSpacePrefix term $ \str ->
                if null str then notFollowedBy (char '-') else return ()
      return $
          case ts of
            [] -> t
            _  -> List.foldl' (\f x -> A.merge f x $ E.App f x) t ts


--------  Normal Expressions  --------

expr :: IParser Source.Expr
expr =
  addLocation (choice [ letExpr, caseExpr, ifExpr ])
    <|> lambdaExpr
    <|> binaryExpr
    <?> "an expression"


binaryExpr :: IParser Source.Expr
binaryExpr =
    Binop.binops appExpr lastExpr anyOp
  where
    lastExpr =
        addLocation (choice [ letExpr, caseExpr, ifExpr ])
        <|> lambdaExpr
        <?> "an expression"


ifExpr :: IParser Source.Expr'
ifExpr =
  ifHelp []


ifHelp :: [(Source.Expr, Source.Expr)] -> IParser Source.Expr'
ifHelp branches =
  do  try (reserved "if")
      whitespace
      condition <- expr
      padded (reserved "then")
      thenBranch <- expr
      whitespace <?> "an 'else' branch"
      reserved "else" <?> "an 'else' branch"
      whitespace
      let newBranches = (condition, thenBranch) : branches
      choice
        [ ifHelp newBranches
        , E.If (reverse newBranches) <$> expr
        ]


lambdaExpr :: IParser Source.Expr
lambdaExpr =
  do  start <- getMyPosition
      char '\\' <|> char '\x03BB' <?> "an anonymous function"
      whitespace
      args <- spaceSep1 Pattern.term
      padded rightArrow
      body <- expr
      end <- getMyPosition
      return (foldr (\a b -> A.at start end $ E.Lambda a b) body args)


caseExpr :: IParser Source.Expr'
caseExpr =
  do  try (reserved "case")
      exp <- padded expr
      reserved "of"
      whitespace
      Indent.withPos $
        do  firstBranch <- branch
            branches <-
                many $ do
                  try (whitespace >> Indent.checkIndent)
                  branch
            return $ E.Case exp (firstBranch : branches)
  where
    branch =
      do  p <- Pattern.expr
          padded rightArrow
          (,) p <$> expr


-- LET

letExpr :: IParser Source.Expr'
letExpr =
  do  try (reserved "let")
      whitespace
      defs <-
        Indent.block $
          do  def <- typeAnnotation <|> definition
              whitespace
              return def
      padded (reserved "in")
      E.Let defs <$> expr

-- TYPE ANNOTATION

typeAnnotation :: IParser Source.Def
typeAnnotation =
    addLocation (Source.TypeAnnotation <$> try start <*> Type.annotatedExpr)
  where
    start =
      do  v <- lowVar <|> parens symOp
          padded hasType
          return v


-- DEFINITION

definition :: IParser Source.Def
definition =
  addLocation $
  Indent.withPos $
    do  (name, args) <- defStart
        padded equals
        body <- expr
        return . Source.Definition name $ makeFunction args body


typeRuleFunc :: IParser [P.RawPattern]
typeRuleFunc =
  expecting "A function pattern" $
  do
    funcname <-addLocation $ P.Var <$> (var <|> parens symOp)
    args <- spacePrefix (addLocation $ P.Var <$> lowVar)

    return $ funcname : args


subErrorTypeRule :: IParser R.SourceRule
subErrorTypeRule = addLocation $
  do
    try (reserved "constrain")
    forcedWS
    v <- lowVar
    return $ R.SubRule v


qualifierRule :: IParser R.SourceRule
qualifierRule = addLocation $
  do
    try (reserved "check")
    forcedWS
    qual <- Type.qualifier

    explanation <- optionMaybe $ do
        try (forcedWS >> reserved "because")
        forcedWS

        anyUntil $ simpleNewline <|> (eof >> return "")

    return $ R.Qualifier qual explanation

constraintTypeRule :: IParser R.SourceRule
constraintTypeRule = addLocation $
  do
    reserved "unify"
    forcedWS
    v <- lowVar
    forcedWS
    reserved "with"
    forcedWS
    tp <- Type.annotatedExpr

    explanation <- optionMaybe $ do
        try (forcedWS >> reserved "because")
        forcedWS

        anyUntil $ simpleNewline <|> (eof >> return "")

    return $ R.Constraint v tp explanation

typeRuleConstr :: IParser R.SourceRule
typeRuleConstr =
  expecting "An error description" $
  subErrorTypeRule <|> constraintTypeRule <|> qualifierRule

typerule :: IParser Source.Def
typerule = addLocation $
  expecting "A description of errors" $
  do
      try (reserved "errors")
      forcedWS
      reserved "for"
      forcedWS
      pats <- typeRuleFunc
      forcedWS
      reserved "where"
      forcedWS

      Indent.withPos $
        do
          firstRule <- typeRuleConstr
          otherRules <-
              many $ do
                try (whitespace >> Indent.checkIndent)
                typeRuleConstr

          return $ Source.TypeRule pats (firstRule : otherRules)


makeFunction :: [P.RawPattern] -> Source.Expr -> Source.Expr
makeFunction args body@(A.A ann _) =
    foldr (\arg body' -> A.A ann $ E.Lambda arg body') body args


defStart :: IParser (P.RawPattern, [P.RawPattern])
defStart =
  expecting "the definition of a value (x = ...)" $
    do  starter <- try Pattern.term <|> addLocation (P.Var <$> parens symOp)
        args <- spacePrefix Pattern.term
        return (starter, args)
