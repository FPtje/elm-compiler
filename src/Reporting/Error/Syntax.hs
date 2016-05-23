{-# OPTIONS_GHC -Wall #-}
module Reporting.Error.Syntax where

import qualified Data.List as List
import qualified Data.Set as Set
import qualified Text.Parsec.Error as Parsec
import Text.PrettyPrint.ANSI.Leijen (dullyellow, hsep, text)

import qualified Reporting.Error.Helpers as Help
import qualified Reporting.Render.Type as RenderType
import qualified Reporting.Report as Report


data Error
    = Parse [Parsec.Message]
    | BadFunctionName Int
    | BadPattern String
    | InfixDuplicate String
    | TypeWithoutDefinition String
    | TypeRuleNotBetweenTypeAndDef String
    | TypeRuleDuplicate
    | TypeRuleNotTopLevel
    | TypeRuleMissingArgs [String]
    | TypeRuleDuplicateSubRule String
    | PortWithoutAnnotation String
    | UnexpectedPort
    | DuplicateFieldName String
    | DuplicateValueDeclaration String
    | DuplicateTypeDeclaration String
    | DuplicateSiblingDeclaration String
    | DuplicateDefinition String
    | UnboundTypeVarsInUnion String [String] [String]
    | UnboundTypeVarsInAlias String [String] [String]
    | UnusedTypeVarsInAlias String [String] [String]
    | MessyTypeVarsInAlias String [String] [String] [String]
    | MessyTypeVarsInInterface String String String String


-- TO REPORT

toReport :: RenderType.Localizer -> Error -> Report.Report
toReport _localizer err =
  case err of
    Parse messages ->
        parseErrorReport messages

    BadFunctionName arity ->
        Report.report
          "BAD FUNCTION DEFINITION"
          Nothing
          "Complex patterns cannot be used as function names."
          ( Help.reflowParagraph $
              "This function definition has " ++ show arity ++ " arguments, but instead\
              \ of a normal name like `add` or `reverse` it has a pattern. There is no\
              \ way to \"deconstruct\" a function with pattern matching, so this needs to\
              \ be changed to a normal name."
          )

    BadPattern name ->
        Report.report
          "BAD PATTERN"
          Nothing
          ("The free variable `" ++ name ++ "` appears more than once in this pattern.")
          ( Help.stack
              [ text "Rename the variables so there are no duplicates."
              , Help.reflowParagraph $
                  "In Elm, pattern matching works by binding these free variables to subsections\
                  \ of the matching value. It does not make sense to have the same name for two\
                  \ different subsections though! When you say `" ++ name ++ "` in some code, there\
                  \ is no way for me to know which subsection you mean!"
              ]
          )

    InfixDuplicate opName ->
        Report.report
          "INFIX OVERLAP"
          Nothing
          ("The infix declarations for " ++ Help.functionName opName ++ " must be removed.")
          ( Help.reflowParagraph $
              "The precedence and associativity of a particular operator can only be set in\
              \ one place in a code base, and " ++ Help.functionName opName
              ++ " has already been set somewhere else."
          )

    TypeWithoutDefinition valueName ->
        Report.report
          "MISSING DEFINITION"
          Nothing
          ("There is a type annotation for `" ++ valueName ++ "` but there"
            ++ " is no corresponding definition!"
          )
          ( text $
              "Directly below the type annotation, put a definition like:\n\n"
              ++ "    " ++ valueName ++ " = 42"
          )

    TypeRuleNotBetweenTypeAndDef valueName ->
        Report.report
          "MISPLACED ERROR RULES"
          Nothing
          ("The errors for `" ++ valueName ++ "` are not placed between a type signature"
            ++ " and definition!"
          )
          ( text $
              "Error rules should be placed between the type annotation of a function\n"
              ++ "and its definition, like this:\n"
              ++ valueName ++ " : ...\n"
              ++ "errors for " ++ valueName ++ " ... where\n"
              ++ "    ...\n\n"
              ++ valueName ++ " = ..."
          )

    TypeRuleDuplicate ->
        Report.report
          "DUPLICATE SET OF ERRORS"
          Nothing
          ("Multiple sets of errors are defined for the same function with the same amount of arguments"
          )
          ( text $
              "A function with n parameters can have n + 1 sets of errors. " ++
              "One for when the function is given 0 arguments, one for when the function is given 1 argument etc.\n" ++
              "One cannot make two sets of errors for a function with the same amount of arguments, " ++
              "because then we wouldn't know which error to throw when the user does something wrong."
          )

    TypeRuleNotTopLevel ->
        Report.report
          "MISPLACED ERROR RULES"
          Nothing
          ("Error rules can only defined on the top level."
          )
          ( text $
              "Error rules customise the errors of functions for when they are used incorrectly.\n"
              ++ "It only makes sense for them to exist globally, because that is when other people use it."
          )

    TypeRuleMissingArgs args ->
        Report.report
          "MISSING UNIFY RULES"
          Nothing
          ("The set of type rules lacks rules about some arguments and/or the return type."
          )
          ( text $
              (List.intercalate ", " (map (\c -> "'" ++ c ++ "'") args)) ++ " must appear at least once on the left hand side of a unify rule."
          )

    TypeRuleDuplicateSubRule subrule ->
        Report.report
          "DUPLICATE CONSTRAIN RULES"
          Nothing
          ("The constrain rule for `" ++ subrule ++ "` is mentioned multiple times"
          )
          ( text $
              "The arguments and return value need only be constrained once at most."
          )

    PortWithoutAnnotation portName ->
        Report.report
          "PORT ERROR"
          Nothing
          ("Port `" ++ portName ++ "` does not have a type annotation!")
          ( text $
              "Directly above the port definition, I need something like this:\n\n"
              ++ "    port " ++ portName ++ " : Signal Int"
          )


    UnexpectedPort ->
        Report.report
          "PORT ERROR"
          Nothing
          "This module has ports, but ports can only appear in the main module."
          ( Help.reflowParagraph $
              "Ports in library code would create hidden dependencies where importing a\
              \ module could bring in constraints not captured in the public API. Furthermore,\
              \ if the module is imported twice, do we send values out the port twice?"
          )

    DuplicateFieldName name ->
        Report.report
          "DUPLICATE FIELD"
          Nothing
          ("This record has more than one field named `" ++ name ++ "`.")
          (text "There can only be one. Do some renaming to make sure the names are distinct!")

    DuplicateValueDeclaration name ->
        Report.report
          "DUPLICATE DEFINITION"
          Nothing
          ( "Naming multiple top-level values `" ++ name ++ "` makes things\n"
            ++ "ambiguous. When you say `" ++ name ++ "` which one do you want?"
          )
          ( Help.reflowParagraph $
              "Find all the top-level values named " ++ Help.functionName name
              ++ " and do some renaming. Make sure the names are distinct!"
          )

    DuplicateTypeDeclaration name ->
        Report.report
          "DUPLICATE DEFINITION"
          Nothing
          ( "There are multiple types named `" ++ name ++ "` in this module."
          )
          ( Help.reflowParagraph $
              "Search through this module, find all the types named `" ++ name
              ++ "`, and give each of them a unique name."
          )

    DuplicateSiblingDeclaration sibling ->
        Report.report
          "DUPLICATE DEFINITION"
          Nothing
          ( "There are multiple sibling that state that " ++ sibling ++ " in this module."
          )
          ( Help.reflowParagraph $
              "Search through this module, find all siblings that say " ++ sibling
              ++ " and remove all but one of them."
          )

    DuplicateDefinition name ->
        Report.report
          "DUPLICATE DEFINITION"
          Nothing
          ("There are multiple values named `" ++ name ++ "` in this let-expression."
          )
          ( Help.reflowParagraph $
              "Search through this let-expression, find all the values named `" ++ name
              ++ "`, and give each of them a unique name."
          )

    UnboundTypeVarsInUnion typeName givenVars unbound ->
        unboundTypeVars "type" typeName givenVars unbound

    UnboundTypeVarsInAlias typeName givenVars unbound ->
        unboundTypeVars "type alias" typeName givenVars unbound

    UnusedTypeVarsInAlias typeName givenVars unused ->
        Report.report
          "UNUSED TYPE VARIABLES"
          Nothing
          ( "Type alias `" ++ typeName ++ "` cannot have unused type variables: "
            ++ Help.commaSep unused
          )
          ( Help.stack
              [ text "You probably need to change the declaration like this:"
              , dullyellow $ hsep $
                  map text ("type" : "alias" : typeName : filter (`notElem` unused) givenVars ++ ["=", "..."])
              ]
          )

    MessyTypeVarsInAlias typeName givenVars unused unbound ->
        Report.report
          "TYPE VARIABLE PROBLEMS"
          Nothing
          ( "Type alias `" ++ typeName ++ "` has some problems with type variables."
          )
          ( Help.stack
              [ Help.reflowParagraph $
                  "The declaration says it uses certain type variables ("
                  ++ Help.commaSep unused ++ ") but they do not appear in the aliased type. "
                  ++ "Furthermore, the aliased type says it uses type variables ("
                  ++ Help.commaSep unbound
                  ++ ") that do not appear in the declaration."
              , text "You probably need to change the declaration like this:"
              , dullyellow $ hsep $
                  map text ("type" : "alias" : typeName : filter (`notElem` unused) givenVars ++ unbound ++ ["=", "..."])
              ]
          )

    MessyTypeVarsInInterface ifaceNm clsNm qualVar actualVar ->
        Report.report
          "INTERFACE TYPE VARIABLE PROBLEMS"
          Nothing
          ( "Interface `" ++ ifaceNm ++ "` has some problems with its qualifiers."
          )
          ( Help.stack
              [ Help.reflowParagraph $
                  "The interface says it requires a ("
                  ++ clsNm ++ " " ++ qualVar ++ ", but " ++ qualVar ++ " does not exist in the interface. "
                  ++ "The only type variable that exists in the interface is " ++ actualVar
              ]
          )


unboundTypeVars :: String -> String -> [String] -> [String] -> Report.Report
unboundTypeVars declKind typeName givenVars unboundVars@(tvar:_) =
  Report.report
    "UNBOUND TYPE VARIABLES"
    Nothing
    ( Help.capitalize declKind ++ " `" ++ typeName ++ "` must declare its use of type variable"
      ++ Help.commaSep unboundVars
    )
    ( Help.stack
        [ text "You probably need to change the declaration like this:"
        , hsep $
            map text (declKind : typeName : givenVars)
            ++ map (dullyellow . text) unboundVars
            ++ map text ["=", "..."]
        , Help.reflowParagraph $
            "Here's why. Imagine one `" ++ typeName ++ "` where `" ++ tvar ++ "` is an Int and\
            \ another where it is a Bool. When we explicitly list the type variables, type\
            \ checker can see that they are actually different types."
        ]
    )



-- TAGGING PARSE ERRORS


newline :: String
newline = "NEWLINE"


freshLine :: String
freshLine = "FRESH_LINE"


whitespace :: String
whitespace = "WHITESPACE"


tab :: String
tab = "TAB"


keyword :: String -> String
keyword kwd =
  "KEYWORD=" ++ kwd


data SpecialMessage
  = MsgKeyword String
  | MsgTab


extractSpecialMessage :: String -> Maybe SpecialMessage
extractSpecialMessage message =
  if List.isPrefixOf "KEYWORD=" message then
      Just $ MsgKeyword (drop (length "KEYWORD=") message)

  else if tab == message then
      Just MsgTab

  else
      Nothing


-- REPORTING PARSE ERRORS

parseErrorReport :: [Parsec.Message] -> Report.Report
parseErrorReport messages =
  let
    addMsg message hint =
      case message of
        Parsec.SysUnExpect _msg ->
            hint

        Parsec.UnExpect _msg ->
            hint

        Parsec.Expect msg ->
          let
            msg' =
              if msg `elem` [whitespace, newline, freshLine] then
                  "whitespace"
              else
                  msg
          in
            if msg == tab then
              -- Our parser looks for tab so it can throw a custom tab error message.
              -- Exclude tabs from the list of expected tokens so that no one thinks they are supported.
              hint
            else
              hint { _expected = Set.insert msg' (_expected hint) }

        Parsec.Message msg ->
            hint { _messages = msg : _messages hint }

    (ParseHint msgs expects) =
      foldr addMsg emptyHint messages

    (preHint, maybePost) =
      case msgs of
        [msg] ->
            case extractSpecialMessage msg of
              Just (MsgKeyword kwd) ->
                  ( "It looks like the keyword `" ++ kwd ++ "` is being used as a variable."
                  , Just "Rename it to something else."
                  )

              Just MsgTab ->
                  ( "A tab character was found, but all whitespace (including indentation) must be spaces not tabs."
                  , Just "I am looking for spaces, not tabs."
                  )

              Nothing ->
                  ( msg
                  , Nothing
                  )

        _ ->
            ( "I ran into something unexpected when parsing your code!"
            , Nothing
            )

    postHint =
      if Set.null expects then
          "Maybe <http://elm-lang.org/docs/syntax> can help you figure it out."

      else
          "I am looking for one of the following things:\n"
          ++ concatMap ("\n    "++) (Set.toList expects)
  in
    Report.report
      "SYNTAX PROBLEM"
      Nothing
      preHint
      (text (maybe postHint id maybePost))


data ParseHint = ParseHint
    { _messages :: [String]
    , _expected :: Set.Set String
    }
    deriving (Show)


emptyHint :: ParseHint
emptyHint =
  ParseHint [] Set.empty
