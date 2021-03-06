{-# OPTIONS_GHC -Wall #-}
module Reporting.Error.Helpers
  ( (|>)
  , functionName, hintLink, stack, reflowParagraph
  , commaSep, capitalize, ordinalize, ordinalizeList, drawCycle
  , findPotentialTypos, vetTypos
  , nearbyNames, distance, maybeYouWant
  )
  where

import Data.Function (on)
import qualified Data.Char as Char
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Text.EditDistance as Dist
import Text.PrettyPrint.ANSI.Leijen
  ( Doc, (<>), dullyellow, fillSep, hardline, text, vcat )

import qualified AST.Helpers as Help
import qualified Elm.Compiler.Version as Compiler
import qualified Elm.Package as Pkg



-- PIPES


(|>) :: a -> (a -> b) -> b
(|>) x f =
  f x


infixl 0 |>



-- DOC HELPERS


functionName :: String -> String
functionName opName =
  let fixedName = implName opName
  in
    if Help.isOp opName then
        "(" ++ fixedName ++ ")"

    else
        "`" ++ fixedName ++ "`"


isImplName :: String -> Bool
isImplName s = not (null s) && head s == '$'

implName :: String -> String
implName s | not $ isImplName s = s
implName s | otherwise = takeWhile (/= '$') . drop 1 $ s

hintLink :: String -> String
hintLink fileName =
  "<https://github.com/elm-lang/elm-compiler/blob/"
  ++ Pkg.versionToString Compiler.version
  ++ "/hints/" ++ fileName ++ ".md>"


stack :: [Doc] -> Doc
stack list =
  case list of
    [] ->
        error "function `stack` requires a non-empty list of docs"

    doc : docs ->
        List.foldl' (\a b -> a <> hardline <> hardline <> b) doc docs


reflowParagraph :: String -> Doc
reflowParagraph paragraph =
  fillSep (map text (words paragraph))


commaSep :: [String] -> String
commaSep tokens =
  case tokens of
    [token] ->
      " " ++ token

    [token1,token2] ->
      " " ++ token1 ++ " and " ++ token2

    _ ->
      " " ++ List.intercalate ", " (init tokens) ++ ", and " ++ last tokens


capitalize :: String -> String
capitalize string =
  case string of
    [] -> []
    c : cs ->
      Char.toUpper c : cs


ordinalize :: Int -> String
ordinalize number =
  let
    remainder10 =
      number `mod` 10

    remainder100 =
      number `mod` 100

    ending
      | remainder100 `elem` [11..13] = "th"
      | remainder10 == 1             = "st"
      | remainder10 == 2             = "nd"
      | remainder10 == 3             = "rd"
      | otherwise                    = "th"
  in
    show number ++ ending

ordinalizeList :: [Int] -> String
ordinalizeList lst =
  let
    ordinalized :: [String]
    ordinalized = map ordinalize lst
  in
    case ordinalized of
      [] -> error "Ordinalizing empty list!"
      [x] -> x
      more -> (concat $ List.intersperse ", " (init more)) ++ " and " ++ last ordinalized


drawCycle :: [String] -> Doc
drawCycle strings =
  let
    topLine =
        [ text "┌─────┐"
        , text "│     V"
        ]

    line str =
        [ text "│    " <> dullyellow (text str)
        ]

    midLine =
        [ text "│     │"
        , text "│     V"
        ]

    bottomLine =
        text "└─────┘"
  in
    vcat (topLine ++ List.intercalate midLine (map line strings) ++ [ bottomLine ])



-- FIND TYPOS


findPotentialTypos :: [String] -> [String] -> [(String, String)]
findPotentialTypos leftOnly rightOnly =
  let
    veryNear leftName =
      map ((,) leftName) (filter ((==1) . distance leftName) rightOnly)
  in
    concatMap veryNear leftOnly


vetTypos :: [(String, String)] -> Maybe (Set.Set String, Set.Set String)
vetTypos potentialTypos =
  let
    tallyNames (ln, rn) (lc, rc) =
      ( Map.insertWith (+) ln 1 lc
      , Map.insertWith (+) rn 1 rc
      )

    (leftCounts, rightCounts) =
      foldr tallyNames (Map.empty, Map.empty) potentialTypos

    acceptable :: Map.Map String Int -> Bool
    acceptable counts =
      not (Map.null counts)
      &&
      Map.foldr (\n unique -> n < 2 && unique) True counts
  in
    if acceptable leftCounts && acceptable rightCounts then
        Just (Map.keysSet leftCounts, Map.keysSet rightCounts)

    else
        Nothing



-- NEARBY NAMES


nearbyNames :: (a -> String) -> a -> [a] -> [a]
nearbyNames format name names =
  let editDistance =
        if length (format name) < 3 then 1 else 2
  in
      names
        |> map (\x -> (distance (format name) (format x), x))
        |> List.sortBy (compare `on` fst)
        |> filter ( (<= editDistance) . abs . fst )
        |> map snd


distance :: String -> String -> Int
distance x y =
  Dist.restrictedDamerauLevenshteinDistance Dist.defaultEditCosts x y


maybeYouWant :: [String] -> String
maybeYouWant suggestions =
  case suggestions of
    [] ->
        ""

    _:_ ->
        "Maybe you want one of the following?\n"
        ++ concatMap ("\n    "++) (take 4 suggestions)

