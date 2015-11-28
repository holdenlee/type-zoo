{-# OPTIONS

 -XFlexibleContexts

#-}

module Parser where

import Data.Maybe
import Text.Parsec
import Text.Parsec.String
import System.Environment

import LeafTree
import Utilities

--generalized word
genWord = many1 (noneOf " (),\n")

parseExpr :: Parser a -> Parser (LeafTree a)
parseExpr p = (spaces >> (p >>= (return . leaf))) <|>
  do {
    char '(';
    trees <- sepEndBy (parseExpr p) spaces;
    char ')';
    return $ node trees;
  }

parseLISP' :: Parser (LeafTree String)
parseLISP' = parseExpr genWord

parseLISP :: String -> Maybe (LeafTree String)
parseLISP = fromRight . parse parseLISP' "" 

parseE :: (IsLeafTree String c) => String -> c 
parseE = fromJust . fmap fromLeafTree . parseLISP

{-
main = do
  s <- getArgs
  parseTest parseLISP (s!!0)
-}
