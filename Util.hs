{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -Werror #-}

module Util (PrClj, pr, Negateable(negative), stringI, parseIdentifier, splitEither, maybeAll,groupMapBy, maybeAllMapToSame) where

import Data.Char(toUpper)
import Data.List (nub, delete, intercalate)

import Text.Parsec (ParseError, (<?>), (<|>), satisfy, char, many1, noneOf, letter, many, alphaNum, oneOf)
import Text.Parsec.Error (Message(..), errorMessages)
import qualified Data.Map.Strict as M
import Text.Parsec.String as TPS

class PrClj a where
  pr :: a -> String

class Negateable a where
  negative :: a -> a

instance (PrClj a) => PrClj [a] where
  pr l = "[" ++ unwords (map pr l) ++ "]"

instance PrClj ParseError where
  pr pe = "{"
          ++ kv ":expected" expects
          ++ kv ":unexpected" unexpected
          ++ kv ":messages"   messages
          ++  "}"
    where
      kv k v = " " ++ k ++ " [" ++ unwords (map show $ delete "" $ nub v) ++ "]"
      expects = [s | Expect s <- errorMessages pe]
      messages = [s | Message s <- errorMessages pe]
      unexpected = [s | UnExpect s <- errorMessages pe]
                   ++ [s | SysUnExpect s <- errorMessages pe]

instance (PrClj a, PrClj b) => PrClj (M.Map a b) where
  pr m = "{"
    ++ intercalate ", " (map (\(k,v)-> pr k ++ " " ++ pr v) $ M.assocs m)
    ++ "}"



-- case insensitive string matching
stringI :: String -> Parser String
stringI cs = mapM caseChar cs <?> cs where
  caseChar c = satisfy (\x -> toUpper x == toUpper c)

parseIdentifier :: Parser String
parseIdentifier = idBacktick <|> id1
  where
    idBacktick = do {
      _ <- char '`';
      s <- many1 $ noneOf "`" ; -- satisfy (/= '`');
      _ <- char '`';
      return s}
    id1 = do {
      firstChar <- letter <|> oneOf "_$";
      restChar <- many (alphaNum <|> oneOf "_:$.");
      return $ firstChar : restChar}

splitEither :: (a -> Either b c) -> [a] -> ([b], [c])
splitEither _ [] = ([],[])
splitEither f (x:xs) = case f x of
  Left a -> (a:as, bs)
  Right b -> (as, b:bs)
  where
    (as, bs) = splitEither f xs

maybeAll :: [Maybe a] -> Maybe [a]
maybeAll [] = Just []
maybeAll (Nothing : _) = Nothing
maybeAll (Just a : xs) = case maybeAll xs of
  Nothing -> Nothing
  Just bs -> Just (a : bs)


groupMapBy :: (Ord k) => (a -> k) -> [a] -> M.Map k [a]
groupMapBy f = foldl (\a x->  (M.insertWith (++) (f x) [x] a)) M.empty

-- assert: xs is not empty.
maybeAllMapToSame :: (Eq k) => (a->k) -> [a] -> Maybe k
maybeAllMapToSame _ [] = Nothing
maybeAllMapToSame f (x : xs) = if all ((== f x) . f) xs then Just (f x) else Nothing
