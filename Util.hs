{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wall -Werror -fwarn-incomplete-uni-patterns  #-}

module Util (PrClj(pr),
             Negateable(negative),
             stringI, parseIdentifier,
             colName,
             splitEither, maybeAll, maybeAllMapToSame, maybeTuple,
             groupMapBy,  allTheSame, mapAssoc2, unique,
             ColumnName(CN), TableName(TN), TabColName(TCN)) where

import Data.Char(toUpper)
import Data.List (nub, delete, intercalate, group, sort)

import Text.Parsec (ParseError, (<?>), (<|>), satisfy, char, many1, noneOf, letter, many, alphaNum, oneOf)
import Text.Parsec.Error (Message(..), errorMessages)
import qualified Data.Map.Strict as M
import Text.Parsec.String as TPS


data TableName = TN String deriving (Eq, Show, Ord)
data ColumnName = CN String deriving (Eq, Show, Ord)
data TabColName = TCN (Maybe TableName) ColumnName deriving (Eq, Show, Ord)

colName :: TabColName -> ColumnName
colName (TCN _ c) = c

class PrClj a where
  pr :: a -> String

class Negateable a where
  negative :: a -> a

instance (PrClj a) => PrClj [a] where
  pr l = "[" ++ unwords (map pr l) ++ "]"

instance PrClj ColumnName where
  pr (CN cn) = "(cn " ++ show cn ++ ")"

instance PrClj TableName where
  pr (TN cn) = "(tn " ++ show cn ++ ")"

instance PrClj TabColName where
  pr (TCN Nothing (CN cn)) = "(tcn nil " ++ show cn ++ ")"
  pr (TCN (Just (TN tn)) (CN cn))  = "(tcn " ++ show tn ++ " "++ show cn ++ ")"

instance PrClj ParseError where
  pr pe = "{:error {"
          ++ kv ":expected" expects
          ++ kv ":unexpected" unexpected
          ++ kv ":messages"   messages
          ++  "}}"
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
      restChar <- many (alphaNum <|> oneOf "_:$");
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

allTheSame :: (Eq a) => [a] -> Bool
allTheSame [] = True
allTheSame [_] = True
allTheSame (x:xs) = all (== x) xs

mapAssoc2 :: (Ord a, Ord b) => a-> b-> c -> M.Map a (M.Map b c) -> M.Map a (M.Map b c)
mapAssoc2 k1 k2 v m = case M.lookup k1 m of
  Nothing -> M.insert k1 (M.insert k2 v M.empty) m
  Just m2 -> M.insert k1 (M.insert k2 v m2)      m

maybeTuple :: (Maybe a, Maybe b) -> Maybe (a, b)
maybeTuple (Nothing, _) = Nothing
maybeTuple (_, Nothing) = Nothing
maybeTuple (Just a, Just b) = Just (a, b)

unique :: (Ord a) => [a] -> [a]
unique = map head . group . sort
