-- {-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts#-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Comp(CompOrder(CST, CLT, CEQ, CLEQ, CSEQ, CNEQ), Comp, Comp.flip, Comp.negate, sides, mapSides, mapSides1, parse, parse1, elems) where

import Text.Parsec as TP
  ((<|>), string, spaces, try)
--import Text.Parsec.Combinator (option, optionMaybe)
--import Text.Parsec.Error (Message(..), errorMessages)
--import Text.Parsec.Language
import Text.Parsec.String as TPS (Parser)
--import Text.Parsec.Token as TPT
import Util (PrClj, pr)


data CompOrder a b = CST a b
                   | CLT a b
                   | CEQ a b
                   | CLEQ a b
                   | CSEQ a b
                   | CNEQ a b
                   deriving (Eq, Show, Ord)

type Comp a = CompOrder a a


instance (PrClj a, PrClj b) => PrClj (CompOrder a b) where
  pr (CEQ a b) = "(== " ++ pr a ++ " " ++ pr b ++")"
  pr (CNEQ a b) = "(!= " ++ pr a ++ " " ++ pr b ++")"
  pr (CLEQ a b) = "(>= " ++ pr a ++ " " ++ pr b ++")"
  pr (CSEQ a b) = "(<= " ++ pr a ++ " " ++ pr b ++")"
  pr (CLT a b) = "(> " ++ pr a ++ " " ++ pr b ++")"
  pr (CST a b) = "(< " ++ pr a ++ " " ++ pr b ++")"


sides :: CompOrder a b -> (a,b)
sides (CEQ p q) = (p,q)
sides (CNEQ p q) = (p,q)
sides (CST p q) = (p,q)
sides (CLT p q) = (p,q)
sides (CLEQ p q) = (p,q)
sides (CSEQ p q) = (p,q)

mapSides :: (a->e) -> (b->f) -> CompOrder a b -> CompOrder e f
mapSides f g (CEQ x y) = CEQ (f x) (g y)
mapSides f g (CNEQ x y) = CNEQ (f x) (g y)
mapSides f g (CLT x y) = CLT (f x) (g y)
mapSides f g (CST x y) = CST (f x) (g y)
mapSides f g (CLEQ x y) = CLEQ (f x) (g y)
mapSides f g (CSEQ x y) = CSEQ (f x) (g y)

mapSides1 :: (a -> e) -> Comp a -> Comp e
mapSides1 f = mapSides f f

parse :: Parser a -> Parser b -> Parser (CompOrder a b)
parse f g = do {a <- f; spaces; c <- op; spaces; b <- g; return (c a b)}
  where
    op :: Parser (a -> b -> CompOrder a b)
    x p q = string p >> return q
    op =  try (x "<>" CNEQ)
      <|> try (x "<=" CSEQ) <|> x "<" CST
      <|> try (x ">=" CLEQ) <|> x ">" CLT
      <|> try (x "==" CEQ)  <|> x "=" CEQ
      <|> x "!=" CNEQ

parse1 :: Parser a -> Parser (Comp a)
parse1 f = parse f f

elems :: CompOrder a b -> (a, b)
elems (CST x y) = (x,y)
elems (CLT x y) = (x,y)
elems (CEQ x y) = (x,y)
elems (CNEQ x y) = (x,y)
elems (CSEQ x y) = (x,y)
elems (CLEQ x y) = (x,y)

flip :: CompOrder a b -> CompOrder b a
flip x = case x of
  (CST a b)  -> CLT  b a
  (CLT a b)  -> CST  b a
  (CEQ a b)  -> CEQ  b a
  (CNEQ a b) -> CNEQ b a
  (CSEQ a b) -> CLEQ b a
  (CLEQ a b) -> CSEQ b a

negate :: CompOrder a b -> CompOrder a b
negate x = case x of
  (CST a b) -> CLEQ a b
  (CLEQ a b) -> CST a b
  (CEQ a b) -> CNEQ a b
  (CNEQ a b) -> CEQ a b
  (CSEQ a b) -> CLT a b
  (CLT a b) -> CSEQ a b
