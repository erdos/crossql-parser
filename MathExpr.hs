{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts#-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}


module MathExpr (collect, AggregateFn, MathExpr(Sca, Read), SomeScalar(DD, II, SS), simplify, toScalar, eval, parse, parseSomeScalar, parseMathExpr, parseAggregateFn) where

import Util

-- import Control.Applicative ((<$>))

-- import Data.Foldable (Foldable, foldMap)
-- import Data.Monoid (mempty, mappend)

import Text.Parsec as TP ((<|>), chainl1, string, spaces, try)
import Text.Parsec.Language
import Text.Parsec.String as TPS
import Text.Parsec.Token as TPT

data SomeScalar = DD Double | II Integer | SS String deriving (Eq, Show, Ord)

parseSomeScalar :: Parser SomeScalar
parseSomeScalar = s <|> n where
  s = SS <$> stringLiteral haskell
  n = do {x <- naturalOrFloat haskell;
          return (case x of (Left i) -> II i; (Right d) -> DD d)}

data AggregateFn a = Avg a | Cnt a | Max a | Min a | Sum a
  deriving (Eq, Show, Ord)

arg1 :: AggregateFn a -> a
arg1 (Avg x) = x
arg1 (Cnt x) = x
arg1 (Max x) = x
arg1 (Min x) = x
arg1 (Sum x) = x

instance (PrClj a) => PrClj (AggregateFn a) where
  pr (Avg x) = "AVG(" ++ pr x ++ ")"
  pr (Cnt x) = "CNT(" ++ pr x ++ ")"
  pr (Max x) = "MAX(" ++ pr x ++ ")"
  pr (Min x) = "MIN(" ++ pr x ++ ")"
  pr (Sum x) = "SUM(" ++ pr x ++ ")"


parseAggregateFn :: Parser a -> Parser (AggregateFn a)
parseAggregateFn p = ff "MAX" Max <|> ff "AVG" Avg <|> ff "CNT" Cnt <|> ff "SUM" Sum where
  ff s f = try $ do
    _ <-stringI s;
    _<-string "("; spaces;
    x <- p;
    spaces; _<-string ")";
    return $ f x


data MathExpr a = Sca SomeScalar
                | Read a
                | Add (MathExpr a) (MathExpr a)
                | Sub (MathExpr a) (MathExpr a)
                | Mul (MathExpr a) (MathExpr a)
                | Div (MathExpr a) (MathExpr a)
                | FnCall (AggregateFn a)
                deriving (Eq, Show, Ord)

instance Foldable MathExpr where
  foldMap f (Read x) = f x
  foldMap _ (Sca _) = mempty
  foldMap f (Add a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Sub a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Mul a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Div a b) = foldMap f a `mappend` foldMap f b
  foldMap f (FnCall x) = f (arg1 x)

instance (PrClj t) => PrClj (MathExpr t) where
  pr (Sca d) = show d
  pr (Read t) = pr t
  pr (Add a b) = "(+ " ++ pr a ++ " " ++ pr b ++ ")"
  pr (Sub a b) = "(- " ++ pr a ++ " " ++ pr b ++ ")"
  pr (Mul a b) = "(* " ++ pr a ++ " " ++ pr b ++ ")"
  pr (Div a b) = "(/ " ++ pr a ++ " " ++ pr b ++ ")"
  pr (FnCall f) = pr f

collect :: MathExpr a -> [a]
collect = foldMap (:[])

toScalar :: MathExpr a -> Maybe (MathExpr a)
toScalar = undefined

simplify :: MathExpr a -> MathExpr a
simplify = undefined

-- eval :: Map a SomeScalar -> MathExpr a -> MathExpr a
eval :: undefined
eval = undefined

-- TODO: also fncalls.
parseMathExpr :: Parser a -> Parser (MathExpr a)
parseMathExpr f = _start
  where
    ss s p = do {_<-string s; return p}
    _start = _sum
    -- TODO: add support for negative sign!
    -- TODO: add function calls!
    -- TODO: extends this ^.
    -- when could read OPEN_PAREN -> fncall else iden.
    -- maybe no difference on upper/lowercases.
    _sum    = chainl1 _prod (ss "+" Add <|> ss "-" Sub)
    _prod   = chainl1 _ll   (ss "*" Mul <|> ss "/" Div)
    _atom   = parens haskell _sum <|> try (FnCall <$> parseAggregateFn f) <|> (Read <$> f) <|> (Sca <$> parseSomeScalar)
    _ll     = do {spaces; x <- _atom; spaces; return x}


parse :: Parser (MathExpr SomeScalar)
parse = parseMathExpr parseSomeScalar
