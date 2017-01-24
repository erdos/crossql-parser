{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

module CNF (LogicTree(And, Or, Not, Leaf), parseLogicTree, unfoldLogicTree, treeToPosCnf, conjunction, PosCNF, clauses, fromClauses, empty, insertClause, splitClauses, map2Clauses, mapPredicates, CNF.null, predicates) where
-- cnf: literal diszjunkciok konjukcioja

import Util

import Control.Applicative ((<$>))
import Data.Foldable (Foldable, foldMap)
import Data.Monoid (mappend)

import Data.List (partition)
import Text.Parsec as TP ((<|>), chainl1, spaces)
import Text.Parsec.Language
import Text.Parsec.String as TPS
import Text.Parsec.Token as TPT

import qualified Data.Set as S
  (Set, union, empty, insert, elems, fromList, map, null)
-- import qualified Data.Map.Strict as M
--   (Map, fromList, empty, insertWith, lookup, foldlWithKey, insert,  assocs, map,
  --  mapWithKey, traverseWithKey, member, alter, intersection, union, null, elems)

-- import Text.Parsec.Combinator (option, optionMaybe)
-- import Text.Parsec.Error (Message(..), errorMessages)

data LogicTree a = And (LogicTree a) (LogicTree a)
                 | Or  (LogicTree a) (LogicTree a)
                 | Not (LogicTree a)
                 | Leaf a
                 deriving (Eq, Show, Ord, Functor)

-- TODO: logic tree should be EDN printable.

instance Foldable LogicTree where
  foldMap f (Leaf x) = f x
  foldMap f (And a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Or a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Not a)  = foldMap f a


parseLogicTree :: Parser a -> Parser (LogicTree a)
parseLogicTree pa = _start
  where
    ss s p = do{spaces; _<-stringI s; spaces; return p}
    _start = _or
    _or  = chainl1 _and (ss "or" Or)
    _and = chainl1 _ll   (ss "and" And)
    _not = do {_<-stringI "not"; spaces; Not <$> _ll}
    _pp  = do {spaces; x <- pa; return $ Leaf x}
    _ll  = parens haskell _start <|> _not <|> _pp


unfoldLogicTree :: LogicTree (LogicTree a) -> LogicTree a
unfoldLogicTree (And a b) = And (unfoldLogicTree a) (unfoldLogicTree b)
unfoldLogicTree (Or a b) = Or (unfoldLogicTree a) (unfoldLogicTree b)
unfoldLogicTree (Not a) = Not (unfoldLogicTree a)
unfoldLogicTree (Leaf x) = x


-- a Clause is a disjunction of positive and negatives items.
data Clause a = PosNeg (S.Set a) (S.Set a) deriving (Eq, Show, Read, Ord)
data CNF a = Clauses (S.Set (Clause a)) deriving (Eq, Show,Read, Ord)


oneset :: (Ord a) => a -> S.Set a
oneset x = S.insert x S.empty

toCnf :: (Ord a) => LogicTree a -> CNF a
toCnf (And x y) = Clauses $ S.union xs ys
  where
    Clauses xs = toCnf x
    Clauses ys = toCnf y
toCnf (Or x y) = Clauses $ S.fromList $ map f ps
  where
    f (PosNeg ee ff, PosNeg gg hh) = PosNeg (S.union ee gg) (S.union ff hh)
    ps = [(p,q) | p <- S.elems xs, q <- S.elems ys]
    Clauses xs = toCnf x
    Clauses ys = toCnf y
toCnf (Not (And x y)) = toCnf $ Or (Not x) (Not y)
toCnf (Not (Or x y))  = toCnf $ And (Not x) (Not y)
toCnf (Not (Not e)) = toCnf e
toCnf (Not (Leaf x)) = Clauses $ oneset $ PosNeg S.empty $ S.insert x S.empty
toCnf (Leaf x) = Clauses $ oneset (PosNeg (oneset x) S.empty)


-- disjunction of positive literals
data PosClause a = PosC (S.Set a)
  deriving (Eq, Show, Read, Ord)
-- conjuction of clauses
newtype PosCNF a = PosClauses (S.Set (PosClause a))
  deriving (Eq, Show, Read, Ord)


toPosCnf :: (Ord a, Negateable a) => CNF a -> PosCNF a
toPosCnf (Clauses cs) = PosClauses $ S.map f cs
  where f (PosNeg gg hh) = PosC $ S.union gg $ S.map Util.negative hh


instance (PrClj a) =>  PrClj (PosCNF a) where
  pr (PosClauses cs) = "(cnf+ " ++ unwords (map pc (S.elems cs)) ++ ")"
    where
      pc :: (PrClj t) => PosClause t -> String
      pc (PosC xs) = "[" ++ unwords (map pr (S.elems xs)) ++ "]"

-- collectPosCnfLiterals :: PosCNF a -> [a]
-- collectPosCnfLiterals (PosClauses cs) = concatMap (\ (PosC c) -> S.elems c) (S.elems cs)

conjunctionNaive :: (Ord a) => PosCNF a -> PosCNF a -> PosCNF a
conjunctionNaive (PosClauses x) (PosClauses y) = PosClauses $ S.union x y

-- TODO: atfedo eseteket ki is szedhetjuk.
-- -> eleg a szukebb diszjunkciokat megtartani??
-- O(nxm) algoritmus lesz igy.
-- szerencsere n, m alacsonyan marad.
-- vagy: elorendezhetunk a konjukciokat a legkisebb elemuk
-- szerint n*log(n) + m*log(m) idoben es m+n idoben megcsinalhatjuk az osszefesulest (* az ellenorzes ha false pos van, ami remelhetoleg ritka)
conjunction :: (Ord a) => PosCNF a -> PosCNF a -> PosCNF a
conjunction = conjunctionNaive

treeToPosCnf :: (Ord a, Negateable a) => LogicTree a -> PosCNF a
treeToPosCnf = toPosCnf . toCnf

clauses :: PosCNF a -> [[a]]
clauses (PosClauses x) = [S.elems y | (PosC y) <- S.elems x]

predicates :: PosCNF a -> [a]
predicates = concat . clauses

mapPredicates :: (Ord a, Ord b) => (a -> b) -> (PosCNF a) -> (PosCNF b)
mapPredicates f cnf = fromClauses [map f xs | xs <- clauses cnf]

fromClauses :: (Ord a) => [[a]] -> PosCNF a
fromClauses xs = PosClauses $ S.fromList [PosC $ S.fromList ys | ys <- xs]

empty :: (Ord a) => PosCNF a
empty = PosClauses $ S.fromList []

null :: (Ord a) => PosCNF a -> Bool
null (PosClauses xs) = S.null xs

insertClause :: (Ord a) => [a] -> PosCNF a -> PosCNF a
insertClause x (PosClauses cs) = PosClauses $ S.insert (PosC (S.fromList x)) cs

splitClauses :: (Ord a) => ([a] -> Bool) -> PosCNF a -> (PosCNF a, PosCNF a)
splitClauses f cnf = (fromClauses xs, fromClauses ys) where
  (xs, ys) = partition f (clauses cnf)

map2Clauses :: (Ord a, Ord b, Ord c) => ([a] -> Either [b] [c]) -> PosCNF a -> (PosCNF b, PosCNF c)
map2Clauses f cnf = (fromClauses xs, fromClauses ys) where
  (xs, ys) = splitEither f $ clauses cnf
