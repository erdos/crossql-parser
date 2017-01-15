-- {-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module SQLStrategy (TopQuery, RawQuery(RawQuery), JoinedQuery(EquiJoin), transformer,
                     splitCNF, maybeOrder, orderCNF,
                     collector
                   ) where


import Data.Foldable (toList)
import Data.List (group)
import Data.Map.Strict as Map (Map, empty, alter)
import Data.Maybe

import SQLParser
import CNF
import Comp
import MathExpr
import Util

-- TODO: turn into execution plan.

-- PLAN
-- this is the result returned to clj

data RawQuery = RawQuery [ColumnName] TableName (PosCNF (CompOrder ColumnName SomeScalar))

-- unqualified aliases. first from first table, second from second table
type EquiJoinCond = [(ColumnAlias, ColumnAlias)]
-- JOIN ... ON c1=c2, d1=d2, ...
data JoinedQuery = EquiJoin EquiJoinCond TopQuery TopQuery
--                 | FullJoin    TopQuery TopQuery
-- also: full join, left/right join, etc

data AggregateStep
  = AS
    [(ColumnAlias, MathExpr ColumnName)] -- SELECT
    [ColumnName] -- GROUP BY
    (PosCNF (Comp (MathExpr ColumnName))) -- HAVING

data TransformStep
  = TS
    [(ColumnAlias, MathExpr ColumnName)]
    (PosCNF (Comp (MathExpr ColumnName)))


data TopQuery = TQ -- root
                (Maybe AggregateStep)
                (Maybe TransformStep)
                (Either RawQuery JoinedQuery)

-- TODO: implement this
instance PrClj TopQuery where
  pr (TQ as ts _) = "TOP_QUERY"
                      ++ maybe "nil" (\_ -> "as") as
                      ++ maybe "nil" (\_ -> "ts") ts
                      ++ "END"

-- legbelulre mozgatjuk a folosleges felteteleket.
-- azokat, amik nem hasznalnak ezen a szinten levo oszlopneveket
-- TODO: implement this
moveConditionsInwards :: TopQuery -> TopQuery
moveConditionsInwards x = x

type CNFCME a = PosCNF (Comp (MathExpr a))

compReads :: Comp (MathExpr a) -> [a]
compReads c = toList (fst $ Comp.sides c) ++ toList (snd $ Comp.sides c)


-- kivalogatjuk azokat az agakat, ahol egy tablahoz tartozo cellak vannak
-- f: column name to table name fn.
splitCNF :: (Eq a, Ord a, Ord b, Eq b) =>
            (a -> b) -> CNFCME a -> (CNFCME a, Map b (CNFCME a))
splitCNF f cnf = foldr fff (CNF.empty, Map.empty) (CNF.clauses cnf)
  where
    fff cs (b, m) = case group $ map f $ concatMap compReads cs of
      [[x]] -> (b, Map.alter af x m) where
        af Nothing = Just $ CNF.fromClauses [cs]
        af (Just d) = Just $ CNF.insertClause cs d
      _   -> (CNF.insertClause cs b, m)


maybeOrder :: Comp (MathExpr a) -> Maybe (CompOrder a SomeScalar)
maybeOrder cmp = case Comp.sides cmp of
  (Read a, Sca b) -> Just $ Comp.mapSides (const a) (const b) cmp
  (Sca b, Read a) -> Just $ Comp.flip $ Comp.mapSides (const b) (const a) cmp
  _ -> Nothing


-- (CST (Read a) (Sca s)) = Just $ CST a s

-- megprobaljuk kettevagni a fat ugy, hogy a levalasztott ag teljesen
-- balra legyen rendezve.
-- TODO: ez most folosleges, mert a WhereClause amugy is balra van rendezve.
orderCNF :: (Ord a) => CNFCME a -> (CNFCME a, PosCNF (CompOrder a SomeScalar))
orderCNF cnf = (CNF.fromClauses os, CNF.fromClauses es)
  where
    (os, es) = foldl f ([], []) (CNF.clauses cnf)
    f (a, b) x = case mapM maybeOrder x of
      Just t -> (a, t:b)
      Nothing -> (x:a, b)


-- WC: LogicTree (CompOrder ColName (ME ColName))
-- kivalogatja azokat a feltetelek, amelyek teljesen balra rendehetoek.
orderCnf' :: WhereClause -> (PosCNF (CompOrder ColumnName SomeScalar), PosCNF (CompOrder ColumnName (MathExpr ColumnName)))
orderCnf' ltree = map2Clauses f cnf where
  cnf :: PosCNF (CompOrder ColumnName (MathExpr ColumnName))
  cnf = treeToPosCnf ltree

  f :: [CompOrder ColumnName (MathExpr ColumnName)] -> Either [CompOrder ColumnName SomeScalar] [CompOrder ColumnName (MathExpr ColumnName)]
  f comparisons = case maybeAll (map (mathMaybeScalar . rightSide) comparisons) of
    Nothing -> Right comparisons
    Just scalars -> Left $ zipWith (\s -> \c -> mapSides id (const s) c) scalars comparisons

-- megprobalja levalasztani a kifejezesekbol a bonyolult matematikai kifejezeseket.
simplifySelectClause :: SelectClause -> ([(ColumnMath, ColumnAlias)], [(ColumnName, ColumnAlias)])
simplifySelectClause [] = ([],[])
simplifySelectClause ((Read a, mColAlias): xs) = (as, xb:bs) where
  xb = (a, fromMaybe a mColAlias)
  (as, bs) = simplifySelectClause xs
simplifySelectClause ((colMath, mColAlias): xs) = (xa:as, bs) where
  xa = (colMath, fromMaybe "??" mColAlias)   -- TODO: replace ?? with toString of colMath
  (as,bs) = simplifySelectClause xs


-- WC: Logictree (CompOrder ColNam (ME ColName))
--whereClauseTo :: WhereClause ->

--splitLeftAlignedCNF :: (PosCNF ColumnName (MathExpr ColumnName)) -> (TableName -> )

-- transformWhereClause :: WhereClause ->
-- SelectCLause: [(ColumnMath, Maybe ColumnAlias)]
-- FromCLause: (TableReference, [(TableReference), Maybe JoinCond])
--                   -> ((Either TableName SubQuery), Maybe TableAlias)
-- WhereClause: LogicTree (CompOrder CN (MathExpr CN))
-- simple easy query is being transformed.
-- meg a megfelelo helyre kell mozgatni a felteteleket.
transformer :: QuerySpec -> TopQuery

transformer (SFW selectClause ((Left tableName, maybeTableAlias), []) whereClause)
  = TQ Nothing undefined source
  where
    (scCmCa, scCnCa) = simplifySelectClause selectClause
    tableAlias = fromMaybe tableName maybeTableAlias
    (filterA, filterB) = orderCnf' whereClause
    -- ha filterA ures -> es scCmCa is ures -> csak egy rawQuery

    source =  Left $ RawQuery undefined tableName undefined
    -- cnf = CNF.treeToPosCnf w

transformer (SFW _ _ _) = undefined

-- ezeket raer kesobb implementalni.

transformer (SFWG _ _ _ _) = undefined "Not yet supported"
transformer (SFWGH _ _ _ _ _) = undefined "Not yet supported"

-- TODO: remove this. we use this fn to export wip unused definitions
collector :: a
collector = undefined moveConditionsInwards AS TS
