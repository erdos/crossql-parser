-- {-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module SQLStrategy (TopQuery, RawQuery(RawQuery), JoinedQuery(EquiJoin), transformer,

                    splitCNF, maybeOrder, orderCNF

                   ) where


import Data.Foldable (toList)
import Data.List (group)
import Data.Map.Strict as Map (Map, empty, alter)


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

instance PrClj TopQuery where
  pr = undefined

-- legbelulre mozgatjuk a folosleges felteteleket.
moveConditionsInwards :: TopQuery -> TopQuery
moveConditionsInwards = undefined

--transformS :: SQLParser.SelectClause -> a
-- transformS = undefined

-- instance Negateable (CompOrder a b) where
--  negate = Comp.negate


type CNFCME a = PosCNF (Comp (MathExpr a))

compReads :: Comp (MathExpr a) -> [a]
compReads c = toList (fst $ Comp.sides c) ++ toList (snd $ Comp.sides c)


-- kivalogatjuk azokat az agakat, ahol egy tablahoz tartozo cellak vannak
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
orderCNF :: (Ord a) => CNFCME a -> (CNFCME a, PosCNF (CompOrder a SomeScalar))
orderCNF cnf = (CNF.fromClauses os, CNF.fromClauses es)
  where
    (os, es) = foldl f ([], []) (CNF.clauses cnf)
    f (a, b) x = case mapM maybeOrder x of
      Just t -> (a, t:b)
      Nothing -> (x:a, b)

-- simple easy query is being transformed.
-- meg a megfelelo helyre kell mozgatni a felteteleket.
transformer :: QuerySpec -> TopQuery
transformer (SFW _ ((Left tableName, _), []) _)
  = TQ Nothing ts source
  where
    ts = undefined -- splitCNF undefined maybeOrder undefined orderCNF undefined
    --;;                        colName   tabName   cnf
    source =  Left $ RawQuery undefined tableName undefined
    -- cnf = CNF.treeToPosCnf w

transformer _ = undefined TQ TS AS moveConditionsInwards

-- todo: write validators too
