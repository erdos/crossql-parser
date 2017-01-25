-- {-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module RelAlg (RelAlg, transform, normalize) where

--import Data.Foldable (toList)
--import Data.List (group, nub)
import Data.Map.Strict as Map (Map)
--import Data.Maybe

import SQLParser
import CNF
import Comp
import MathExpr
--import Util

type SelCond = PosCNF (Comp (MathExpr ColumnName))

data AggregateFun a = Sum a | Cnt a | Avg a | Min a | Max a deriving (Eq, Ord, Show)

data JS = NaturalJoin [(ColumnName, ColumnName)] RelAlg RelAlg -- full inner join
          deriving (Eq, Ord, Show)

data RelAlg = From TableName
            | Joins JS
            | Sel  SelCond RelAlg
            | Proj (Map ColumnName (MathExpr ColumnName)) RelAlg
            | Aggr (Map ColumnName (AggregateFun ColumnName)) [ColumnName]
            deriving (Eq, Ord, Show)

-- selectClause: [(ColMath, Maybe CA)]
-- fromClauseL: (TR, [(TR, Maybe JoinCond)])
--     TR: (Either TN SubQuery, Maybe TableAlias)
--  JoinCond: LogicTree (Comp (MathExpr CA))
-- whereClause: LogicTree (CompOrder CN (MathExpr CN))
transform :: QuerySpec -> RelAlg
transform (SFW selectC fromC whereC) = Proj projMap (Sel selCond from)
  where
    projMap = undefined selectC -- build it from select clause.
    from = undefined fromC -- this is complicated (maybe joins too)
    selCond = mapPredicates (mapSides Read id) $ treeToPosCnf whereC

transform _ = undefined

normalize :: RelAlg -> RelAlg
normalize = undefined
-- maybe it will be easier to transform
