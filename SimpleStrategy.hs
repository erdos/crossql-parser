-- {-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module SimpleStrategy (transform) where

import Data.Map.Strict as Map (Map, fromList, union, keys, assocs)
import Data.Maybe
import Data.Either

import Util
import SQLParser
import CNF
import Comp
import MathExpr

type MixWhereClauseCNF = PosCNF (Comp (MathExpr TabColName))

-- TODO: later impl other joins
data JS = InnerJoin RelAlg ColumnName ColumnName RelAlg
        -- | FullOuterJoin RelAlg ColumnName ColumnName RelAlg -- TODO: impl later on
          deriving (Eq, Ord, Show)

type ProjBody = (Map ColumnName (MathExpr TabColName))

type ColMath = MathExpr ColumnName
type ColCNF = PosCNF (Comp (MathExpr ColumnName))
type TabColCNF = PosCNF (Comp (MathExpr TabColName))

data RelAlg = SourceNode [ColumnName] (PosCNF (CompOrder ColumnName SomeScalar)) TableName
            --          filter cols |  filter rows | project rows
            | TransformNode ColCNF (Map ColumnName ColMath) RelAlg
            | JoinNode JS
            -- | Aggr (Map ColumnName (AggregateFn ColumnName)) [ColumnName] RelAlg
            deriving (Eq, Ord, Show)

{-
instance PrClj RelAlg where
  pr (From cs cnf (TN c)) = "{:table \"" ++ c ++ "\", :cols " ++ pr cs ++ ", :cond " ++ pr cnf  ++"}"
  pr (Sel sc r) = "{:select " ++ scp ++ ", :src " ++ pr r ++ "}" where
    scp = pr sc -- "{" ++ concat [ "xx" | (k, v) <- assocs sc] ++ "}"
  pr (Proj pp r) = "{:project " ++ proj ++ ", :src " ++ pr r ++ "}" where
    proj = "{" ++ concat [ '"' : k ++ '"' : " " ++ pr v | (CN k, v) <- assocs pp] ++ "}"
  pr (Joins (InnerJoin  t1 (CN c1) (CN c2) t2))
    = "{:join :inner, "
      ++ ":left " ++ pr t1
      ++ ", :right " ++ pr t2
      ++ ", :left-column " ++ c1
      ++ ", :right-column" ++ c2
      ++ "}}"
  pr _ = "??"
-}

maybeLeftAligned :: PosCNF (CompOrder TabColName (MathExpr TabColName))
                 -> (PosCNF (Comp (MathExpr TabColName)),
                     PosCNF (CompOrder ColumnName SomeScalar))
maybeLeftAligned cnf = (fromClauses aa, fromClauses bb) where
  (aa, bb) = partitionEithers $ map efn $ clauses cnf where
      --efn :: [Comp (MathExpr TabColName)] -> Either a b
      efn clause = case maybeAll $ map cf clause of
        Nothing -> Left $ map (mapSides Read id) clause
        Just xs -> Right xs
      --cf :: CompOrder TabColName (MathExpr TabColName) -> Maybe (CompOrder ColumnName SomeScalar)
      cf co = case sides co of
        -- FIXME: maybe check here for table name matching!
        (TCN _ cn, me) | Just ss <- maybeEvalScalar me
                         ->  Just $ replaceSides cn ss co
        _ -> Nothing


-- makes a column name of an expr
colExprName :: ColumnMath -> Maybe ColumnName -> ColumnName
colExprName cm mcn = fromMaybe (CN (renderMathExpr cm)) mcn

data TransformError = TE

transform :: QuerySpec -> Either TransformError RelAlg

-- SELECT ... FROM <t> WHERE ...
transform (SFW selectClause ((Left tableName, _), []) whereClause)
  = Right
  $ TransformNode filterCond filterProj
  $ SourceNode sourceColumns fromCondition tableName
  where
    filterCond = mapPredicates (mapSides1 (fmap colName)) selectCondition
    filterProj = fromList [(colExprName cm mcn, fmap colName cm) | (cm, mcn) <- selectClause]

    sourceColumns = unique $ selectViewCols ++ selectCondCols
    selectViewCols = concat [map colName $ collect math | (math, _) <- selectClause]
    selectCondCols = concat [map colName $ collect l ++ collect r
                            | (l, r) <- map sides $ predicates selectCondition]
    (selectCondition, fromCondition) = maybeLeftAligned $ treeToPosCnf whereClause

-- transform (SFW selectClause ((Left tableName, mta), []) whereClause)

transform _ = Left TE
