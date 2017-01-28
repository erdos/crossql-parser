-- {-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module RelAlg (RelAlg, transform, normalize, simplify, ExecPlan, placeholder) where

--import Data.Foldable (toList)
--import Data.List (group, nub)
import Data.Map.Strict as Map (Map, fromList, union, keys,member)
import Data.Maybe

import SQLParser
import CNF
import Comp
import MathExpr
--import Util

type SelCond = PosCNF (Comp (MathExpr ColumnName))

data JS = NaturalJoin [(ColumnName, ColumnName)] RelAlg RelAlg -- full inner join
          deriving (Eq, Ord, Show)

data RelAlg = From TableName
            | Joins JS
            | Sel  SelCond RelAlg
            --
            -- normalize step shall turn Sel to CleanSel where possible
            -- | CleanSel (PosCNF (CompOrder ColumnName SomeScalar)) RelAlg
            | Proj (Map ColumnAlias (MathExpr ColumnName)) RelAlg
            | Aggr (Map ColumnAlias (AggregateFn ColumnName)) [ColumnName] RelAlg
            deriving (Eq, Ord, Show)

hasColName :: ColumnName -> RelAlg -> Bool
hasColName _ (From _) = False
hasColName c (Proj _ t)= or [undefined c, hasColName c t]
hasColName c (Aggr m cns _) = or [member c m, elem c cns]
hasColName _ _ = undefined


type MixWhereClauseCNF = PosCNF (Comp (MathExpr ColumnName))

-- selectClause: [(ColMath, Maybe CA)]
-- fromClauseL: (TR, [(TR, Maybe JoinCond)])
--     TR: (Either TN SubQuery, Maybe TableAlias)
--  JoinCond: LogicTree (Comp (MathExpr CA))
-- whereClause: LogicTree (CompOrder CN (MathExpr CN))
transform :: QuerySpec -> RelAlg

-- JOIN nelkuli tablak kezelese, ez is kell es elvileg jo strategia.
transform (SFW selectC ((src, mTableAlias), []) whereC)
  =  Proj projMapRestricted $ Sel selCond $ Proj (Map.union projMap projMapAll) $ source
  where
    source = case src of Left tableName -> From tableName
                         Right subQuery -> transform subQuery

    -- TODO: optionally use mTableAlias and tableName to de-qualify col name symbols.
    -- tableAlias = fromMaybe tableName mTableAlias
    -- TODO: resolve them by aliases from select clause!!
    colsWhereClause :: [ColumnName]
    colsWhereClause = concatMap (\(a,b) -> a:collect b) $ map sides $ predicates whereClausePosCNF
    -- column names from select expressions
    colsSelectClause :: [ColumnName]
    colsSelectClause = concatMap (collect . fst) selectC

    projMapRestricted = Map.fromList $ map (\k -> (k, Read k)) $ Map.keys projMap
    projMap = Map.fromList $ map (\(cm, mCA) -> (fromMaybe (renderMathExpr cm) mCA, cm)) selectC

    -- az osszes oszlopnev benne van - IDENTITAS
    projMapAll = Map.fromList $ map (\x -> (x, Read x)) $ colsWhereClause ++ colsSelectClause

    whereClausePosCNF = treeToPosCnf whereC :: PosCNF (CompOrder ColumnName (MathExpr ColumnName))
    -- TODO: optionally replace column names with aliases from projMap
    selCond = mapPredicates (mapSides Read id) whereClausePosCNF

transform (SFW selectC (t1, xs) whereC) | xs /= []
  = Sel (undefined selX) $ Proj (undefined whereX) $ resultX
  where
    -- TODO: ezek mar csak a maradekok, ezekbol kell kifejezest csinalni.
    (resultX, selX, whereX) = foldl rf (ra, sel2, where2) xs

    whereCNF :: MixWhereClauseCNF
    whereCNF = mapPredicates (mapSides Read id) $ treeToPosCnf whereC
    (ra, sel2, where2) = consumeTransform (selectC, whereCNF) t1

    rf :: (RelAlg, SelectClause, MixWhereClauseCNF)
       -> (TableReference, Maybe JoinCond)
       -> (RelAlg, SelectClause, MixWhereClauseCNF)
    -- TODO: ennek a feladata a join-t is megcsinalni.
    rf (ra, sc, mwc) ((tabNameOrSubQ, maybeTableAlias), mJoinCond) = undefined (ra, sc, mwc)
    -- TODO: call consumeTransform here.



    -- try
    consumeTransform :: (SelectClause, MixWhereClauseCNF)
                     -> (Either TableName QuerySpec, Maybe TableAlias)
                     -> (RelAlg, SelectClause, MixWhereClauseCNF)
    consumeTransform x (Left tn, Nothing) = consumeTransform x (Left tn, Just tn)
    consumeTransform (sc, mwc) (Left tn, Just ta) = undefined
    -- kiszedjuk a table alias-ra vonatkozo oszlop neveket mindenhonnan
    -- letrehozunk igy egy uj kifejezest es visszaadjuk a maradekot.

{-
-- TODO: impl GROUP BY and HAVING clauses too
transform (SFWG select fromC whereC groupingColNames)
  = Aggr aggSel groupingColNames $ innerRelation
  where
    -- TODO: ha a SELECT nem csak aggregalo fuggvenyek -> tegyunk kivulre egy projekciot is.

    aggSel :: Map ColumnAlias (AggregateFn ColumnName)
    aggSel = undefined select -- undefined select -- TODO: filter all col names from select and where

    -- collect from grouping col names + aggsel.
    innerSelectC =  map (\x -> (Read x, Just x)) $ groupingColNames ++ undefined

    innerRelation = transform (SFW innerSelectC fromC whereC)

transform (SFWGH s f w g having) = Sel selCond $ transform $ SFWG s f w g
  where selCond = undefined -- TODO: impl this
-}

transform _ = undefined


-- normalize fn creates a nice execution plan.
-- TODO: find transitive closures of equivalences and introduce them.
-- TODO: move clean selects inwards
-- TODO:
normalize :: RelAlg -> RelAlg
normalize = undefined
-- maybe it will be easier to transform


-- kivant: (Aggr Proj From), (Aggr From)
data ExecPlan = EP_From [ColumnName] (PosCNF (CompOrder ColumnName SomeScalar)) TableName
              | EP_Sel SelCond ExecPlan
              | EP_Join JS
              | EP_Proj (Map ColumnName (MathExpr ColumnName)) ExecPlan
              | EP_Aggr (Map ColumnName (AggregateFn ColumnName)) [ColumnName] ExecPlan

simplify :: RelAlg -> ExecPlan
simplify = undefined EP_From EP_Sel EP_Proj EP_Aggr EP_Join

placeholder :: undefined
placeholder = undefined hasColName
