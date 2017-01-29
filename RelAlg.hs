-- {-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module RelAlg (RelAlg, transform, placeholder) where

import Data.Map.Strict as Map (Map, fromList, union, keys)
import Data.Maybe
import Data.Either

import Util
import SQLParser
import CNF
import Comp
import MathExpr

type MixWhereClauseCNF = PosCNF (Comp (MathExpr TabColName))

-- TODO: later impl other joins
data JS = NaturalJoin [(ColumnName, ColumnName)] RelAlg RelAlg -- full inner join
          deriving (Eq, Ord, Show)

data RelAlg = From [ColumnName] TableName
            | Joins JS
            | Sel (PosCNF (Comp (MathExpr TabColName))) RelAlg
            -- normalize step shall turn Sel to CleanSel where possible
            -- | CleanSel (PosCNF (CompOrder ColumnName SomeScalar)) RelAlg
            | Proj (Map ColumnName (MathExpr TabColName)) RelAlg
            | Aggr (Map ColumnName (AggregateFn TabColName)) [TabColName] RelAlg
            deriving (Eq, Ord, Show)


getTableName :: RelAlg -> Maybe TableName
getTableName (From _ tn) = Just tn
getTableName (Joins _) = Nothing
getTableName (Sel _ a) = getTableName a
getTableName (Proj _ a) = getTableName a
getTableName (Aggr _ _ a) = getTableName a

join :: RelAlg -> RelAlg -> (Maybe JoinCond) -> RelAlg
join leftRA rightRA Nothing = Joins (NaturalJoin [] leftRA rightRA)
join leftRA rightRA (Just jc) = optionalSel $ natJoin where
  (leftT, rightT) = (getTableName leftRA, getTableName rightRA)
  natJoin = Joins (NaturalJoin eqs leftRA rightRA)
  optionalSel = if otherClauses == [] then id else (Sel $ fromClauses otherClauses)

  -- FIXME: kesobb kiegesziteni, h magatol megtalalja mely kifejezes mely fahoz tartozik.
  pf [CEQ (Read (TCN (Just t1) a)) (Read (TCN (Just t2) b))]
    | (Just tc1) <- leftT, t1 == tc1
    , (Just tc2) <- rightT, t2 == tc2
    = Left (a, b)
  pf [CEQ (Read (TCN (Just t1) a)) (Read (TCN (Just t2) b))]
    | (Just tc1) <- leftT, t2 == tc1
    , (Just tc2) <- rightT, t1 == tc2
    = Left (b, a)
  pf x = Right x

  otherClauses :: [[Comp (MathExpr TabColName)]]
  (eqs, otherClauses) = partitionEithers $ map pf $ clauses $ treeToPosCnf jc

-- TODO: nem jo, ha az oszlopnev idezojelek kozt van, vagy matekos kifejezes tizedesponttal
--columnGetTable :: ColumnName -> Maybe (TableName, ColumnName)
--columnGetTable (CN cn) = case elemIndex '.' cn of
--  Nothing -> Nothing
--  Just i -> let (tns, cns) = splitAt i cn in
--    Just $ (TN tns, CN cns)

-- levalogatja a relevans select/where klozokat
-- keszit belole egy kifejezest
-- a maradekot visszaadja
consumeJoin :: (SelectClause, MixWhereClauseCNF)
                 -> (Either TableName QuerySpec, Maybe TableName)
                 -> (RelAlg, SelectClause, MixWhereClauseCNF)
consumeJoin x (Left tn, Nothing) = consumeJoin x (Left tn, Just tn) -- get defanult table name alias

consumeJoin (sc, whereCNF) (Left tn, Just _) -- FIXME: second arg is table alias, should be used here.
  = (relAlg, selectRem, fromClauses whereRemClauses) where
  relAlg = Proj projMapIdentity
           $ Sel selCond
           $ Proj (Map.union projMap projMapAll)
           $ From fromColList tn

  -- copy from other.
  projMapIdentity = Map.fromList $ map (\k -> (k, Read (TCN Nothing k))) $ Map.keys projMap
  selCond = fromClauses whereClauses
  projMap = Map.fromList [(fromMaybe (CN (renderMathExpr cm)) mCA, cm) | (cm, mCA) <- selectRem]
  projMapAll = Map.fromList $ map (\t@(TCN _ c) -> (c, Read t)) $ colsWhereClause ++ colsSelectClause

  colsWhereClause =  concatMap (\(a,b) -> collect a ++ collect b) $  concatMap (map sides) $ whereRemClauses :: [TabColName]
  colsSelectClause = concatMap (collect . fst) selectC :: [TabColName]
  -- end of close

  fromColList = [c | (TCN _ c) <- colsWhereClause ++ colsSelectClause] :: [ColumnName]

  -- szetvalogatja az alapjan, hogy a klozon belul minden elem egy tablahoz tartozik v sem
  (whereClauses, whereRemClauses) = partitionEithers $ map wherePart $ clauses whereCNF

  -- a klozokat szetvalogatjuk es mappeljuk
  wherePart :: [Comp ColumnMath] -> Either [Comp ColumnMath] [Comp ColumnMath]
  wherePart xs = case maybeAll $ map preds xs of
    Nothing -> Left xs
    Just ts -> Right ts
    where
      -- megprobalja az aktualis oszlopra mappelni.
      preds :: Comp ColumnMath -> Maybe (Comp ColumnMath)
      preds cmp = maybeComp $ mapSides1 (mapMaybeMathExpr maybeGoodColumn) cmp

  -- a szelekt-ek kozul csak azt valasztjuk ki, aminek a table aliasa realisan jo.

  (selectRem, selectC) = partitionEithers $ map selectPart sc :: (SelectClause, SelectClause)
  selectPart (cm, mca) = case mapMaybeMathExpr maybeGoodColumn cm of
    Just mmm -> Right (mmm, mca)
    Nothing -> Left (cm, mca)

  -- TODO: megnezni, h kell-e melyebb strategia.
  maybeGoodColumn :: TabColName -> Maybe TabColName
  maybeGoodColumn a@(TCN (Just t) _) | t == tn = Just a
  maybeGoodColumn (TCN Nothing _) = undefined -- megnezni h kell-e melyebb strategia.
  maybeGoodColumn _ = Nothing


consumeJoin _ _ = undefined

-- selectClause: [(ColMath, Maybe CA)]
-- fromClauseL: (TR, [(TR, Maybe JoinCond)])
--     TR: (Either TN SubQuery, Maybe TableAlias)
--  JoinCond: LogicTree (Comp (MathExpr CA))
-- whereClause: LogicTree (CompOrder CN (MathExpr CN))
transform :: QuerySpec -> RelAlg

transform (SFW selectC ((Left tableName, _), []) whereC)
  = Proj projMapIdentity $ Sel selCond $ Proj (Map.union projMap projMapAll) $ From allColNames tableName
  where
    -- tableAlias = fromMaybe tableName mTableAlias

    -- az osszes oszlopnev SELECT valtozok + WHERE kifejezesekbol
    allColNames :: [ColumnName] -- FIXME: itt leelenorizni, hogy minden tnev nothing vagy just tableAlias !!!
    -- TODO: maybe dedup!
    allColNames = [cn | (TCN _ cn) <- concatMap (collect . fst) selectC]
                  ++ [cn | (s1, s2) <- map sides $ predicates whereCNF
                         , (TCN _ cn) <- s1 : collect s2] -- TODO: finish

    -- projMap = undefined
    projMap = Map.fromList [(fromMaybe (CN (renderMathExpr cm)) mCA, cm) | (cm, mCA) <- selectC]


    -- a select klozbol eloallitunk egy identitast.
    projMapIdentity = Map.fromList [ (colName, Read (TCN Nothing colName)) | colName <- Map.keys projMap]

    -- a where klzobol jon
    selCond = mapPredicates (mapSides Read id) whereCNF


    whereCNF = treeToPosCnf whereC
    projMapAll = Map.fromList [(cn, Read (TCN Nothing cn)) | cn <- allColNames]

{-
-- JOIN nelkuli tablak kezelese, ez is kell es elvileg jo strategia.
transform (SFW selectC ((src, _), []) whereC)
  =  Proj projMapIdentity $ Sel selCond $ Proj (Map.union projMap projMapAll) $ source
  where
    source = case src of Left tableName -> From (colsWhereClause ++ colsSelectClause) tableName
                         Right subQuery -> transform subQuery

    -- TODO: optionally use mTableAlias and tableName to de-qualify col name symbols.
    -- tableAlias = fromMaybe tableName mTableAlias
    -- TODO: resolve them by aliases from select clause!!
    colsWhereClause :: [ColumnName]
    colsWhereClause = concatMap (\(a,b) -> a:collect b) $ map sides $ predicates whereClausePosCNF
    colsSelectClause = concatMap (collect . fst) selectC :: [ColumnName]

    projMapIdentity = Map.fromList [(k, Read k) | k <- Map.keys projMap]
    projMap = Map.fromList [(fromMaybe (CN (renderMathExpr cm)) mCA, cm) | (cm, mCA) <- selectC]

    -- az osszes oszlopnev benne van - IDENTITAS
    projMapAll = Map.fromList $ map (\x -> (x, Read x)) $ colsWhereClause ++ colsSelectClause

    whereClausePosCNF = treeToPosCnf whereC :: PosCNF (CompOrder ColumnName (MathExpr ColumnName))
    -- TODO: optionally replace column names with aliases from projMap
    selCond = mapPredicates (mapSides Read id) whereClausePosCNF
-}

transform (SFW selectC (t1, xs) whereC) | xs /= []
  = Sel selection $ Proj projection $ resultX
  where
    projection = Map.fromList [(fromMaybe (CN (renderMathExpr cm)) mca, cm) | (cm, mca) <- selX]

    (resultX, selX, selection) = foldl rf (ra, sel2, where2) xs

    whereCNF = mapPredicates (mapSides Read id) $ treeToPosCnf whereC :: MixWhereClauseCNF
    (ra, sel2, where2) = consumeJoin (selectC, whereCNF) t1

    rf :: (RelAlg, SelectClause, MixWhereClauseCNF)
       -> (TableReference, Maybe JoinCond)
       -> (RelAlg, SelectClause, MixWhereClauseCNF)
    rf (leftRA, sc, mwc) (subQuery, mJoinCond)
      = (join leftRA rightRA mJoinCond, sc2, mwc2)
      where (rightRA, sc2, mwc2) = consumeJoin (sc, mwc) subQuery

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


placeholder :: undefined
placeholder = undefined

instance PrClj RelAlg where
  pr (From cs (TN c)) = "{:table \"" ++ c ++ "\", :cols " ++ pr cs ++ "}"
  pr (Sel sc r) = "{:select " ++ pr sc ++ ", :src " ++ pr r ++ "}"
  pr (Proj pp r) = "{:project " ++ pr pp ++ ", :src " ++ pr r ++ "}"
  pr _ = "??"
