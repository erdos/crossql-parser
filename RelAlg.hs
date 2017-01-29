-- {-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module RelAlg (RelAlg, transform, placeholder) where

import Data.Map.Strict as Map (Map, fromList, union, keys,member)
import Data.Maybe
import Data.Either
import Data.List

import Util
import SQLParser
import CNF
import Comp
import MathExpr

type SelCond = PosCNF (Comp (MathExpr ColumnName))
type MixWhereClauseCNF = PosCNF (Comp (MathExpr ColumnName))

-- TODO: later impl other joins
data JS = NaturalJoin [(ColumnName, ColumnName)] RelAlg RelAlg -- full inner join
          deriving (Eq, Ord, Show)

data RelAlg = From [ColumnName] TableName
            | Joins JS
            | Sel  SelCond RelAlg
            -- normalize step shall turn Sel to CleanSel where possible
            -- | CleanSel (PosCNF (CompOrder ColumnName SomeScalar)) RelAlg
            | Proj (Map ColumnName (MathExpr ColumnName)) RelAlg
            | Aggr (Map ColumnName (AggregateFn ColumnName)) [ColumnName] RelAlg
            deriving (Eq, Ord, Show)


hasColName :: ColumnName -> RelAlg -> Bool
hasColName c (From cns _) = elem c cns
hasColName c (Proj _ t)= or [undefined c, hasColName c t]
hasColName c (Aggr m cns _) = or [member c m, elem c cns]
hasColName _ _ = undefined


join :: RelAlg -> RelAlg -> (Maybe JoinCond) -> RelAlg
join leftRA rightRA Nothing = Joins (NaturalJoin [] leftRA rightRA)
join leftRA rightRA (Just jc) = optionalSel $ natJoin where
  natJoin = Joins (NaturalJoin eqs leftRA rightRA)
  optionalSel = if otherClauses == [] then id else (Sel (fromClauses otherClauses))
  cnf = treeToPosCnf jc :: PosCNF (Comp (MathExpr ColumnName))
  (eqs, otherClauses) = partitionEithers
                        [(case x of
                             [CEQ (Read a) (Read b)] -> Left (a, b)
                             _ -> Right x)
                          | x <- (clauses cnf)]

-- TODO: nem jo, ha az oszlopnev idezojelek kozt van, vagy matekos kifejezes tizedesponttal
columnGetTable :: ColumnName -> Maybe (TableName, ColumnName)
columnGetTable (CN cn) = case elemIndex '.' cn of
  Nothing -> Nothing
  Just i -> let (tns, cns) = splitAt i cn in
    Just $ (TN tns, CN cns)

-- levalogatja a relevans select/where klozokat
-- keszit belole egy kifejezest
-- a maradekot visszaadja
consumeJoin :: (SelectClause, MixWhereClauseCNF)
                 -> (Either TableName QuerySpec, Maybe TableName)
                 -> (RelAlg, SelectClause, MixWhereClauseCNF)
consumeJoin x (Left tn, Nothing) = consumeJoin x (Left tn, Just tn) -- get defanult table name alias

consumeJoin (sc, whereCNF) (Left tn, Just ta)
  = (relAlg, selectRem, fromClauses whereRemClauses) where
  relAlg = Proj projMapIdentity
           $ Sel selCond
           $ Proj (Map.union projMap projMapAll)
           $ From (colsWhereClause ++ colsSelectClause) tn

  -- copy from other.
  projMapIdentity = Map.fromList $ map (\k -> (k, Read k)) $ Map.keys projMap
  selCond = fromClauses whereClauses
  projMap = Map.fromList $ map (\(cm, mCA) -> (fromMaybe (CN (renderMathExpr cm)) mCA, cm)) selectRem
  projMapAll = Map.fromList $ map (\x -> (x, Read x)) $ colsWhereClause ++ colsSelectClause
  colsWhereClause =  concatMap (\(a,b) -> collect a ++ collect b) $  concatMap (map sides) $ whereRemClauses
  colsSelectClause = concatMap (collect . fst) selectC
  -- end of close

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

  maybeGoodColumn :: ColumnName -> Maybe ColumnName
  maybeGoodColumn a = case columnGetTable a of
    Nothing -> Nothing
    Just (t, c) -> if (t == ta) then Just c else Nothing


consumeJoin _ _ = undefined

-- selectClause: [(ColMath, Maybe CA)]
-- fromClauseL: (TR, [(TR, Maybe JoinCond)])
--     TR: (Either TN SubQuery, Maybe TableAlias)
--  JoinCond: LogicTree (Comp (MathExpr CA))
-- whereClause: LogicTree (CompOrder CN (MathExpr CN))
transform :: QuerySpec -> RelAlg

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


transform (SFW selectC (t1, xs) whereC) | xs /= []
  = Sel selection $ Proj projection $ resultX
  where

    projection = Map.fromList [(fromMaybe (CN (renderMathExpr cm)) mca, cm) | (cm, mca) <- selX]

    -- TODO: ezek mar csak a maradekok, ezekbol kell kifejezest csinalni.
    (resultX, selX, selection) = foldl rf (ra, sel2, where2) xs

    whereCNF = mapPredicates (mapSides Read id) $ treeToPosCnf whereC :: MixWhereClauseCNF
    (ra, sel2, where2) = consumeJoin (selectC, whereCNF) t1

    rf :: (RelAlg, SelectClause, MixWhereClauseCNF)
       -> (TableReference, Maybe JoinCond)
       -> (RelAlg, SelectClause, MixWhereClauseCNF)
    -- TODO: ennek a feladata a join-t is megcsinalni.
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
placeholder = undefined hasColName

instance PrClj RelAlg where
  pr (From cs (TN c)) = "{:table \"" ++ c ++ "\", :cols " ++ pr cs ++ "}"
  pr (Sel sc r) = "{:select " ++ pr sc ++ ", :src " ++ pr r ++ "}"
  pr (Proj pp r) = "{:project " ++ pr pp ++ ", :src " ++ pr r ++ "}"
  pr _ = "??"
