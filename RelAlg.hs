-- {-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module RelAlg (RelAlg, transform) where

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
data JS = NaturalJoin [(ColumnName, ColumnName)] RelAlg RelAlg -- full inner join
          deriving (Eq, Ord, Show)

data RelAlg = From [ColumnName] (PosCNF (CompOrder ColumnName SomeScalar)) TableName
            | Joins JS
            | Sel (PosCNF (Comp (MathExpr ColumnName))) RelAlg
            | Proj (Map ColumnName (MathExpr ColumnName)) RelAlg
            -- | Aggr (Map ColumnName (AggregateFn ColumnName)) [ColumnName] RelAlg
            deriving (Eq, Ord, Show)

instance PrClj RelAlg where
  pr (From cs cnf (TN c)) = "{:table \"" ++ c ++ "\", :cols " ++ pr cs ++ ", :cond " ++ pr cnf  ++"}"
  pr (Sel sc r) = "{:select " ++ scp ++ ", :src " ++ pr r ++ "}" where
    scp = pr sc -- "{" ++ concat [ "xx" | (k, v) <- assocs sc] ++ "}"
  pr (Proj pp r) = "{:project " ++ proj ++ ", :src " ++ pr r ++ "}" where
    proj = "{" ++ concat [ '"' : k ++ '"' : " " ++ pr v | (CN k, v) <- assocs pp] ++ "}"
  pr (Joins (NaturalJoin cs t1 t2))
    = "{:join :natural, "
      ++ ":left " ++ pr t1
      ++ ", :right " ++ pr t2
      ++ ", :on {" ++ (concatMap (\(a, b) -> pr a ++ " " ++ pr b) cs) ++ "}}"
  pr _ = "??"


getTableName :: RelAlg -> Maybe TableName
getTableName (From _ _ tn) = Just tn
getTableName (Joins _) = Nothing
getTableName (Sel _ a) = getTableName a
getTableName (Proj _ a) = getTableName a
-- getTableName (Aggr _ _ a) = getTableName a

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


consumeJoin :: (SelectClause, MixWhereClauseCNF)
                 -> (Either TableName QuerySpec, Maybe TableName)
                 -> (RelAlg, SelectClause, MixWhereClauseCNF)
consumeJoin x (Left table, Nothing) = consumeJoin x (Left table, Just table)

consumeJoin (sc, whereCNF) (Left tn, Just _) -- FIXME: second arg is table alias, should be used here.
  = (relAlg, selectRem, fromClauses whereRemClauses) where
  relAlg = Proj projMapIdentity
           $ Sel (fromClauses aaaaa)
           $ Proj (Map.union projMap projMapAll)
           $ From fromColList (fromClauses aaaaToFrom) tn

  -- copy from other.
  projMapIdentity = Map.fromList $ map (\k -> (k, Read (TCN Nothing k))) $ Map.keys projMap
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


  (aaaaa, aaaaToFrom) = partitionEithers $ map efn $ whereClauses where
      efn clause = case maybeAll $ map cf clause of
        Nothing -> Left $ clause
        Just xs -> Right xs
      cf :: Comp (MathExpr TabColName) -> Maybe (CompOrder ColumnName SomeScalar)
      cf co = case sides co of
        -- FIXME: maybe check here for table name matching!
        (me, Read (TCN _ cn)) | Just ss <- maybeEvalScalar me
                          -> Just $ Comp.flip $ replaceSides ss cn co

        (Read (TCN _ cn), me) | Just ss <- maybeEvalScalar me
                         ->  Just $ replaceSides cn ss co
        _ -> Nothing



  -- itt a selectC TODO:TODO:TODO:FIXME:TODO:XXX:


  -- TODO: megnezni, h kell-e melyebb strategia.
  maybeGoodColumn :: TabColName -> Maybe TabColName
  maybeGoodColumn a@(TCN (Just t) _) | t == tn = Just a
  maybeGoodColumn (TCN Nothing _) = undefined -- megnezni h kell-e melyebb strategia.
  maybeGoodColumn _ = Nothing

consumeJoin _ _ = undefined

transform :: QuerySpec -> RelAlg

-- SELECT ... FROM <t> WHERE ...
transform (SFW selectC ((Left tableName, _), []) whereC)
  = (if selCondClauses == [] then id else Proj projMapIdentity)
  $ (if selCondClauses == [] then id else Sel (fromClauses selCondClauses))
  $ (if selCondClauses == [] then Proj projMap else Proj (Map.union projMap projMapAll))
  $ From allColNames (fromClauses fromConditionClauses) tableName
  where
    allColNames :: [ColumnName]
    -- FIXME: itt leelenorizni, hogy minden tnev nothing vagy just tableAlias !!!
    allColNames = unique
                  $ [cn | (TCN _ cn) <- concatMap (collect . fst) selectC]
                  ++ [cn | (s1, s2) <- map sides $ predicates whereCNF
                         , (TCN _ cn) <- s1 : collect s2] -- TODO: finish

    projMap = Map.fromList [(fromMaybe (CN (renderMathExpr cm)) mCA, cm) | (cm, mCA) <- selectC]
    projMapAll = Map.fromList [(cn, Read (TCN Nothing cn)) | cn <- allColNames]
    projMapIdentity = Map.fromList [ (colName, Read (TCN Nothing colName))
                                   | colName <- Map.keys projMap]

    (selCondClauses, fromConditionClauses) = partitionEithers $ map efn $ clauses whereCNF where
      efn clause = case maybeAll $ map cf clause of
        Nothing -> Left $ map (mapSides Read id) clause
        Just xs -> Right xs
      cf :: CompOrder TabColName (MathExpr TabColName) -> Maybe (CompOrder ColumnName SomeScalar)
      cf co = case sides co of
        -- FIXME: maybe check here for table name matching!
        (TCN _ cn, me) | Just ss <- maybeEvalScalar me
                         ->  Just $ replaceSides cn ss co
        _ -> Nothing
    whereCNF = treeToPosCnf whereC


-- SELECT ... FROM (SELECT ...) ...
transform (SFW selectC ((Right subQuery, _), []) whereC)
  = Proj projMapIdentity
  $ Sel whereCNFMix
  $ Proj (Map.union projMap projMapAll)
  $ transform subQuery
  where
    -- TODO: megnezni, hogy az table nevek ne tunjenek el foloslegesen.
    allColNames :: [ColumnName]
    allColNames = unique
                  $ [cn | (TCN _ cn) <- concatMap (collect . fst) selectC]
                  ++ [cn | (s1, s2) <- map sides $ predicates whereCNF
                         , (TCN _ cn) <- s1 : collect s2] -- TODO: finish

    projMap = Map.fromList [(fromMaybe (CN (renderMathExpr cm)) mCA, cm) | (cm, mCA) <- selectC]
    projMapAll = Map.fromList [(cn, Read (TCN Nothing cn)) | cn <- allColNames]
    projMapIdentity = Map.fromList [ (colName, Read (TCN Nothing colName))
                                   | colName <- Map.keys projMap]

    whereCNF = treeToPosCnf whereC
    whereCNFMix = mapPredicates (mapSides Read id) whereCNF

-- SELECT ... FROM t1, t2, ...
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

-}

transform (SFWGH s f w g having) = Sel selCond $ transform $ SFWG s f w g
  where selCond = mapPredicates m $ treeToPosCnf having -- TODO: impl this
        m = mapSides (FnCall . fmap (TCN Nothing)) Sca

transform _ = undefined
