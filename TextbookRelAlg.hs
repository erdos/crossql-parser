-- {-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- http://www.databasteknik.se/webbkursen/relalg-lecture/

module TextbookRelAlg (RelAlg, transform, getMaybeTableId, getColumns) where

import Data.Map.Strict as Map (Map, fromList, keys, assocs, elems, notMember, map)
import Data.Maybe
import Data.Either
import Data.List

import Util
import SQLParser
import CNF
import Comp
import MathExpr

type TabColCNF = PosCNF (Comp (MathExpr TabColName))
type ColCNF = PosCNF (Comp (MathExpr ColumnName))

type TabColMath = MathExpr TabColName
type ColMath = MathExpr ColumnName

data RelAlg = Source TableName -- table name with alias
            | Projection [ColumnName] RelAlg -- filter cols
            | Selection (PosCNF (Comp (MathExpr ColumnName))) RelAlg -- filter rows
            | Rename (Map ColumnName (MathExpr ColumnName)) RelAlg -- renames some cols (adds them)
            | InnerJoin RelAlg ColumnName ColumnName RelAlg -- join where column names match
            | MTableAlias TableName RelAlg -- meta: contains table alias
            | MProjection [ColumnName] RelAlg
            deriving (Eq, Show, Ord)

instance PrClj RelAlg where
  pr = show

data CleanModel = CS [ColumnName] ColCNF TableName
                | CInnerJoin CleanModel ColumnName ColumnName CleanModel
                | CTransform [ColumnName] ColCNF (Map ColumnName ColMath) CleanModel
                deriving (Eq, Show, Ord)

getMaybeTableId :: RelAlg -> Maybe TableName
getMaybeTableId (Source tn) = Just tn
getMaybeTableId (Projection _ x) = getMaybeTableId x
getMaybeTableId (Selection _ x) = getMaybeTableId x
getMaybeTableId (Rename _ x) = getMaybeTableId x
getMaybeTableId (MTableAlias tn _) = Just tn
getMaybeTableId (MProjection _ x) = getMaybeTableId x
getMaybeTableId (InnerJoin _ _ _ _) = Nothing

getColumns :: RelAlg -> [ColumnName]
getColumns (Source _) = []
getColumns (MTableAlias _ r) = getColumns r
getColumns (Projection cn _) = cn
getColumns (Selection _ r) = getColumns r
getColumns (Rename m r) = unique (keys m ++ getColumns r)
getColumns (InnerJoin _ _ _ _) = []
getColumns (MProjection xs _) = xs

renderMathCol :: (RenderColName a) => MathExpr a -> Maybe ColumnName -> ColumnName
renderMathCol cm mcn = fromMaybe (CN (renderColName cm)) mcn

unqualifyMathExpr :: TabColMath -> ColMath
unqualifyMathExpr = fmap (CN . renderColName)


clauseAllRead :: Comp (MathExpr a) -> [a]
clauseAllRead c = collect a ++ collect b where
  (a,b) = sides c

-- levalogatja azokat a klozokat, amik csak erre a reszfara szolnak es hozzaadja a relalg kifejezehez.
joinMapAccum :: TabColCNF -> RelAlg -> (TabColCNF, RelAlg)
joinMapAccum tcnf ra = (fromClauses mixs, para ra) where
  para = if Data.List.null goods then id else Selection (fromClauses goods)

  (mixs, goods) = partitionEithers
    [if all (\(TCN mta _) -> mta == mTableAlias) (concatMap clauseAllRead clause)
     then Right (fmap (mapSides1 (fmap colName)) clause)
     else Left clause
    | clause <- clauses tcnf]

  mTableAlias = getMaybeTableId ra


-- legalogatja azokat a szelekteket, amik csak ebbol a tablabol kerdeznek le.
selectMapAccum :: (Map ColumnName TabColMath) -> RelAlg -> (Map ColumnName TabColMath, RelAlg)
selectMapAccum m ra = (Map.fromList mixs, para ra) where
  para = if Data.List.null goods then id else Rename (Map.fromList goods)
  (mixs, goods) = partitionEithers
    [if all (\(TCN mta _) -> mta == mTableAlias) (collect v)
      then Right (k, fmap colName v)
      else Left (k, v)
      | (k, v) <- assocs m]
  mTableAlias = getMaybeTableId ra


joinSelectMapAccum :: (TabColCNF, Map ColumnName TabColMath)
                   -> RelAlg
                   -> ((TabColCNF, Map ColumnName TabColMath), RelAlg)
joinSelectMapAccum (tcnf, m) ra = ((cnf2, m2), ra3) where
  (m2, ra2) = selectMapAccum m ra
  (cnf2, ra3) = joinMapAccum tcnf ra2


-- kiszedi a from klozbol
preMapBranches :: FromClause -> [RelAlg]
preMapBranches (FromSimple _ (Left tn)) = [Source tn]
preMapBranches (FromSimple _ (Right sq)) = [transform sq]
preMapBranches (FromJoined _ (Left tn) _ xt) = (Source tn) : (preMapBranches xt)
preMapBranches (FromJoined _ (Right sq) _ xs) = (transform sq) : (preMapBranches xs)

-- findJoinConds :: FromClause -> (TabColCNF, [(ColumnName, ColumnName)])


mapWhereClause :: WhereClause -> PosCNF (Comp ColMath)
mapWhereClause w = (mapPredicates (mapSides (Read . colName) (fmap colName))
                      $ treeToPosCnf w)

-- mapWhereClauseTab :: WhereClause -> PosCNF (Comp TabColMath)
-- mapWhereClauseTab w = mapPredicates (mapSides Read id) $ treeToPosCnf w


-- TODO: add maybe stuff or error reporting at least.
doJoins :: TabColCNF -> [RelAlg] -> (TabColCNF, RelAlg)
doJoins _ [] = undefined
doJoins cnf [ra] = (cnf, ra)
doJoins cnf (a: b: relalgs) = (finalCNF, InnerJoin a c1 c2 jj) where
  (Just at) = getMaybeTableId a
  (Just bt) = getMaybeTableId b

  (finalCNF, jj) = doJoins (fromClauses restClauses) (b:relalgs)

  (c1, c2, restClauses) = f $ clauses cnf
  f [] = undefined
  f (x:xxs) = case x of
    [(CEQ (Read (TCN (Just t1) cc1))
          (Read (TCN (Just t2) cc2)))] |
      (and [(t1 == at), (t2 == bt)])
      -> (cc1, cc2, xxs)
    _ -> (cc1, cc2, x:ys) where (cc1, cc2, ys) = f xxs


{-
-- tranzitiv lezart.
expandEquivalences :: (Eq a, Ord a) => (PosCNF (Comp (MathExpr a))) -> (PosCNF (Comp (MathExpr a)))
expandEquivalences = undefined

-- adds col list just in front of FROM (maybe not needed?)
addMProjection :: RelAlg -> RelAlg
addMProjection = undefined
-}

transform :: QuerySpec -> RelAlg

-- SELECT ... FROM . WHERE ...
transform (SFW selectClause (FromSimple maybeTableAlias source) whereClause)
  = (maybe id MTableAlias maybeTableAlias)
  $ Projection (keys renameMap)
  $ Selection selectionCNF
  $ Rename renameMap
  $ MProjection mproj
  $ (either Source transform source)
    where
      selectionCNF = mapWhereClause whereClause
      renameMap = (fromList [(renderMathCol cm mcn, fmap colName cm)
                            | (cm, mcn) <- selectClause])
      mproj = filter (Prelude.flip Map.notMember renameMap)
              $ unique $ (concatMap collect (Map.elems renameMap))
              ++ concat [collect l ++ collect r
                        | (l,r) <- Data.List.map sides $ predicates selectionCNF]

-- TODO: maybe add projections too
-- TODO: maybe expand equivalences
-- TODO: maybe add meta too.
transform (SFW selectClause fromClause whereClause)
  = Selection filterCNF $ Rename renameMap $ joined
  where
    filterCNF = mapPredicates (mapSides1 unqualifyMathExpr) outmostCNF
    (outmostCNF, joined) = doJoins outerCNF branches
    renameMap = Map.map unqualifyMathExpr outerSelectMap
    ((outerCNF, outerSelectMap), branches) = mapAccumL joinSelectMapAccum (cnf, selMap) fromAlgs
      where
        selMap = fromList [(renderMathCol cm mcn, cm) | (cm, mcn) <-selectClause]
        fromAlgs = preMapBranches fromClause
        cnf = fromClauses $ clauses wc ++ (fromCnf fromClause) where
          wc  = mapPredicates (mapSides Read id) (treeToPosCnf whereClause)
          fromCnf (FromSimple _ _) = []
          fromCnf (FromJoined _ _ (Just jc) xs) = (clauses $ treeToPosCnf jc) ++ (fromCnf xs)
          fromCnf (FromJoined _ _ Nothing xs) = fromCnf xs

transform _ = undefined
-- TODO:  talan a feltetelek atrendezese kesobbi feladat?
