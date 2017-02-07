-- {-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- http://www.databasteknik.se/webbkursen/relalg-lecture/

module TextbookRelAlg (transform, getMaybeTableId, getColumns) where

import Data.Map.Strict as Map (Map, fromList, union, keys, assocs, elems, notMember)
import Data.Maybe
import Data.Either

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

data CleanModel = CS TableName
                | CInnerJoin RelAlg ColumnName ColumnName RelAlg
                deriving (Eq, Show, Ord)

getMaybeTableId :: RelAlg -> Maybe TableName
getMaybeTableId (Source tn) = Just tn
getMaybeTableId (Projection _ x) = getMaybeTableId x
getMaybeTableId (Selection _ x) = getMaybeTableId x
getMaybeTableId (Rename _ x) = getMaybeTableId x
getMaybeTableId (MTableAlias tn _) = Just tn

getColumns :: RelAlg -> [ColumnName]
getColumns (Source _) = []
getColumns (MTableAlias _ r) = getColumns r
getColumns (Projection cn _) = cn
getColumns (Selection _ r) = getColumns r
getColumns (Rename m r) = unique (keys m ++ getColumns r)

renderMathCol :: (RenderColName a) => MathExpr a -> Maybe ColumnName -> ColumnName
renderMathCol cm mcn = fromMaybe (CN (renderColName cm)) mcn

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
      selectionCNF = (mapPredicates (mapSides (Read . colName) (fmap colName))
                      $ treeToPosCnf whereClause)
      renameMap = (fromList [(renderMathCol cm mcn, fmap colName cm)
                            | (cm, mcn) <- selectClause])
      mproj = filter (Prelude.flip Map.notMember renameMap)
              $ unique $ (concatMap collect (Map.elems renameMap))
              ++ concat [collect l ++ collect r
                        | (l,r) <- map sides $ predicates selectionCNF]

transform _ = undefined
-- TODO:  talan a feltetelek atrendezese kesobbi feladat?
