-- {-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module ExecPlan (ExecPlan, relAlgToExecPlan) where

--import Data.Foldable (toList)
--import Data.List (group, nub)
-- import Data.Map.Strict as Map (Map, fromList, union, keys,member)
-- import Data.Maybe
-- import Data.List
-- import Data.Either

import RelAlg
import SQLParser
import CNF
import Comp
import MathExpr
--import Util

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

relAlgToExecPlan :: RelAlg -> ExecPlan
relAlgToExecPlan = undefined EP_From EP_Sel EP_Proj EP_Aggr EP_Join normalize
