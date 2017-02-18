-- {-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- http://www.databasteknik.se/webbkursen/relalg-lecture/

module TextbookRelAlg (pipeline, CleanModel) where

import Data.Map.Strict as Map (Map, fromList, keys, assocs, elems, notMember, map, null)
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

data CleanModel = CS [ColumnName] (PosCNF (CompOrder ColumnName SomeScalar)) TableName
                | CInnerJoin CleanModel ColumnName ColumnName CleanModel
                | CTransform [ColumnName] ColCNF (Map ColumnName ColMath) CleanModel
                --  TODO: grouping node too
                deriving (Eq, Show, Ord)

data TransformError = TError String

instance PrClj CleanModel where
  pr (CS cols cnf (TN tn))
    = "{:keep [" ++ concat [" " ++ show col ++ "" | (CN col) <- cols] ++ " ] "
      ++ ":from " ++ show tn
      ++ " :where " ++ pr cnf ++ "}"
  pr (CInnerJoin left (CN cnLeft) (CN cnRight) right)
    = "{:left " ++ pr left
      ++ " :right " ++ pr right
      ++ " :left-col " ++ cnLeft
      ++ " :right-col " ++ cnRight
      ++ "}"
  pr (CTransform cols cnf m source) =
    "{:keep [" ++ concat [" " ++ show col ++ " " | (CN col) <- cols] ++ " ]"
    ++ ":filter " ++ pr cnf
    ++ ":map " ++ pr m
    ++ ":source " ++ pr source
    ++ "}"

instance PrClj TransformError where
  pr (TError msg) = "{:error " ++ show msg ++ "}"

getMaybeTableId :: RelAlg -> Maybe TableName
getMaybeTableId (Source tn) = Just tn
getMaybeTableId (Projection _ x) = getMaybeTableId x
getMaybeTableId (Selection _ x) = getMaybeTableId x
getMaybeTableId (Rename _ x) = getMaybeTableId x
getMaybeTableId (MTableAlias tn _) = Just tn
getMaybeTableId (MProjection _ x) = getMaybeTableId x
getMaybeTableId (InnerJoin _ _ _ _) = Nothing

{-
getColumns :: RelAlg -> [ColumnName]
getColumns (Source _) = []
getColumns (MTableAlias _ r) = getColumns r
getColumns (Projection cn _) = cn
getColumns (Selection _ r) = getColumns r
getColumns (Rename m r) = unique (keys m ++ getColumns r)
getColumns (InnerJoin _ _ _ _) = []
getColumns (MProjection xs _) = xs
-}

renderMathCol :: (RenderColName a) => MathExpr a -> Maybe ColumnName -> ColumnName
renderMathCol cm mcn = fromMaybe (CN (renderColName cm)) mcn

unqualifyMathExpr :: TabColMath -> ColMath
unqualifyMathExpr = fmap (CN . renderColName)


clauseAllRead :: Comp (MathExpr a) -> [a]
clauseAllRead c = collect a ++ collect b where
  (a,b) = sides c

-- addColumnToRelAlg :: ColumnName -> ColumnName -> RelAlg -> RelAlg
-- addColumnToRelAlg alias colnamee ra = undefined


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

wrapMaybeAlias :: Maybe TableName -> RelAlg -> RelAlg
wrapMaybeAlias Nothing x = x
wrapMaybeAlias (Just tn) x = MTableAlias tn x

-- kiszedi a from klozbol -- TODO: add table alias here.
preMapBranches :: FromClause -> [RelAlg]
preMapBranches (FromSimple mtn (Left tn)) = [wrapMaybeAlias mtn $ Source tn]
preMapBranches (FromSimple mtn (Right sq)) = [wrapMaybeAlias mtn $ transform sq]
preMapBranches (FromJoined mtn (Left tn) _ xt) = (wrapMaybeAlias mtn $ Source tn) : (preMapBranches xt)
preMapBranches (FromJoined mtn (Right sq) _ xs) = (wrapMaybeAlias mtn $ transform sq) : (preMapBranches xs)

-- findJoinConds :: FromClause -> (TabColCNF, [(ColumnName, ColumnName)])


mapWhereClause :: WhereClause -> PosCNF (Comp ColMath)
mapWhereClause w = (mapPredicates (mapSides (Read . colName) (fmap colName)) $ treeToPosCnf w)

-- TODO: legyen a join condition-ban hasznalt oszlopnev benne mindket agban.

-- TODO: add maybe stuff or error reporting at least.
doJoins :: TabColCNF -> [RelAlg] -> (TabColCNF, RelAlg)
doJoins _ [] = error "illegal arg"
doJoins cnf [ra] = (cnf, ra)
doJoins cnf (a : b : relalgs) = (finalCNF, inner) where

  inner = InnerJoin a c1 c2 jj

  (Just at) = getMaybeTableId a
  (Just bt) = getMaybeTableId b

  (finalCNF, jj) = doJoins (fromClauses restClauses) (b:relalgs)

  (c1, c2, restClauses) = f $ clauses cnf
  f [] = error "did not find clause to join on."
  f (x:xxs) = case x of
    [(CEQ (Read (TCN (Just t1) cc1))
          (Read (TCN (Just t2) cc2)))] |
      (and [(t1 == at), (t2 == bt)])
      -> (cc1, cc2, xxs)
    [(CEQ (Read (TCN (Just t2) cc2))
          (Read (TCN (Just t1) cc1)))] |
      (and [(t1 == at), (t2 == bt)])
      -> (cc1, cc2, xxs)
    _ -> (cc1, cc2, x:ys) where (cc1, cc2, ys) = f xxs

-- doJoins a b = error $ "Illegal case" ++ show a ++ show b

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
transform (SFW selectClause fromClause@(FromJoined _ _ _ _) whereClause)
  = (if CNF.null filterCNF then id else Selection filterCNF)
  $ (if Map.null renameMap then id else Rename renameMap)
  $ joined
  where
    filterCNF = mapPredicates (mapSides1 unqualifyMathExpr) outmostCNF
    (outmostCNF, joined) = doJoins outerCNF branches
    -- itt az outerCNF-beli oszlopneveken vegig lehet menni meg1x
    -- es megbizonyosodni rola h benne vannak a joined-ben

    --joinedWithAllCols = foldl (\jned col -> jned) joined allcols
    --allcols = []

    {-
    ensureContains :: RelAlg -> TabColName -> ColumnName -> RelAlg
    ensureContains src@(Source _) _ _ = src
    ensureContains (Projection p ra) tcn cn = Projection (cn: p) $ ensureContains ra tcn cn
    ensureContains (Selection cnf ra) tcn cn = Selection cnf $ ensureContains ra tcn cn
    ensureContains (Rename m ra) tcn cn = Rename m ra -- TODO: add rename
    ensureContains (InnerJoin ra a b rb) = undefined
    -}

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

transform (SFWG _ _ _ _) = undefined

transform (SFWGH _ _ _ _ _) = undefined

-- maybe keep them instead
-- TODO: maybe clean MTableAlias nodes or wtf
cleanMetaNodes :: RelAlg -> RelAlg
cleanMetaNodes (MTableAlias _ r) = cleanMetaNodes r
cleanMetaNodes node@(Source _) = node
cleanMetaNodes (MProjection _ r) = cleanMetaNodes r
cleanMetaNodes (Projection p r) = Projection p $ cleanMetaNodes r
cleanMetaNodes (Rename r n) = Rename r $ cleanMetaNodes n
cleanMetaNodes (Selection s n) = Selection s $ cleanMetaNodes n
cleanMetaNodes (InnerJoin t1 a b t2) = InnerJoin (cleanMetaNodes t1) a b (cleanMetaNodes t2)

splitComp :: (Ord a) => PosCNF (Comp (MathExpr a))
          -> (PosCNF (CompOrder a SomeScalar), PosCNF (Comp (MathExpr a)))
splitComp cnf = (fromClauses selected, fromClauses rest) where
  (rest, selected) = partitionEithers $ Data.List.map f $ clauses cnf
  f clause = case maybeAll (Data.List.map ff clause) of
    Nothing -> Left clause
    (Just newClause) -> Right newClause
  ff predicate = case sides predicate of
    (Read x, Sca s) -> Just $ replaceSides x s predicate
    (Sca s, Read x) -> Just $ Comp.flip $ replaceSides s x predicate
    _ -> Nothing

isProjIdentity :: (Map ColumnName ColMath) -> Bool
isProjIdentity m = and [(v == (Read k)) | (k, v) <- Map.assocs m]

-- transforming
transformToClean :: RelAlg -> Either TransformError CleanModel

-- projekciokat kette kell vagni.
transformToClean (Projection projection (Selection selection (Rename rename (Source table)))) =
  -- Left $ TError $ "Should be a simple one!" ++ show n
  Right
  $ (if projection==tables && isProjIdentity rename && CNF.null restCNF
      then id
      else  CTransform projection restCNF rename)
  $ CS tables sourceCNF table
  where
    (sourceCNF, restCNF) = splitComp selection
    tables = unique $ (concatMap collect $ Map.elems rename)
             ++ concatMap (concatMapSides collect) (predicates restCNF)

transformToClean arg@(Selection _ (Rename projmap (Source _)))
  = transformToClean $ Projection cols arg where
  cols = Map.keys projmap -- just a bugfix, needs to test it.

{- TODO: test cases
  select m1.a,m2.b from mama as m1 join mama as m2 on m1.c==m2.d where m1.x==2 and m2.y==4
  select m1.a,m2.b from mama as m1 join mama as m2 on m2.c==m1.d where m1.x==2 and m2.y==4

  select m1.ga:sessions,m1.ga:date, m2.ga:sessions from mama as m1 join mama as m2 on m1.ga:date==m2.ga:date where m1.ga:date between "2017-01-01" and "2017-02-01" and m2.ga:date between "2017-01-01" and "2017-02-01"


  should produce minimal result:
  select a from t as tt where t.c==3
-}


transformToClean (InnerJoin left colLeft colRight right) =
  case (transformToClean left, transformToClean right) of
    (Right leftC, Right rightC) -> Right $ CInnerJoin leftC colLeft colRight rightC
    (Left err, _) -> Left err
    (_, Left err) -> Left err


transformToClean x = Left $ TError $ "Unexpected node: " ++ show x


pipeline :: QuerySpec -> Either TransformError CleanModel
pipeline =  transformToClean . cleanMetaNodes . transform
