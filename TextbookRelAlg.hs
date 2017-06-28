-- {-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall -Werror -fwarn-incomplete-uni-patterns  #-}

-- http://www.databasteknik.se/webbkursen/relalg-lecture/

module TextbookRelAlg (pipeline, CleanModel) where

import Data.Map.Strict as Map (Map, fromList, keys, assocs, elems, notMember, map, insert, empty, findWithDefault)
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
            | Grouping [ColumnName] RelAlg
            | InnerJoin RelAlg ColumnName ColumnName RelAlg -- join where column names match
            | MTableAlias TableName RelAlg -- meta: contains table alias
            | MProjection [ColumnName] RelAlg
            deriving (Eq, Show, Ord)

-- todo: use these constructors only
buildProjectSelectRename :: [ColumnName] -> ColCNF -> (Map ColumnName ColMath) -> RelAlg -> RelAlg
buildProjectSelectRename a b c rel = Projection a $ Selection b $ Rename c rel

data CleanModel = CS [ColumnName] (PosCNF (CompOrder ColumnName SomeScalar)) TableName
                | CInnerJoin CleanModel ColumnName ColumnName CleanModel
                | CTransform [ColumnName] ColCNF (Map ColumnName ColMath) CleanModel
                | CGrouping [ColumnName] (Map ColumnName (AggregateFn ColumnName)) CleanModel
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
      ++ " :left-col " ++ show cnLeft
      ++ " :right-col " ++ show cnRight
      ++ "}"
  pr (CTransform cols cnf m source) =
    "{:keep [" ++ concat [" " ++ show col ++ " " | (CN col) <- cols] ++ " ]"
    ++ ":filter " ++ pr cnf
    ++ ":map " ++ pr m
    ++ ":source " ++ pr source
    ++ "}"
  pr (CGrouping cols m source) =
    "{:group-by [" ++ concat [" " ++ show col ++ " " | (CN col) <- cols] ++ "]"
    ++ " :map " ++ pr m
    ++ " :source " ++ pr source
    ++ "}"


instance PrClj TransformError where
  pr (TError msg) = "{:error " ++ show msg ++ "}"

getMaybeTableId :: RelAlg -> Maybe TableName
getMaybeTableId (Source tn) = Just tn
getMaybeTableId (Grouping _ x) = getMaybeTableId x
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

unqualifyTCN :: TabColName -> ColumnName
unqualifyTCN = CN . renderColName

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


fromClauseToCnf :: FromClause -> TabColCNF
fromClauseToCnf from = fromClauses $ fromCnf from where
  fromCnf (FromSimple _ _) = []
  fromCnf (FromJoined _ _ (Just jc) xs) = (clauses $ treeToPosCnf jc) ++ (fromCnf xs)
  fromCnf (FromJoined _ _ Nothing xs) = fromCnf xs


joinSelectMapAccum :: (TabColCNF, Map ColumnName TabColMath)
                   -> RelAlg -> ((TabColCNF, Map ColumnName TabColMath), RelAlg)
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

mapWhereClause :: WhereClause -> PosCNF (Comp ColMath)
mapWhereClause w = (mapPredicates (mapSides (Read . colName) (fmap colName)) $ treeToPosCnf w)

findEquivalence :: (TableName, TableName, TabColCNF) -> Maybe (TabColName, TabColName, TabColCNF)
findEquivalence (at, bt, cnf) = case f $ clauses cnf of
  Just (colLeft, colRight, cls) -> Just (colLeft, colRight, fromClauses cls)
  Nothing -> Nothing
  where
    f ([(CEQ (Read cc1@(TCN (Just t1) _))
             (Read cc2@(TCN (Just t2) _)))]: xxs)
      | (and [(t1 == at), (t2 == bt)])
      =  Just (cc1, cc2, xxs)
    f ([(CEQ (Read cc2@(TCN (Just t2) _))
             (Read cc1@(TCN (Just t1) _)))]: xxs)
      | (and [(t1 == at), (t2 == bt)])
      = Just (cc1, cc2, xxs)
    f (x: xxs)
      | Just (cc1, cc2, ys) <- f xxs
      = Just (cc1, cc2, x:ys)
    f _ = Nothing

-- TODO: add maybe stuff or error reporting at least.
doJoins :: TabColCNF -> [RelAlg] -> (TabColCNF, RelAlg)
doJoins _ [] = error "illegal arg"
doJoins cnf [ra] = (cnf, ra)
doJoins cnf (a : b : relalgs)
  | Just at <- getMaybeTableId a
  , Just bt <- getMaybeTableId b
  , Just (c1, c2, restCNF) <- findEquivalence (at, bt, cnf)
  , (finalCNF, jj) <- doJoins restCNF (b:relalgs)
  , inner <- InnerJoin a (unqualifyTCN c1) (unqualifyTCN c2) jj
  = (finalCNF, inner)
doJoins _ _ = error "Other illegal case"


-- TODO: tranzitiv lezartat is kene szamolni.
findEquivalences :: (Eq a, Ord a) => (PosCNF (Comp (MathExpr a))) -> (Map a [a])
findEquivalences cnf = foldl f  Map.empty eqs2 where
  f m (k, v) = Map.insert k (v: (Map.findWithDefault [] k m)) m
  eqs2 = eqs ++ [(b,a) | (a, b) <- eqs]
  eqs = catMaybes $ Data.List.map mEq $ clauses cnf where
    mEq [CEQ (Read a) (Read b)] = Just (a, b)
    mEq _ = Nothing

-- egyenlosegek kiterjesztese
-- az egyszeru (olyanok, ahol egyik oldalt read van) kifejezesek read oldalat transzformalja a
-- megadott egyenlosegek segitsegevel.
-- TODO: lehet altalanositani rajta.
expandEquivalences :: (Map TabColName [TabColName])
                   -> (PosCNF (Comp (MathExpr TabColName)))
                   -> (PosCNF (Comp (MathExpr TabColName)))
expandEquivalences mm = fromClauses . (concatMap mapClause) . clauses where
  ffind x = x : Map.findWithDefault [] x mm
  mapClause literal@[(CEQ _ _)] = [literal]
  mapClause [literal]
    | (Read litLeftSide, Read litRightSide) <- sides literal
    , leftSides <- ffind litLeftSide
    , rightSides <- ffind litRightSide
    = [[replaceSides (Read left1) (Read right1) literal]
      | left1 <- leftSides , right1 <- rightSides]
  mapClause [literal]
    | (Read litLeftSide, litRightSide) <- sides literal
    , leftSides <- ffind litLeftSide
    = [[replaceSides (Read left1) litRightSide literal] | left1 <- leftSides]
  mapClause [literal]
    | (litLeftSide, Read litRightSide) <- sides literal
    , rightSides <- ffind litRightSide
    = [[replaceSides litLeftSide (Read right1) literal] | right1 <- rightSides]
  mapClause literal = [literal]


-- TODO: debug to cover all cases
ensureContains :: RelAlg -> TabColName -> ColumnName -> RelAlg
ensureContains (Rename ren (MProjection mproj (Source src))) (TCN _ cn) acn
  = Rename (Map.insert acn (Read cn) ren)
  $ MProjection (cn : mproj)
  $ Source src -- TODO: assert TN == source (or maybe some alias whatever)
ensureContains (Selection sel (Rename ren (MTableAlias ali (Source src)))) (TCN _ cn) acn
  = Selection sel
  $ Rename (Map.insert acn (Read cn) ren)
  $ MTableAlias ali
  $ Source src -- TODO: assert TN == source or alias (?)
ensureContains (Selection sel (Rename ren (Source src))) (TCN _ cn) acn
  = Selection sel
  $ Rename (Map.insert acn (Read cn) ren)
  $ Source src -- TODO: assert TN == source or alias (?)
ensureContains (Projection p ra) tcn cn = Projection (cn : p) $ ensureContains ra tcn cn
-- ensureContains (Selection cnf ra) tcn cn = Selection cnf $ ensureContains ra tcn cn
-- ensureContains (Rename m ra) tcn cn = Rename m $ ensureContains ra tcn cn
ensureContains (InnerJoin ra a b rb) (TCN tn cn) acn | tn == getMaybeTableId ra
  = InnerJoin (ensureContains ra (TCN tn cn) acn) a b rb
ensureContains (InnerJoin ra a b rb) (TCN tn cn) acn | tn == getMaybeTableId rb
  = InnerJoin ra a b (ensureContains rb (TCN tn cn) acn)
ensureContains (MTableAlias mta x) a b = MTableAlias mta $ ensureContains x a b
ensureContains x _ _ = error $ "Unexpected " ++ show x -- todo: egyeb agak is elofordulhatnak.


transform :: QuerySpec -> RelAlg

-- SELECT ... FROM . WHERE ...
transform (SFW selectClause (FromSimple maybeTableAlias source) whereClause)
  = (maybe id MTableAlias maybeTableAlias)
  $ buildProjectSelectRename (keys renameMap) selectionCNF renameMap
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
  = buildProjectSelectRename preProjection filterCNF renameMap newJoined
  where

    -- make uo from projection only
    preProjection = [renderMathCol cm mcn | (cm, mcn) <- selectClause]

    -- outercnf -> seq of col names
    newJoined = foldl (\branch tcn -> ensureContains branch tcn (unqualifyTCN tcn)) joined colnames
      where colnames = concatMap (concatMapSides collect) (predicates outerCNF)

    filterCNF = mapPredicates (mapSides1 unqualifyMathExpr) outmostCNF :: ColCNF

    (outmostCNF :: TabColCNF, joined) = doJoins outerCNF branches

    renameMap = Map.map unqualifyMathExpr outerSelectMap

    ((outerCNF, outerSelectMap), branches) = mapAccumL joinSelectMapAccum (cnf, selMap) fromAlgs
      where
        selMap = fromList [(renderMathCol cm mcn, cm) | (cm, mcn) <-selectClause]
        fromAlgs = preMapBranches fromClause
        cnf = expandEquivalences joinEquivalences cnf1 where
          joinEquivalences = findEquivalences $ fromClauseToCnf fromClause
          cnf1 = fromClauses $ clauses wc ++ (clauses $ fromClauseToCnf fromClause) where
            wc  = mapPredicates (mapSides Read id) (treeToPosCnf whereClause)

-- calls to next implementation
transform (SFWGH a b c d havingC) = Selection cnf $ transform $ inside where
  inside = SFWG a b c d
  cnf = mapPredicates (mapSides FnCall Sca) $ treeToPosCnf havingC

-- simple impl (maybe more later)
transform (SFWG a b c groupingC) = Grouping groupingC $ transform (SFW a b c) where

-- maybe keep them instead
-- TODO: maybe clean MTableAlias nodes or wtf
cleanMetaNodes :: RelAlg -> RelAlg
cleanMetaNodes (MTableAlias _ r) = cleanMetaNodes r
cleanMetaNodes (Grouping g r) = Grouping g $ cleanMetaNodes r
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

transformToClean (Projection projectionCols (Selection selectionCNF (Rename renameMap source)))
  = case transformToClean source of
      Right clean -> Right $ CTransform projectionCols selectionCNF renameMap clean
      Left err -> Left err

transformToClean (InnerJoin left colLeft colRight right) =
  case (transformToClean left, transformToClean right) of
    (Right leftC, Right rightC) -> Right $ CInnerJoin leftC colLeft colRight rightC
    (Left err, _) -> Left err
    (_, Left err) -> Left err

-- transformToClean (Selection sel grp@(Grouping _ _))
--  = CTransform [] transformToClean grp


transformToClean (Grouping groupByColList xs)
  | Right (CTransform cn cnf colMap root) <- transformToClean xs
  , (fnAssocs, otherAssocs) <- partitionEithers [
      case v of
        (FnCall fc) -> Left (k, fc)
        _ -> Right (k, v)
      |(k,v) <- assocs colMap]
  , trMap <- Map.fromList otherAssocs
  , mappi <- Map.fromList fnAssocs
  = Right $ CTransform cn cnf trMap $ CGrouping groupByColList mappi root

transformToClean x = Left $ TError $ "Unexpcted node: " ++ show x


pipeline :: QuerySpec -> Either TransformError CleanModel
pipeline =  transformToClean . cleanMetaNodes . transform
