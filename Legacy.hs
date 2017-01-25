#!/usr/bin/env runhaskell
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Legacy (handleLine) where

import Control.Monad

import qualified Data.Set as S
  (Set, union, elems, fromList, null, intersection)
import qualified Data.Map.Strict as M
  (Map, fromList, empty, insertWith, lookup, foldlWithKey, insert,  assocs, map,
    mapWithKey, traverseWithKey, member, alter, null, elems)

import Data.Either()
import Data.Foldable (concat)
import Data.Maybe(listToMaybe, mapMaybe)

import Text.Parsec as TP((<|>), string,runParser, spaces, try)
import Text.Parsec.Combinator (optionMaybe)

import Text.Parsec.Language
import Text.Parsec.String as TPS
import Text.Parsec.Token as TPT

import CNF
import MathExpr
import Comp
import Util

-- used in GROUP BY and HAVING clauses
data SelectExpression = SelectAggregate (AggregateFn ColumnQualified)
                      | SelectColumn    ColumnQualified
                      -- | SelectMath      (MathExpr ColumnQualified)
                      deriving (Eq, Show, Ord)


instance PrClj ColumnQualified where
  pr (CQ (TA a) (CN b)) = a ++ "/" ++ b

-- cnfOrderedMathUnorder :: PosCNF (CompOrder a SomeNumber)

newtype ColumnName  = CN String deriving (Show, Eq, Ord)
newtype ColumnAlias = CA String deriving (Show, Eq, Ord)
newtype TableName   = TN String deriving (Show, Eq, Ord)
newtype TableAlias  = TA String deriving (Show, Eq, Ord)


data ColumnQualified = CQ TableAlias ColumnName deriving (Show, Eq, Ord)

type SelectMap         = M.Map ColumnAlias SelectExpression
type ColumnMap         = M.Map ColumnAlias ColumnQualified
type ParsedFromClause  = M.Map TableAlias (Either ParsedQueryTree TableName)
type ParsedWhereClause = LogicTree (Comp (MathExpr ColumnQualified))

data SelectMapSlice = SMSlice (M.Map ColumnAlias ColumnQualified) (M.Map ColumnAlias (AggregateFn ColumnQualified))

splitSelectMap :: SelectMap -> SelectMapSlice
splitSelectMap m = foldl f (SMSlice M.empty M.empty) (M.assocs m)
  where
    f (SMSlice a b) (k, SelectAggregate af) = SMSlice a (M.insert k af b)
    f (SMSlice a b) (k, SelectColumn cq)    = SMSlice (M.insert k cq a) b

collectCQ :: ParsedWhereClause -> [ColumnQualified]
collectCQ w = concatMap (foldMap (:[])) $ concatMap ((\(a,b)->[a,b]) . sides) $ foldMap (:[]) w


data GroupingClause = GroupBy (M.Map ColumnAlias (AggregateFn ColumnQualified))
                              [ColumnQualified]
                              (Maybe (LogicTree (CompOrder (AggregateFn ColumnQualified) SomeScalar)))
                    deriving (Eq, Show)


-- get it from parser
data ParsedQueryTree = PQT ColumnMap ParsedFromClause ParsedWhereClause (Maybe GroupingClause)
                     -- | PQTG SelectMap ParsedFromClause ParsedWhereClause
                     deriving (Eq, Show)

-- this is the output. also holds info on evaluation order
data ResultQueryTree = NestedRQT
                         (M.Map ColumnAlias ColumnQualified)
                         (M.Map TableAlias ResultQueryTree)
                         (PosCNF (Comp (MathExpr ColumnQualified)))
                     | GroupRQT
                         (M.Map ColumnAlias (AggregateFn ColumnAlias))
                         ResultQueryTree
                         [ColumnAlias] -- group by them. also, return them. (not necessary by sql syntax)
                     | SimpleRQT
                        (M.Map ColumnAlias ColumnName)
                        TableName
                        (PosCNF (CompOrder ColumnName SomeScalar))
                     deriving (Eq, Show)

instance PrClj ColumnAlias where
  pr (CA s) = s

instance PrClj ColumnName where
  pr (CN s) = s

instance PrClj TableName where
  pr (TN s) = s

instance PrClj TableAlias where
  pr (TA s) = s

instance PrClj ResultQueryTree where
  pr (NestedRQT a b c) = "{:select " ++ pr a ++ " :from " ++ pr b ++ " :where " ++ pr c ++ "}"
  pr (SimpleRQT a b c) = "{:select " ++ pr a ++ " :from " ++  pr b ++ " :where " ++ pr c ++ "}"
  pr (GroupRQT a b c) = "{:select " ++ pr a ++ " :from " ++ pr b ++ " :group-by " ++ pr c ++ "}"

instance PrClj SelectExpression where
  pr (SelectColumn cq) = pr cq
  pr (SelectAggregate kk) = pr kk

parseFromClause1 :: Parser (TableAlias, Either ParsedQueryTree TableName)
parseFromClause1 = try ps2 <|> ps1 <|> ps3 where
  ps1 = do {(TN x) <- parseTableName;
             return (TA x, Right (TN x))}
  ps2 = do {(tAlias, tName) <- parseAsPair parseTableName parseTableAlias;
             return (tAlias, Right tName)}
  ps3 = do {(tAlias, tQuery) <- parseAsPair (parens haskell parseQuery) parseTableAlias;
             return (tAlias, Left tQuery)}

parseFromClause :: Parser ParsedFromClause
parseFromClause = M.fromList <$> commaSep1 haskell parseFromClause1

parseColumnAlias :: Parser ColumnAlias
parseColumnAlias = CA <$> parseIdentifier

parseColumnName :: Parser ColumnName
parseColumnName = CN <$> parseIdentifier

parseTableAlias :: Parser TableAlias
parseTableAlias = TA <$> parseIdentifier

parseTableName :: Parser TableName
parseTableName = TN <$> parseIdentifier

parseColumnQualified :: Parser ColumnQualified
parseColumnQualified = do {
  tab <- parseTableAlias;
  _   <- string ".";
  nam <- parseColumnName;
  return $ CQ tab nam
  }


parseSelectMap :: Parser SelectMap
parseSelectMap = M.fromList <$> commaSep1 haskell selectPart
  where
    selectPart :: Parser (ColumnAlias, SelectExpression)
    selectPart = try parseExprWithAlias <|> try parseColWithoutAlias
    -- no alias is given: alis will be full qualified name with dot.
    parseColWithoutAlias = do {qualified@(CQ (TA table) (CN column)) <- parseColumnQualified;
                            return (CA $  table ++ "." ++
                                    column, SelectColumn qualified)}
    -- alias is given.
    parseExprWithAlias = parseAsPair parseSelectExpression parseColumnAlias

    -- TODO: add parsing aggregate without alias (alias name shall be generated)


parseSelectExpression :: Parser SelectExpression
parseSelectExpression = try (SelectAggregate <$> parseAggregateFn parseColumnQualified)
                        <|> (SelectColumn <$> parseColumnQualified)


parseWhereClause1 :: forall a. Parser a -> Parser (LogicTree (Comp (MathExpr a)))
parseWhereClause1 p = unfoldLogicTree <$> parseLogicTree (try parse_between <|> (Leaf <$> pc))
  where
    pc :: Parser (Comp (MathExpr a))
    pc = Comp.parse1 $ parseMathExpr p

    parse_between :: Parser (LogicTree (Comp (MathExpr a)))
    parse_between = do
      colname <- Read <$> p
      spaces;
      _ <- stringI "BETWEEN";
      spaces;
      x1 <- parseMathExpr p;
      spaces;
      _ <- stringI "AND";
      spaces;
      x2 <- parseMathExpr p;
      return $ And (Leaf (CSEQ x1 colname)) (Leaf (CSEQ colname x2))

parseWhereClause :: Parser ParsedWhereClause
parseWhereClause = parseWhereClause1 parseColumnQualified

parseQuery :: Parser ParsedQueryTree
parseQuery = try parseSimpleQuery <|> parseAliasedQuery

-- todo: parseselectclase -> parseselectmap
parseAliasedQuery :: Parser ParsedQueryTree
parseAliasedQuery =
  do
    _<-stringI "SELECT";
    spaces;
    selectMap <- parseSelectMap
    spaces;
    _<-stringI "FROM";
    spaces;
    fromClause <- parseFromClause
    spaces;
    _<-stringI "WHERE";
    spaces;
    whereClause <- parseWhereClause;
    -- we maybe have a GROUP BY clause (not sure)
    spaces;
    groupByClause <- optionMaybe $ do
      a <- parseGroupBySuffix;
      spaces;
      b <- optionMaybe parseHavingSuffix;
      return (a, b);
    build selectMap fromClause whereClause groupByClause
    -- TODO: warn when aggregated selection is given but group by clause is not.
  where
    build selectMap fromClause whereClause groupByClause
      | Nothing <- groupByClause, not (M.null ca2agg)
      = fail "Aggregate functions used without GROUP BY!"
      | Nothing <- groupByClause
      = return $ PQT ca2cq fromClause whereClause Nothing
      | Just _ <- groupByClause, M.null ca2agg
      = fail "GROUP BY used without aggregate functions!"
      | Just (a, b) <- groupByClause
      = return $ PQT ca2cq fromClause whereClause (Just $ GroupBy ca2agg a b)
      | otherwise = fail "Illegal state." -- could not happen.
      where
        (SMSlice ca2cq ca2agg) = splitSelectMap selectMap

        --groupBy :: Maybe GroupingClause
        -- groupBy = fmap (uncurry $ GroupBy ca2agg) groupByClause

--data LogicTree_Disjunction a = AndD (LogicTree_Disjunction a) | NotD a | LeafD a
--	deriving (Eq)

-- warning: returns reverse pair!
parseAsPair :: Parser a -> Parser b -> Parser (b, a)
parseAsPair pa pb =
  do
    a <- pa
    spaces;
    _ <- stringI "AS"
    spaces;
    b <- pb
    return (b, a)


parseGroupBySuffix :: Parser [ColumnQualified]
parseGroupBySuffix = do
  _ <- stringI "GROUP";
  spaces;
  _ <- stringI "BY";
  spaces;
  commaSep1 haskell parseColumnQualified;


parseHavingSuffix :: Parser (LogicTree (CompOrder (AggregateFn ColumnQualified) SomeScalar))
parseHavingSuffix = do
  _ <- stringI "HAVING";
  spaces;
  parseLogicTree $ Comp.parse (parseAggregateFn parseColumnQualified) parseSomeScalar


-- parses a query with one tablename/table in it, therefore no col aliases needed.
parseSimpleQuery :: Parser ParsedQueryTree
parseSimpleQuery =
  do
    _ <- stringI "SELECT"
    spaces;
    selectMap <- parseSelect
    spaces;
    _ <- stringI "FROM"
    spaces;
    fromTable <- parseFrom;
    spaces;
    _ <- stringI "WHERE"
    spaces;
    whereClause <- parseWhereClause1 parseColumnName;

    return $ build selectMap fromTable whereClause
  where
    build selectMap fromTable whereClause =
      PQT (toSelectClause tableName selectMap)
          (toFromClause fromTable)
          (toWhereClause tableName whereClause)
          Nothing
      where
        -- (SMSlice caToCq caToAgg) = splitSelectMap selectMap
        -- selectClause = caToCq
        tableName = getTableAlias fromTable

    -- alias is either table name or "$" when subquery.
    getTableAlias :: Either ParsedQueryTree TableName -> TableAlias
    getTableAlias (Left _) = TA "$"
    getTableAlias (Right (TN tn)) = TA tn

    toFromClause :: Either ParsedQueryTree TableName -> ParsedFromClause
    toFromClause x = M.insert (getTableAlias x) x M.empty

    toSelectClause :: TableAlias -> [(ColumnAlias, ColumnName)] -> ColumnMap
    toSelectClause t = foldl (\m (a,c) -> M.insert a (CQ t c) m) M.empty

    parseSelect :: Parser [(ColumnAlias, ColumnName)]
    parseSelect = commaSep1 haskell part

    toWhereClause :: TableAlias -> LogicTree (Comp (MathExpr ColumnName)) -> ParsedWhereClause
    toWhereClause t = fmap $ Comp.mapSides1 $ fmap $ CQ t

    parseFrom :: Parser (Either ParsedQueryTree TableName)
    parseFrom = try  (Right <$> parseTableName)
                <|>  (Left <$> parens haskell parseQuery)

    part :: Parser (ColumnAlias, ColumnName)
    part = try parseWithAlias <|> parseWithoutAlias

    parseWithoutAlias = do {(CN cn) <- parseColumnName; return (CA cn, CN cn)}
    parseWithAlias = parseAsPair parseColumnName parseColumnAlias

-- visitComp :: ((a -> a -> Comp a) -> a -> a -> b) -> Comp a -> b

  -- try to produce left aligned conditions.
maybeLeftAlign :: Comp (MathExpr t) -> Maybe (CompOrder t SomeScalar)
maybeLeftAlign t = f a b
  where
    f (Read _) (Read _) = Nothing
    f (Read c) x = case maybeEvalScalar x of
      Just (DD d)  -> Just $ compToCompOrder t c $ DD d
      Just (II i) -> Just $ compToCompOrder t c $ II i
      Just (SS s) -> Just $ compToCompOrder t c $ SS s
      Nothing ->  Nothing
    f x (Read c) = case maybeEvalScalar x of
      Just (DD d)  -> Just $ compToCompOrder (Comp.flip t) c $ DD d
      Just (II i) -> Just $ compToCompOrder (Comp.flip t) c $ II i
      Just (SS s) -> Just $ compToCompOrder (Comp.flip t) c $ SS s
      Nothing ->  Nothing
    f _  _ = Nothing
    (a, b) = sides t
    compToCompOrder :: Comp a -> b -> c -> CompOrder b c
    compToCompOrder (CST _ _) = CST
    compToCompOrder (CLT _ _) = CLT
    compToCompOrder (CEQ _ _) = CEQ
    compToCompOrder (CNEQ _ _) = CNEQ
    compToCompOrder (CSEQ _ _) = CSEQ
    compToCompOrder (CLEQ _ _) = CLEQ

-- given cnf -> collects clauses with same table alias on left side. (and rest clauses)
splitPosCnfCompOrder ::
  PosCNF (CompOrder ColumnQualified SomeScalar)
  -> (Maybe (PosCNF (CompOrder ColumnQualified SomeScalar)),
      M.Map TableAlias (PosCNF (CompOrder ColumnName SomeScalar)))
splitPosCnfCompOrder pcnf = (common, spec)
  where

    common = liftM CNF.fromClauses (M.lookup Nothing m)
    spec :: M.Map TableAlias (PosCNF (CompOrder ColumnName SomeScalar))
    spec =  M.foldlWithKey (\mm k v ->
                              (case k of  -- v is a list
                                 Just a -> M.insert a (mapPredicates
                                                       (Comp.mapSides (\(CQ _ c) -> c) id)
                                                       (CNF.fromClauses v)) mm
                                 Nothing -> mm)) M.empty m

    m :: M.Map (Maybe TableAlias) [[CompOrder ColumnQualified SomeScalar]]
    m = groupMapBy maybeHomogenClause $ CNF.clauses pcnf

    -- RETURN TableAlias when all literal share the same.
    maybeHomogenClause :: [CompOrder ColumnQualified SomeScalar] -> Maybe TableAlias
    maybeHomogenClause = maybeAllMapToSame $ (\(CQ c _) -> c) . fst . elems


type ParsedComp = Comp (MathExpr ColumnQualified)


-- orders as much conditions as possible.
prepareWhereClauseFlatten
  :: PosCNF ParsedComp
        -> (Maybe (PosCNF ParsedComp), Maybe (PosCNF (CompOrder ColumnQualified SomeScalar)))
prepareWhereClauseFlatten cnf = case (maybePosCNF bb, maybePosCNF aa) of
  -- if we have conditions to both filter and join and we have an equavalence join condition:
  -- then we create conditions that are implications of the equivalence.
  -- for example:
  -- (a.data==b.data and a.data>1) => (a.data==b.data and a.data>1 and b.data>1)
  (Just joinCnf, Just filterCnf) -> (Just joinCnf, Just (make_cnf joinCnf filterCnf))
  any_other_pair                 -> any_other_pair
  where
    make_eqs joinClauses = [(l, r) | [(CEQ (Read l) (Read r))] <- clauses joinClauses]
    make_cnf joinCnf = expandEquivalences (make_eqs joinCnf)
    --- Comp to CompOrder -> MaybeLeftAlign
    -- doClause :: PosClause ParsedComp -> Maybe (PosClause (CompOrder ColumnQualified SomeScalar))
    doClause =  mapM maybeLeftAlign

    (aa,bb) = foldl (\(a,b) x -> case doClause x of
                                   Just t  -> (insertClause t a, b);
                                   Nothing -> (a, insertClause x b))
                                                 (CNF.empty, CNF.empty) (clauses cnf)


prepareWhereClause :: LogicTree ParsedComp
                   -> (Maybe (PosCNF ParsedComp),
                       M.Map TableAlias (PosCNF (CompOrder ColumnName SomeScalar)))
prepareWhereClause tree = case orderCnfMaybe of
  Nothing -> (mixCnfMaybe, M.empty)
  Just lefts -> case splitPosCnfCompOrder lefts of
    (Nothing, m) -> (mixCnfMaybe, m)
    (Just aa, m) -> case mixCnfMaybe of
      Nothing -> (Just $ convertBack aa , m);
      Just bb -> (Just $ conjunction (convertBack aa) bb, m)
  where
    (mixCnfMaybe , orderCnfMaybe) = prepareWhereClauseFlatten $ treeToPosCnf tree
    convertBack :: PosCNF (CompOrder ColumnQualified SomeScalar) -> PosCNF ParsedComp
    convertBack = mapPredicates (Comp.mapSides Read Sca)

data ProcessError = PE String deriving (Eq, Show, Ord)


instance PrClj ProcessError where
  pr (PE s) = "{:error " ++ show s ++"}"


-- addAliasFor :: TableName ResultQueryTree

-- parse and move names, aliases, expressions to right layer.
processTree :: ParsedQueryTree -> Either ProcessError ResultQueryTree

-- an unknown table alias is used in the WHERE clause
processTree (PQT columnMap tableMap whereClause _)
  | (Just (TA tAlias)) <- msum $ f <$> collectCQ whereClause
  = Left $ PE $ "Unexpected table name in WHERE clause: " ++ tAlias
  | (Just (TA tAlias)) <- msum $ f <$> M.elems columnMap
  = Left $ PE $ "Unecpected table name in SELECT clause: " ++ tAlias
  where f (CQ t _) = if not $ M.member t tableMap then Just t else Nothing

-- TODO: add check for when GROUP BY is found without aggregate fn in SELECT
-- TODO: add check for GROUP BY clause too.
-- TODO: enable this for total error handling!!!
-- an unknown table alias is used in SELECT clause
-- processTree (PQT _ tableMap _ (GroupBy m _ _ ))
-- processTree (PQT _ tableMap _ (GroupBy _ cols _ ))
-- processTree (PQT _ tableMap _ (GroupBy _ _ (Just tree)))

processTree x@(PQT _ _ _ Nothing) = processTreeCore x

-- TODO: Having not supported
processTree x@(PQT _ _ _ (Just (GroupBy ca2af cqs Nothing))) =
  case processTreeCore x of
    err@(Left _) -> err
    (Right child@(SimpleRQT colMap _ _)) -> Right $ GroupRQT ca2afa child cols
      where
        ca2afa = M.map (fmap (\(CQ _ (CN t)) -> (CA t))) ca2af
        cols  = fmap (\(CQ _ (CN a)) -> reverseLookupWithDefault (CN a) (CA a) colMap) cqs
    _ -> Left $ PE "Not impled"
    -- need to modify all possible subselect to embed specia col names!!

processTree _ = Left $ PE "HAVING is not implemented! " -- HAVING not implemented

reverseLookupWithDefault :: (Eq v) => v -> k -> M.Map k v -> k
reverseLookupWithDefault v k m = head $ [a | (a, b) <- M.assocs m , b == v ] ++ [k]

-- discards group by (will be added later).
processTreeCore :: ParsedQueryTree -> Either ProcessError ResultQueryTree
processTreeCore (PQT columnMap tableMap whereClause _)
  --- => SELECT ... FROM tname WHERE ...
  | [(tAlias, Right tName)] <- M.assocs tableMap,
    -- Nothing <- groupByClause,
    (Just cnf)              <- M.lookup tAlias whereMap -- maybe alias for full table name too.
  = case whereJoin of
      Nothing           -> Right $ SimpleRQT cMap tName cnf
      (Just joinClause) -> Right parent
        where
          child  = SimpleRQT cMap2 tName cnf
          parent = NestedRQT parentColumns parentTableMap parentJoin
          -- we collect column names from the parent WHERE clause and insert them to child SELECT clause
          -- so they are available from the outside
          cMap2  = foldl (\cm (CQ _ (CN cn)) -> M.insert (CA cn) (CN cn) cm) cMap columnsFromJoinClause
          columnsFromJoinClause = concatMap collect $ concatMap (\(x,y) -> [x,y]) $ map sides $ CNF.predicates parentJoin
          parentColumns  = M.mapWithKey (\(CA kn) (CQ q _) -> CQ q (CN kn)) columnMap
          parentTableMap = M.insert tAlias child M.empty
          parentJoin     =  joinClause -- maybe rework it?




  --- => SELECT ... FROM (SELECT ...) WHERE ...
  {-
  | [(tAlias, Left parsedSubtree)] <- M.assocs tableMap, (Just _) <- M.lookup tAlias whereMap, Nothing <- whereJoin
  = case processTree parsedSubtree of
      Left err -> Left err
      Right (SimpleRQT _ _ _) -> Left $ PE "Not impl: only one simple?"
      Right (NestedRQT _ _ _) -> Left $ PE "Not impl: made one?"
  -}
  {-
  | [(tAlias, Right (TN tName))] <- M.assocs tableMap,
    Nothing <- M.lookup tAlias whereMap -- maybe alias for full table name too.
  = Left $ PE $ "No WHERE conditions for table name: " ++ tName
  | Nothing <- whereJoin,
    M.size tableMap > 1
  = Left $ PE "Missing JOIN conditions!"
  | (Left b) <- subTables
  = Left b   -- when error while crating subtable.
  -}
  -- general case:
  --- => SELECT t1, ... FROM ... WHERE ...
  | (Right tts)           <- subTables,
    (Just joinConditions) <- whereJoin -- ,    Nothing <- groupByClause
    -- here: filter aliases from select and condition and replace them with aliases from subtables.
  = let columnsFromJoinClause = concatMap collect $ concatMap (\(x,y) -> [x,y]) $ map sides $ predicates joinConditions
        columnsForTab :: TableAlias -> [ColumnName]
        columnsForTab ta = mapMaybe (\(CQ t c) -> if t==ta then Just c else Nothing) columnsFromJoinClause


        -- XXX here: maybe select renames should be handled somehow
        ff tableAlias (SimpleRQT colMap b c) = SimpleRQT newColMap b c
          where columns = columnsForTab tableAlias
                newColMap = foldl (\aa (CN x) -> M.insertWith (\_ t -> t) (CA x) (CN x) aa) colMap columns

        ff _ nm  = nm -- @(NestedRQT colMap b c) = nm -- NestedRQT newColMap b c
        -- where columns = columnsForTab tableAlias
        --      newColMap = foldl (\aa (CN x) -> M.insert (CA x) (CN x) aa) colMap columns
        -- we add column aliases from joinConditions to subqueries (when missing).
        ttsWithJoinAliases = M.mapWithKey ff tts

    in Right $ NestedRQT columnMap ttsWithJoinAliases joinConditions
  | otherwise = Left $ PE "Unexpected case"
  where

    -- split select map types  SMSlice caToCQ caToAgg = splitSelectMap columnMap

    subTables :: Either ProcessError (M.Map TableAlias ResultQueryTree)
    subTables = M.traverseWithKey makeSubTable tableMap
    makeSubTable :: TableAlias -> Either ParsedQueryTree TableName
                 -> Either ProcessError ResultQueryTree
    -- in submaps, we simplify all alias bindings (because they are void anyways)
    makeSubTable sTabAlias (Left pqt) =
      case M.lookup sTabAlias whereMap of
        Nothing -> processTree pqt
        (Just cnf) ->
          case processTree pqt of
            (Left a) -> Left a -- error is propagated
            (Right (GroupRQT a b c)) -> Right $ GroupRQT a b c -- TODO: what is it for??
            (Right (NestedRQT as tsm cnf2)) -> Right (NestedRQT asSimple tsm mergedWhereClause) -- TODO group by
              where
                cnfColNameToAlias = mapPredicates $ Comp.mapSides (\(CN x) -> CA x) id
                aliasToQualified x = cq where (Just cq) = M.lookup x columnMap -- what if!
                -- TODO: handle other cases too.
                asSimple = M.fromList $ map (\ (CA _, CQ ta (CN cn)) -> (CA cn, CQ ta (CN cn))) $ M.assocs as
                mergedWhereClause = conjunction cnf2
                                      (mapPredicates
                                        (Comp.mapSides (Read . aliasToQualified)
                                         Sca) (cnfColNameToAlias cnf))
            (Right (SimpleRQT as tsm cnf2)) -> Right $ SimpleRQT asSimple tsm (conjunction cnfRenamed cnf2)
              where
                -- we map back column aliases in the WHERE clause
                cnfRenamed = mapPredicates (Comp.mapSides mapColName id) cnf
                mapColName :: ColumnName -> ColumnName
                mapColName (CN colName) = case M.lookup (CA colName) as of
                  (Just cn) -> cn
                  Nothing   -> CN colName
                -- we map back column aliases in the SELECT clause.
                asSimple = M.fromList $ map (\ (CA _, CN cn) -> (nameToAlias (CN cn), CN cn)) $ M.assocs as
                nameToAlias :: ColumnName -> ColumnAlias
                nameToAlias (CN cn) = reverseLookupWithDefault (CN cn) (CA cn) as
    makeSubTable sTabAlias (Right subTableName)
      |        (Just cnf) <- M.lookup sTabAlias whereMap,
        (Just colAliases) <- M.lookup sTabAlias subTableColAliases,
        -- we map back names
         simpleColAliases <- M.fromList $ map (\ (CA _, CN cn) -> (CA cn, CN cn)) $ M.assocs colAliases
      = Right $ SimpleRQT simpleColAliases subTableName cnf
      | otherwise = Left $ PE "SELECT or WHERE clause is missing."
    cMap = M.map (\(CQ _ columnName) -> columnName) columnMap

    (whereJoin, whereMap) = prepareWhereClause whereClause
    subTableColAliases = M.foldlWithKey (\m ca (CQ ta cn) -> mapAssoc2 ta ca cn m)
                           M.empty columnMap


-- transitive closure of a list of equivalences. TODO: maybe optimize this.
spanEquations :: forall a. (Eq a, Ord a) => [(a,a)] -> [(a,a)]
spanEquations [] = []
spanEquations [(x,y)] = if x == y then [(x,y)] else [(x,y), (y,x)]
spanEquations xs = [(q,p) | s <- S.elems solution, p <- S.elems s, q <- S.elems s,  p /= q]
  where
    solution = fixpt s0 step
    s0 :: S.Set (S.Set a)
    s0 = S.fromList [S.fromList [x, y] | (x,y) <- xs]

    step :: S.Set (S.Set a) -> S.Set (S.Set a)
    step s = S.fromList $ map findMatching ss
      where ss = S.elems s
            findMatching s1 = head $ mapMaybe
                              (\s2 -> if s1 /= s2 && not (S.null $ S.intersection s1 s2)
                                      then Just $ S.union s1 s2
                                      else Nothing)
                              ss ++ [s1]
    fixpt x f = if x == fx then x else fixpt fx f where fx = f x


-- takes equivalences and adds literals
-- a should be ColumnAlias or ColumnName, b should be SomeScalar or some other expressio
expandEquivalences :: forall a . (Eq a, Ord a) =>
  [(a,a)] -> PosCNF (CompOrder a SomeScalar) -> PosCNF (CompOrder a SomeScalar)
-- PosCNF (CompOrder a (MathExpr a)) -> PosCNF (CompOrder a (MathExpr a))
expandEquivalences equivs cnf = newCnf
  where

    equivalences = spanEquations equivs :: [(a,a)]

      -- decides if this clause should be extended to other relations
    maybeRel :: [CompOrder a SomeScalar] -> Maybe a
    maybeRel xs
      | leftSides <- map (fst . sides) xs,
        allTheSame leftSides
        = listToMaybe leftSides
      | otherwise = Nothing

        -- maps to clauses that only have key on left side (and no column on right)
    homogenClausesMap :: M.Map a [[CompOrder a SomeScalar]]
    homogenClausesMap = foldl rf M.empty (CNF.clauses cnf) where
      -- rf :: M.Map a (PosClause (CompOrder a SomeScalar))
      rf m clause = case maybeRel clause of
        Nothing -> m
        (Just colName) -> M.alter alter colName m where
          -- alter :: Maybe v -> Maybe v
          alter Nothing = Just [clause]
          alter (Just xs) = Just (clause : xs)

    reClause :: a -> [CompOrder a SomeScalar] -> [CompOrder a SomeScalar]
    reClause newKey = map (Comp.mapSides (const newKey) id)

    newCnf :: PosCNF (CompOrder a SomeScalar)
    newCnf = foldl (Prelude.flip insertClause) cnf kk where
      kk = [reClause k2 clause
           | (k1, k2) <- equivalences,
             clause <- Data.Foldable.concat $ M.lookup k1 homogenClausesMap]

handleLine :: String -> String
handleLine line =
  case runParser parseQuery () "" line of
    (Left pe) -> pr pe
    (Right b) -> case processTree b of
                   (Left err) -> pr err
                   (Right tree) -> pr tree
