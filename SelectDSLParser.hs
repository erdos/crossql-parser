{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
--{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Main (MathExpr(..),  ResultQueryTree(..), ParsedQueryTree(..), Column(..),
             ColumnQualified(..), CompOrder(..), PrClj(..),
             parseColumnEitherQualified, tryParser, handleLine, main) where

import qualified Data.Set as S
  (Set, union, empty, insert, elems, fromList,map, null)
import qualified Data.Map.Strict as M
  (Map, fromList, empty, insertWith, lookup, foldlWithKey, insert,  assocs, map,
    mapWithKey, traverseWithKey, elems, member)

import Control.Monad
import Control.Applicative ((<$>))

import Data.Either()
import Data.List (intercalate)
import Data.Foldable (Foldable, foldMap)
import Data.Monoid (mempty, mappend)

import Text.Parsec as TP
  (chainl1, (<|>), string,runParser, ParseError, spaces, try)
import Text.Parsec.Combinator (option)
import Text.Parsec.Error (Message(..), errorMessages)
import Text.Parsec.Language
import Text.Parsec.String as TPS
import Text.Parsec.Token as TPT

data Column = ColName deriving (Eq, Show, Ord)

type SomeNumber = Either Integer Double

data MathExpr a = D Double | I Integer | Read a
                | Add (MathExpr a) (MathExpr a)
                | Sub (MathExpr a) (MathExpr a)
                | Mul (MathExpr a) (MathExpr a)
                | Div (MathExpr a) (MathExpr a)
                | Pow (MathExpr a) (MathExpr a)
                | Log (MathExpr a)
                deriving (Eq, Show, Ord, Functor)

instance Foldable MathExpr where
  foldMap f (Read x) = f x
  foldMap _ (I _) = mempty
  foldMap _ (D _) = mempty
  foldMap f (Add a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Sub a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Mul a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Div a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Pow a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Log a) = foldMap f a


numberToMathExpr :: SomeNumber -> MathExpr a
numberToMathExpr (Left i) = I i
numberToMathExpr (Right d) = D d


class PrClj a where
  pr :: a -> String

instance PrClj ParseError where
  pr pe = "{:messages " ++ concatMap f (errorMessages pe) ++ "}"
    where f (Expect x) = show x
          f (UnExpect x) = show x
          f _ = "_"

instance (PrClj a) => PrClj (MathExpr a) where
  pr (D d) = show d
  pr (I i) = show i
  pr (Read t) = pr t
  pr (Add a b) = "(+ " ++ pr a ++ " " ++ pr b ++ ")"
  pr (Sub a b) = "(- " ++ pr a ++ " " ++ pr b ++ ")"
  pr (Mul a b) = "(* " ++ pr a ++ " " ++ pr b ++ ")"
  pr (Div a b) = "(/ " ++ pr a ++ " " ++ pr b ++ ")"
  pr (Pow a b) = "(pow " ++ pr a ++ " " ++ pr b ++ ")"
  pr (Log a) = "(log " ++ pr a ++ ")"


instance PrClj ColumnQualified where
  pr (CQ a b) = a ++ "/" ++ b

{-
instance (PrClj a) => PrClj (LogicTree a) where
  pr (And a b) = "(and " ++ pr a ++ " " ++ pr b ++")"
  pr (Or a b) = "(or " ++ pr a ++ " " ++ pr b ++")"
  pr (Not a) = "(not " ++ pr a ++")"
  pr (Leaf a) = pr a
-}

instance (PrClj a, PrClj b) => PrClj (CompOrder a b) where
  pr (CEQ a b) = "(== " ++ pr a ++ " " ++ pr b ++")"
  pr (CNEQ a b) = "(!= " ++ pr a ++ " " ++ pr b ++")"
  pr (CLEQ a b) = "(>= " ++ pr a ++ " " ++ pr b ++")"
  pr (CSEQ a b) = "(<= " ++ pr a ++ " " ++ pr b ++")"
  pr (CLT a b) = "(< " ++ pr a ++ " " ++ pr b ++")"
  pr (CST a b) = "(> " ++ pr a ++ " " ++ pr b ++")"


instance (PrClj a) => PrClj (PosCNF a) where
  pr (PosClauses cs) = "(cnf " ++ unwords (map f $ S.elems cs) ++ ")"
    where
      f (PosC c) = "[" ++ unwords (map pr (S.elems c)) ++ "]"

instance (PrClj a, PrClj b) => PrClj (M.Map a b) where
  pr m = "{"
    ++ intercalate ", " (map (\(k,v)-> pr k ++ " " ++ pr v) $ M.assocs m)
    ++ "}"


someNumberMathExpr :: SomeNumber -> MathExpr a
someNumberMathExpr (Left i) = I i
someNumberMathExpr (Right d) = D d


maybeEvalMath :: MathExpr t -> Maybe SomeNumber
maybeEvalMath (D d) = Just $ Right d
maybeEvalMath (I i) = Just $ Left i
maybeEvalMath (Read _) = Nothing
maybeEvalMath (Add a b) = liftM2 op (maybeEvalMath a) (maybeEvalMath b)
  where
    op :: SomeNumber -> SomeNumber -> SomeNumber
    op (Left i) (Left j) = Left $ i + j
    op (Left i) (Right d) = Right $ fromIntegral i + d
    op (Right d) (Left i) = Right $ d + fromIntegral i
    op (Right d) (Right dr) = Right $ d + dr
maybeEvalMath (Sub a b) = liftM2 op (maybeEvalMath a) (maybeEvalMath b)
  where
    op :: SomeNumber -> SomeNumber -> SomeNumber
    op (Left i) (Left j) = Left $ i - j
    op (Left i) (Right d) = Right $ fromIntegral i - d
    op (Right d) (Left i) = Right $ d - fromIntegral i
    op (Right d) (Right dr) = Right $ d - dr
maybeEvalMath (Mul a b) = liftM2 op (maybeEvalMath a) (maybeEvalMath b)
  where
    op :: SomeNumber -> SomeNumber -> SomeNumber
    op (Left i) (Left j) = Left $ i * j
    op (Left i) (Right d) = Right $ fromIntegral i * d
    op (Right d) (Left i) = Right $ d * fromIntegral i
    op (Right d) (Right dr) = Right $ d * dr
maybeEvalMath (Div a b) = liftM2 op (maybeEvalMath a) (maybeEvalMath b)
  where
    op :: SomeNumber -> SomeNumber -> SomeNumber
    op (Left i) (Left j) = Right $ fromIntegral i / fromIntegral j
    op (Left i) (Right d) = Right $ fromIntegral i / d
    op (Right d) (Left i) = Right $ d / fromIntegral i
    op (Right d) (Right dr) = Right $ d / dr
maybeEvalMath (Pow a b) = liftM2 op (maybeEvalMath a) (maybeEvalMath b)
  where
    op :: SomeNumber -> SomeNumber -> SomeNumber
    op (Left i) (Left j) = Left $ i ^ j
    op (Left i) (Right d) = Right $ fromIntegral i ** d
    op (Right d) (Left i) = Right $ d ** fromIntegral i
    op (Right d) (Right dr) = Right $ d ** dr
maybeEvalMath (Log a) = liftM op (maybeEvalMath a)
  where
    op :: SomeNumber -> SomeNumber
    op (Left i) = Right $ log $ fromIntegral i
    op (Right d) = Right $ log d

-- COMPARISON OPERATOR

data CompOrder a b = CST a b
                   | CLT a b
                   | CEQ a b
                   | CLEQ a b
                   | CSEQ a b
                   | CNEQ a b
                   deriving (Eq, Show, Ord)

type Comp a = CompOrder a a

-- compLeft :: CompOrder a b -> a
-- compLeft = fst . getCompSides

getCompSides :: CompOrder a b -> (a,b)
getCompSides (CEQ p q) = (p,q)
getCompSides (CNEQ p q) = (p,q)
getCompSides (CST p q) = (p,q)
getCompSides (CLT p q) = (p,q)
getCompSides (CLEQ p q) = (p,q)
getCompSides (CSEQ p q) = (p,q)

--visitComp :: ((a -> a -> Comp a) -> a -> a -> b) -> Comp a -> b
--visitComp f (CST x y) = f CST x y
--visitComp f (CLT x y) = f CLT x y
--visitComp f (CSEQ x y) = f CSEQ x y
--visitComp f (CLEQ x y) = f CLEQ x y
--visitComp f (CEQ x y) = f CEQ x y
--visitComp f (CNEQ x y) = f CNEQ x y


mapComp :: (a->e) -> (b->f) -> CompOrder a b -> CompOrder e f
mapComp f g (CEQ x y) = CEQ (f x) (g y)
mapComp f g (CNEQ x y) = CNEQ (f x) (g y)
mapComp f g (CLT x y) = CLT (f x) (g y)
mapComp f g (CST x y) = CST (f x) (g y)
mapComp f g (CLEQ x y) = CLEQ (f x) (g y)
mapComp f g (CSEQ x y) = CSEQ (f x) (g y)


mapComp1 :: (a -> e) -> Comp a -> Comp e
mapComp1 f = mapComp f f


parseComp :: Parser a -> Parser (Comp a)
parseComp f = do {a <- f; spaces; c <- op; spaces; b <- f; return (c a b)}
  where
    op :: Parser (a -> a -> Comp a)
    x p q = string p >> return q
    op =  try (x "<=" CSEQ)  -- we need try to enforce backtracking
      <|> try (x ">=" CLEQ)  -- because some patterns share same prefix
      <|> x "<" CST
      <|> x ">" CLT
      <|> x "==" CEQ
      <|> x "!=" CNEQ


elemsCompOrder :: CompOrder a b -> (a,b)
elemsCompOrder (CST x y) = (x,y)
elemsCompOrder (CLT x y) = (x,y)
elemsCompOrder (CEQ x y) = (x,y)
elemsCompOrder (CNEQ x y) = (x,y)
elemsCompOrder (CSEQ x y) = (x,y)
elemsCompOrder (CLEQ x y) = (x,y)


flipComp :: CompOrder a b -> CompOrder b a
flipComp x = case x of
  (CST a b) -> CLT b a
  (CLT a b) -> CST b a
  (CEQ a b) -> CEQ b a
  (CNEQ a b) -> CNEQ b a
  (CSEQ a b) -> CLEQ b a
  (CLEQ a b) -> CSEQ b a


negateComp :: CompOrder a b -> CompOrder a b
negateComp x = case x of
  (CST a b) -> CLEQ a b
  (CLEQ a b) -> CST a b
  (CEQ a b) -> CNEQ a b
  (CNEQ a b) -> CEQ a b
  (CSEQ a b) -> CLT a b
  (CLT a b) -> CSEQ a b

-- cnfOrderedMathUnorder :: PosCNF (CompOrder a SomeNumber)

type ColumnName = String

type ColumnAlias = String
data ColumnQualified = CQ TableAlias ColumnName deriving (Show, Eq, Ord)

type TableName = String
type TableAlias = String

type ColumnEitherQualified = Either ColumnQualified ColumnAlias

type ColumnMap         = M.Map ColumnAlias ColumnQualified
type ParsedFromClause  = M.Map TableAlias (Either ParsedQueryTree TableName)
type ParsedWhereClause = LogicTree (Comp (MathExpr ColumnQualified))

collectCQ :: ParsedWhereClause -> [ColumnQualified]
collectCQ w = concatMap (foldMap (:[])) $ concatMap ((\(a,b)->[a,b]) . getCompSides) $ foldMap (:[]) w


-- get it from parser
data ParsedQueryTree = PQT ColumnMap ParsedFromClause ParsedWhereClause deriving (Eq, Show)

-- this is the output. also holds info on evaluation order
data ResultQueryTree = NestedRQT
                         (M.Map ColumnAlias ColumnQualified)
                         (M.Map TableAlias ResultQueryTree)
                         (PosCNF (Comp (MathExpr ColumnQualified)))
                     |  SimpleRQT
                        (M.Map ColumnAlias ColumnName)
                        TableName
                        (PosCNF (CompOrder ColumnName SomeNumber))
                     deriving (Eq, Show)

instance PrClj ColumnAlias where
  pr = id

instance PrClj ResultQueryTree where
  pr (NestedRQT a b c) = "{:select " ++ pr a ++ " :from " ++ pr b ++ " :where " ++ pr c ++ "}"
  pr (SimpleRQT a b c) = "{:select " ++ pr a ++ " :from " ++  pr b ++ " :where " ++ pr c ++ "}"

instance PrClj SomeNumber where
  pr (Left x) = show x
  pr (Right x) = show x


parseFromClause :: Parser ParsedFromClause
parseFromClause = M.fromList <$> commaSep1 haskell ps
  where
    ps :: Parser (TableAlias, Either ParsedQueryTree TableName)
    ps = try ps2 <|> ps1 <|> ps3
    ps1 = do {x <- parseTableName;
              return (x, Right x)}
    ps2 = do {(tAlias, tName) <- parseAsPair parseTableName parseTableAlias;
              return (tAlias, Right tName)}
    ps3 = do {(tAlias, tQuery) <- parseAsPair parseQuery parseTableAlias;
               return (tAlias, Left tQuery)}


parseColumnAlias :: Parser ColumnAlias
parseColumnAlias = identifier haskell


parseColumnName :: Parser ColumnName
parseColumnName = identifier haskell


parseTableAlias :: Parser TableAlias
parseTableAlias = identifier haskell


parseTableName :: Parser TableName
parseTableName = identifier haskell


parseColumnEitherQualified :: Parser ColumnEitherQualified
parseColumnEitherQualified = do {
  str <- identifier haskell;
  option (Right str)
    (do {_<-string ".";
         qq <- identifier haskell;
         return $ Left $ CQ str qq
        })}


parseColumnQualified :: Parser ColumnQualified
parseColumnQualified = do {
  tab <- parseTableName;
  _   <- string ".";
  nam <- parseColumnName;
  return $ CQ tab nam
  }


-- map of alias to equalified.
-- creates dummy alias keys when not given.
parseSelectClause :: Parser ColumnMap
parseSelectClause = M.fromList <$> commaSep1 haskell part
  where
    part :: Parser (ColumnAlias, ColumnQualified)
    part = try parseWithAlias <|> parseWithoutAlias
    -- no alias is given: alis will be full qualified name with dot.
    parseWithoutAlias = do {qualified@(CQ table column) <- parseColumnQualified;
                            return (table ++ "." ++ column, qualified)}
    -- alias is given.
    parseWithAlias = parseAsPair parseColumnQualified parseColumnAlias


parseMathExpr :: Parser a -> Parser (MathExpr a)
parseMathExpr f = _start
  where
    ss s p = do{_<-string s; return p}
    _start = _sum
    -- TODO: add support for negative sign!
    -- TODO: add function calls!
    _number = do {spaces; x <- naturalOrFloat haskell; spaces;
                  let y = (case x of (Left i) -> I i; (Right d) -> D d)
                  in return y}
    _col    = do {spaces; d <- f; spaces; return $ Read d}
    _sum    = chainl1 _prod (ss "+" Add <|> ss "-" Sub)
    _prod   = chainl1 _ll   (ss "*" Mul <|> ss "/" Div)
    _ll     = parens haskell _sum <|> _col <|>_number


data LogicTree a = And (LogicTree a) (LogicTree a)
                 | Or (LogicTree a) (LogicTree a)
                 | Not (LogicTree a)
                 | Leaf a
                 deriving (Eq, Show, Ord, Functor)

instance Foldable LogicTree where
  foldMap f (Leaf x) = f x
  foldMap f (And a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Or a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Not a)  = foldMap f a

  --  fmap f x = undefined

parseLogicTree :: Parser a -> Parser (LogicTree a)
parseLogicTree pa = _start
  where
    ss s p = do{spaces; _<-string s; spaces; return p}
    _start = _or
    _or  = chainl1 _and (ss "or" Or)
    _and = chainl1 _ll   (ss "and" And)
    _not = do {_<-string "not"; spaces; x<-_ll; return $ Not x}
    _pp  = do {spaces; x <- pa; return $ Leaf x}
    _ll  = parens haskell _start <|> _not <|> _pp

-- tryParser "a and not c or b" (parseLogicTree parseColumnName)

parseWhereClause :: Parser ParsedWhereClause
parseWhereClause = parseLogicTree $ parseComp $ parseMathExpr parseColumnQualified

parseQuery :: Parser ParsedQueryTree
parseQuery = try parseSimpleQuery <|> parseAliasedQuery

parseAliasedQuery :: Parser ParsedQueryTree
parseAliasedQuery =
  do
    _<-string "SELECT";
    spaces;
    selectClause <- parseSelectClause
    spaces;
    _<-string "FROM";
    spaces;
    fromClause <- parseFromClause
    spaces;
    _<-string "WHERE";
    spaces;
    whereClause <- parseWhereClause
    return (PQT selectClause fromClause whereClause)

--data LogicTree_Disjunction a = AndD (LogicTree_Disjunction a) | NotD a | LeafD a
--	deriving (Eq)

-- warning: returns reverse pair!
parseAsPair ::Parser a -> Parser b -> Parser (b, a)
parseAsPair pa pb =
  do
    a <- pa
    spaces;
    _ <- try (string "AS") <|> string "As" <|> string "as"
    spaces;
    b <- pb
    return (b, a)

-- todo: maybe also support subQuery
parseSimpleQuery :: Parser ParsedQueryTree
parseSimpleQuery =
  do
    _ <- string "SELECT"
    spaces;
    selectClause <- parseSelect
    spaces;
    _ <- string "FROM"
    spaces;
    fromTable <- parseFrom;
    spaces;
    _ <- string "WHERE"
    spaces;
    whereClause <- parseLogicTree $ parseComp $ parseMathExpr parseColumnName;
    let tableName = getTableName fromTable in
      return $ PQT (toSelectClause tableName selectClause)
                   (toFromClause fromTable)
                   (toWhereClause tableName whereClause)
  where
    getTableName (Left _) = "$"
    getTableName (Right t) = t

    toFromClause :: Either ParsedQueryTree TableName -> ParsedFromClause
    toFromClause x = M.insert (getTableName x) x M.empty

    toSelectClause :: TableAlias -> [(ColumnAlias, ColumnName)] -> ColumnMap
    toSelectClause t = foldl (\m (a,c) -> M.insert a (CQ t c) m) M.empty

    toWhereClause :: TableAlias -> LogicTree (Comp (MathExpr ColumnName)) -> ParsedWhereClause
    toWhereClause t = fmap $ mapComp1 $ fmap $ CQ t
    --toWhereClause = undefined

    parseFrom :: Parser (Either ParsedQueryTree TableName)
    parseFrom = try  (Right <$> parseTableName)
                <|>  (Left <$> parens haskell parseQuery)

    parseSelect :: Parser [(ColumnAlias, ColumnName)]
    parseSelect = commaSep1 haskell part

    part :: Parser (ColumnAlias, ColumnName)
    part = try parseWithAlias <|> parseWithoutAlias

    parseWithoutAlias = do {q <- parseColumnName; return (q, q)}
    parseWithAlias = parseAsPair parseColumnName parseColumnAlias

-- a Clause is a disjunction of positive and negatives items.
data Clause a = PosNeg (S.Set a) (S.Set a) deriving (Eq, Show, Read, Ord)
data CNF a = Clauses (S.Set (Clause a)) deriving (Eq, Show,Read, Ord)


oneset :: (Ord a) => a -> S.Set a
oneset x = S.insert x S.empty


to_cnf :: (Ord a) => LogicTree a -> CNF a
to_cnf (And x y) = Clauses (S.union xs ys)
  where
    Clauses xs = to_cnf x
    Clauses ys = to_cnf y
to_cnf (Not (And x y)) = to_cnf (Or (Not x) (Not y))
to_cnf (Not (Or x y))  = to_cnf (And (Not x) (Not y))
to_cnf (Or x y) = Clauses $ S.fromList $ map f ps
  where
    f (PosNeg ee ff, PosNeg gg hh) = PosNeg (S.union ee gg) (S.union ff hh)
    ps = [(p,q) | p <- S.elems xs, q <- S.elems ys]
    Clauses xs = to_cnf x
    Clauses ys = to_cnf y
to_cnf (Not (Not e)) = to_cnf e
to_cnf (Not (Leaf x)) = Clauses $ oneset (PosNeg S.empty (S.insert x S.empty))
to_cnf (Leaf x) = Clauses $ oneset (PosNeg (oneset x) S.empty)


-- disjunction of positive literals
data PosClause a = PosC (S.Set a)
  deriving (Eq, Show, Read, Ord)
-- conjuction of clauses
data PosCNF a = PosClauses (S.Set (PosClause a))
  deriving (Eq, Show, Read, Ord)

-- collectPosCnfLiterals :: PosCNF a -> [a]
-- collectPosCnfLiterals (PosClauses cs) = concatMap (\ (PosC c) -> S.elems c) (S.elems cs)

conjunction :: (Ord a) => PosCNF a -> PosCNF a -> PosCNF a
conjunction (PosClauses x) (PosClauses y) = PosClauses $ S.union x y


toPosCnf :: (Ord a) => CNF (Comp a) -> PosCNF (Comp a)
toPosCnf (Clauses cs) = PosClauses (S.map f cs)
  where f (PosNeg gg hh) = PosC (S.union gg (S.map negateComp hh))


-- like `fmap` for PosCNF
mapPosCnfLiterals :: (Ord a) => (Ord b) => (a -> b) -> PosCNF a -> PosCNF b
mapPosCnfLiterals f (PosClauses cs) =
  PosClauses (S.map (\ (PosC c) -> PosC (S.map f c)) cs)


compToCompOrder :: Comp a -> b -> c -> CompOrder b c
compToCompOrder (CST _ _) = CST
compToCompOrder (CLT _ _) = CLT
compToCompOrder (CEQ _ _) = CEQ
compToCompOrder (CNEQ _ _) = CNEQ
compToCompOrder (CSEQ _ _) = CSEQ
compToCompOrder (CLEQ _ _) = CLEQ

-- visitComp :: ((a -> a -> Comp a) -> a -> a -> b) -> Comp a -> b

  -- try to produce left aligned conditions.
maybeLeftAlign :: Comp (MathExpr t) -> Maybe (CompOrder t SomeNumber)
maybeLeftAlign t = f a b
  where
    f (Read c) x = case maybeEvalMath x of
      Just (Left d)  -> Just $ compToCompOrder t c $ Left d
      Just (Right i) -> Just $ compToCompOrder t c $ Right i
      Nothing ->  Nothing
    f x (Read c) = case maybeEvalMath x of
      Just (Left d)  -> Just $ compToCompOrder (flipComp t) c $ Left d
      Just (Right i) -> Just $ compToCompOrder (flipComp t) c $ Right i
      Nothing ->  Nothing
    f _  _ = Nothing
    (a, b) = getCompSides t


--maybeEquation :: Comp (MathExpr t) -> Maybe (t,t)
--maybeEquation (CEQ (Read a) (Read b)) = Just (a,b)
--maybeEquation _ = Nothing


tryParser :: String -> Parser a -> Either ParseError a
tryParser s p = runParser p () "" s


groupMapBy :: (Ord k) => (a -> k) -> [a] -> M.Map k [a]
groupMapBy f = foldl (\a x->  (M.insertWith (++) (f x) [x] a)) M.empty

-- assert: xs is not empty.
maybeAllMapToSame :: (Eq k) => (a->k) -> [a] -> Maybe k
maybeAllMapToSame _ [] = Nothing
maybeAllMapToSame f (x : xs) = if all ((== f x) . f) xs then Just (f x) else Nothing


-- given cnf -> collects clauses with same table alias on left side. (and rest clauses)
splitPosCnfCompOrder ::
  PosCNF (CompOrder ColumnQualified SomeNumber)
  -> (Maybe (PosCNF (CompOrder ColumnQualified SomeNumber)),
      M.Map TableAlias (PosCNF (CompOrder ColumnName SomeNumber)))
splitPosCnfCompOrder (PosClauses pcnf) = (common, spec)
  where
    common = liftM (PosClauses . S.fromList) (M.lookup Nothing m)
    spec :: M.Map TableAlias (PosCNF (CompOrder ColumnName SomeNumber))
    spec =  M.foldlWithKey (\mm k v ->
                              (case k of  -- v is a list
                                 Just a -> M.insert a (mapPosCnfLiterals
                                                       (mapComp (\(CQ _ c) -> c) id)
                                                       (PosClauses (S.fromList v))) mm
                                 Nothing -> mm)) M.empty m

    m :: M.Map (Maybe TableAlias) [PosClause (CompOrder ColumnQualified SomeNumber)]
    m = groupMapBy maybeHomogenClause (S.elems pcnf)

    -- RETURN TableAlias when all literal share the same.
    maybeHomogenClause :: PosClause (CompOrder ColumnQualified SomeNumber) -> Maybe TableAlias
    maybeHomogenClause (PosC clauseSet) =
      maybeAllMapToSame ((\(CQ c _) -> c) . fst . elemsCompOrder) (S.elems clauseSet)

type ParsedComp = Comp (MathExpr ColumnQualified)



-- orders as much conditions as possible.
prepareWhereClauseFlatten
  :: PosCNF ParsedComp
        -> (Maybe (PosCNF ParsedComp), Maybe (PosCNF (CompOrder ColumnQualified SomeNumber)))
prepareWhereClauseFlatten (PosClauses clauses) = (build bb, build aa)
  where
    --- Comp to CompOrder -> MaybeLeftAlign
    doClause :: PosClause ParsedComp -> Maybe (PosClause (CompOrder ColumnQualified SomeNumber))
    doClause (PosC clause) = liftM (PosC . S.fromList) $ mapM maybeLeftAlign $ S.elems clause
    build set = if S.null set then Nothing else Just $ PosClauses set
    (aa,bb) = foldl (\(a,b) x ->
                  case doClause x of
                    Just t  -> (S.insert t a, b);
                    Nothing -> (a, S.insert x b))
              (S.empty,S.empty) (S.elems clauses)


-- first value: CNF that could either not be left aligned or contains join statemt.
-- second value: left aligned cnf in map by table alias name.
prepareWhereClause :: LogicTree ParsedComp
                   -> (Maybe (PosCNF ParsedComp),
                       M.Map TableAlias (PosCNF (CompOrder ColumnName SomeNumber)))
prepareWhereClause tree = rrr
  where
    (mixCnfMaybe , orderCnfMaybe) = prepareWhereClauseFlatten $ toPosCnf $ to_cnf tree
    --convertBack :: PosCNF (CompOrder ColumnQualified SomeNumber) -> PosCNF ParsedComp
    convertBack = mapPosCnfLiterals (mapComp Read someNumberMathExpr)
    rrr = case orderCnfMaybe of
      Nothing -> (mixCnfMaybe, M.empty)
      Just lefts -> case splitPosCnfCompOrder lefts of
                      (Nothing, m) -> (mixCnfMaybe, m)
                      (Just aa, m) -> case mixCnfMaybe of
                                        Nothing -> (Just $ convertBack aa , m);
                                        Just bb -> (Just $ conjunction (convertBack aa) bb, m)


mapAssoc2 :: (Ord a, Ord b) => a-> b-> c -> M.Map a (M.Map b c) -> M.Map a (M.Map b c)
mapAssoc2 k1 k2 v m = case M.lookup k1 m of
  Nothing -> M.insert k1 (M.insert k2 v M.empty) m
  Just m2 -> M.insert k1 (M.insert k2 v m2)      m


processTreeSimple :: M.Map ColumnAlias ColumnName
  -> TableName -> PosCNF (CompOrder ColumnName SomeNumber)  -> ResultQueryTree
processTreeSimple = SimpleRQT


data ProcessError = PE String deriving (Eq, Show, Ord)

instance PrClj ProcessError where
  pr (PE s) = "{:error " ++ show s ++"}"



-- parse and move names, aliases, expressions to right layer.
processTree :: ParsedQueryTree -> Either ProcessError ResultQueryTree
processTree (PQT columnMap tableMap whereClause)

  -- and unknown table alias is used in a WHERE condition
  | (Just t) <- msum $ fmap (\(CQ t _) ->
                                if not $ M.member t tableMap
                                then Just t else Nothing)  (collectCQ whereClause)
  = Left $ PE $ "Unexpected table name in WHERE clause: " ++ t

  -- an unknown table alias is used in SELECT clause
  | (Just t) <-  msum $ fmap (\(CQ t _) ->
                                if not $ M.member t tableMap
                                then Just t else Nothing) (M.elems columnMap)
    = Left $ PE $ "Unecpected table name in SELECT clause: " ++ t

  --- => SELECT ... FROM tname WHERE ...
  | [(tAlias, Right tName)] <- M.assocs tableMap,
    (Just cnf)              <- M.lookup tAlias whereMap
                               -- maybe alias for full table name too.
  = case whereJoin of
      Nothing -> Right $ processTreeSimple cMap tName cnf
      (Just joinClause) -> Right parent
        where
          child  = SimpleRQT cMap tName cnf
          parent = NestedRQT pc m parentJoin
          pc     = M.mapWithKey (\k (CQ q _) -> CQ q k) columnMap
          m      = M.insert tAlias child M.empty
          parentJoin =  joinClause -- maybe rework it?

  --- => SELECT ... FROM (SELECT ...) WHERE ...
  | [(tAlias, Left _)] <- M.assocs tableMap,
    (Just _)           <- M.lookup tAlias whereMap
  = case whereJoin of
      -- outer table has only left-aligned filters -> can be moven inwards.
      -- TODO: implement this
      Nothing -> Left $ PE "No JOIN on outer table.."
      -- outer table has mixed filters.
      -- TODO: implement this.
      (Just _) -> Left $ PE "not implemented: outer table has mixed filters"
 {-       case processTree subTable of
          (Left pe) -> Left pe;
          (Right child) -> Right $ NestedRQT pc m parentJoin
            where
              pc     = M.mapWithKey (\k (CQ q _) -> CQ q k) columnMap
              m      = M.insert tAlias child M.empty
              parentJoin =  joinClause -- maybe rework it?
-}

  --- => SELECT t1, ... FROM ... WHERE
  | [(tAlias, Right tName)] <- M.assocs tableMap,
    Nothing                 <- M.lookup tAlias whereMap -- maybe alias for full table name too.
  = Left $ PE $ "No WHERE conditions for table name: " ++ tName
  | Nothing <- whereJoin
  = Left $ PE "Missing JOIN conditions!"
  | (Left b) <- subTables
  = Left b   -- when error while crating subtable.
  | (Right tts)           <- subTables,
    (Just joinConditions) <- whereJoin
  =  Right $ NestedRQT columnMap tts joinConditions
  | otherwise = Left $ PE "Unexpected case"
  where
    subTables = M.traverseWithKey makeSubTable tableMap
    makeSubTable :: TableAlias -> Either ParsedQueryTree TableName
                 -> Either ProcessError ResultQueryTree
    makeSubTable sTabAlias (Left pqt) =
      case M.lookup sTabAlias whereMap of
        Nothing -> processTree pqt
        (Just cnf) ->
          case processTree pqt of
            (Right (NestedRQT as tsm cnf2)) ->
              Right $ NestedRQT as tsm (conjunction cnf2
                   (mapPosCnfLiterals
                     (mapComp (Read . aliasToQualified) numberToMathExpr) cnf))
            (Right (SimpleRQT as tsm cnf2)) ->
              Right $ SimpleRQT as tsm (conjunction cnf cnf2)
            (Left a) -> Left a
    makeSubTable sTabAlias (Right subTableName)
      |        (Just cnf) <- M.lookup sTabAlias whereMap,
        (Just colAliases) <- M.lookup sTabAlias subTableColAliases
      = Right $ SimpleRQT colAliases subTableName cnf
      | otherwise = Left $ PE "SELECT or WHERE clause is missing."
    cMap = M.map (\(CQ _ columnName) -> columnName) columnMap

    aliasToQualified ::ColumnAlias -> ColumnQualified
    aliasToQualified x = cq
      where (Just cq) = M.lookup x columnMap

    (whereJoin, whereMap) = prepareWhereClause whereClause
    subTableColAliases = M.foldlWithKey (\m ca (CQ ta cn) -> mapAssoc2 ta ca cn m)
                           M.empty columnMap

-- TODO: Date support.
-- TODO: JOIN ON support.
-- TODO: equivalence classes on conditions.
-- TODO: test nested selects.

handleLine :: String -> IO ()
handleLine line =
  case runParser parseQuery () "" line of
    (Left _) ->  putStrLn ":error"--putStrLn $ pr a
    (Right b) -> case processTree b of
                   (Left err) -> putStrLn $ pr err
                   (Right tree) -> putStrLn $ pr tree

main :: IO ()
main = do
  c <- getContents;
  forM_ (lines c) handleLine

-- END
