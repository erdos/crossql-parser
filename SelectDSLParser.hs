#!/usr/bin/env runhaskell

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Main (parseColumnEitherQualified, tryParser, main, mergeFromClauses, parseJoin, Formula(..)) where

import Control.Monad
import Control.Applicative ((<$>))

import Data.Char(toUpper)

import qualified Data.Set as S
  (Set, union, empty, insert, elems, fromList,map, null, intersection,size)
import qualified Data.Map.Strict as M
  (Map, fromList, empty, insertWith, lookup, foldlWithKey, insert,  assocs, map,
    mapWithKey, traverseWithKey, elems, member, alter, intersection, union, null)

import Data.Either()
import Data.Foldable (Foldable, foldMap, concat, find)
import Data.List (intercalate)
import Data.Maybe(listToMaybe, mapMaybe, fromMaybe)
import Data.Monoid (mempty, mappend)

import System.IO (hSetBuffering, BufferMode(LineBuffering), stdout)

import Text.Parsec as TP
  (ParseError, (<?>), (<|>), chainl1, string,runParser, spaces, try, sepBy1, satisfy, letter, alphaNum, many, many1, oneOf, char, noneOf)
import Text.Parsec.Combinator (option)
import Text.Parsec.Error (Message(..), errorMessages)
import Text.Parsec.Language
import Text.Parsec.String as TPS
import Text.Parsec.Token as TPT


data SomeScalar = DD Double | II Integer | SS String deriving (Eq, Show, Ord)

data MathExpr a = D Double | I Integer | S String | Read a
                | Add (MathExpr a) (MathExpr a)
                | Sub (MathExpr a) (MathExpr a)
                | Mul (MathExpr a) (MathExpr a)
                | Div (MathExpr a) (MathExpr a)
                deriving (Eq, Show, Ord, Functor)

-- not used (yet)
data Formula a t where
  Cell :: t -> Formula a t
  LitI :: Int -> Formula Int t
  LitS :: String -> Formula String t
  LitD :: Double -> Formula Double t
  IToD :: Formula Int t -> Formula Double t
  IToS :: Formula Int t -> Formula String t
  DToS :: Formula Double t -> Formula String t
  -- integer
  AddI :: Formula Int t -> Formula Int t -> Formula Int t
  SubI :: Formula Int t -> Formula Int t -> Formula Int t
  MulI :: Formula Int t -> Formula Int t -> Formula Int t
  QuotI :: Formula Int t -> Formula Int t -> Formula Int t
  -- doubles
  AddD :: Formula Double t -> Formula Double t -> Formula Double t
  SubD :: Formula Double t -> Formula Double t -> Formula Double t
  MulD :: Formula Double t -> Formula Double t -> Formula Double t
  DivD :: Formula Double t -> Formula Double t -> Formula Double t
  -- string
  Concat :: Formula String t -> Formula String t -> Formula String t


collectReads :: MathExpr a -> [a]
collectReads (Read a) = [a]
collectReads (D _) = []
collectReads (I _) = []
collectReads (S _) = []
collectReads (Add x y) = collectReads x ++ collectReads y
collectReads (Sub x y) = collectReads x ++ collectReads y
collectReads (Mul x y) = collectReads x ++ collectReads y
collectReads (Div x y) = collectReads x ++ collectReads y


instance Foldable MathExpr where
  foldMap f (Read x) = f x
  foldMap _ (I _) = mempty
  foldMap _ (D _) = mempty
  foldMap _ (S _) = mempty
  foldMap f (Add a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Sub a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Mul a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Div a b) = foldMap f a `mappend` foldMap f b


scalarToMathExpr :: SomeScalar -> MathExpr a
scalarToMathExpr (DD d) = D d
scalarToMathExpr (II i) = I i
scalarToMathExpr (SS s) = S s


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
  pr (S s) = show s
  pr (Read t) = pr t
  pr (Add a b) = "(+ " ++ pr a ++ " " ++ pr b ++ ")"
  pr (Sub a b) = "(- " ++ pr a ++ " " ++ pr b ++ ")"
  pr (Mul a b) = "(* " ++ pr a ++ " " ++ pr b ++ ")"
  pr (Div a b) = "(/ " ++ pr a ++ " " ++ pr b ++ ")"


instance PrClj ColumnQualified where
  pr (CQ (TA a) (CN b)) = a ++ "/" ++ b


instance (PrClj a, PrClj b) => PrClj (CompOrder a b) where
  pr (CEQ a b) = "(== " ++ pr a ++ " " ++ pr b ++")"
  pr (CNEQ a b) = "(!= " ++ pr a ++ " " ++ pr b ++")"
  pr (CLEQ a b) = "(>= " ++ pr a ++ " " ++ pr b ++")"
  pr (CSEQ a b) = "(<= " ++ pr a ++ " " ++ pr b ++")"
  pr (CLT a b) = "(> " ++ pr a ++ " " ++ pr b ++")"
  pr (CST a b) = "(< " ++ pr a ++ " " ++ pr b ++")"


instance (PrClj a) => PrClj (PosCNF a) where
  pr (PosClauses cs) = "(cnf " ++ unwords (map f $ S.elems cs) ++ ")"
    where
      f (PosC c) = "[" ++ unwords (map pr (S.elems c)) ++ "]"

instance (PrClj a, PrClj b) => PrClj (M.Map a b) where
  pr m = "{"
    ++ intercalate ", " (map (\(k,v)-> pr k ++ " " ++ pr v) $ M.assocs m)
    ++ "}"


-- someNumberMathExpr :: SomeNumber -> MathExpr a
-- someNumberMathExpr (Left i) = I i
-- someNumberMathExpr (Right d) = D d

someScalarMathExpr :: SomeScalar -> MathExpr a
someScalarMathExpr (II i) = I i
someScalarMathExpr (DD d) = D d
someScalarMathExpr (SS s) = S s

maybeEvalScalar :: MathExpr t -> Maybe SomeScalar
maybeEvalScalar expr = case simplifyMathExpr expr of
  (D d) -> Just $ DD d
  (I i) -> Just $ II i
  (S s) -> Just $ SS s
  _ -> Nothing

simplifyMathExpr :: forall t. MathExpr t -> MathExpr t
simplifyMathExpr expr = case expr of
  (Add a b) -> ccc expr a b ((Just .) . (+)) ((Just .) . (+)) ((Just .) . (++))
  (Sub a b) -> ccc expr a b ((Just .) . (-)) ((Just .) . (-)) (\ _ _ -> Nothing)
  (Mul a b) -> ccc expr a b ((Just .) . (*)) ((Just .) . (*)) (\ _ _ -> Nothing)
  (Div a b) -> ccc expr a b ((Just .) . div) ((Just .) . (/)) (\ _ _ -> Nothing)
  _ -> expr
  where
    ccc original x y f g h = fromMaybe original $ calc x y f g h
    calc x y f g h = op f g h (simplifyMathExpr x) (simplifyMathExpr y)
    op _ f _ (D i) (D j) = liftM D $ f i j
    op _ f _ (I i) (D d) = liftM D $ f (fromIntegral i) d
    op _ f _ (D d) (I i) = liftM D $ f d (fromIntegral i)
    op f _ _ (I x) (I y) = liftM I $ f x y
    op _ _ f (S s) (D d) = liftM S $ f s (show d)
    op _ _ f (S s) (I i) = liftM S $ f s (show i)
    op _ _ f (D d) (S s) = liftM S $ f (show d) s
    op _ _ f (I i) (S s) = liftM S $ f (show i) s
    op _ _ _ _ _ = Nothing



{-
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
-}
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
    op =  try (x "<>" CNEQ)
      <|> try (x "<=" CSEQ) <|> x "<" CST
      <|> try (x ">=" CLEQ) <|> x ">" CLT
      <|> try (x "==" CEQ)  <|> x "=" CEQ
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
  (CST a b)  -> CLT  b a
  (CLT a b)  -> CST  b a
  (CEQ a b)  -> CEQ  b a
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

newtype ColumnName  = CN String deriving (Show, Eq, Ord)
newtype ColumnAlias = CA String deriving (Show, Eq, Ord)
newtype TableName   = TN String deriving (Show, Eq, Ord)
newtype TableAlias  = TA String deriving (Show, Eq, Ord)


data ColumnQualified = CQ TableAlias ColumnName deriving (Show, Eq, Ord)
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

instance PrClj SomeScalar where
  pr (II x) = show x
  pr (DD x) = show x
  pr (SS x) = show x

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


-- case insensitive string matching
stringI :: String -> Parser String
stringI cs = mapM caseChar cs <?> cs where
  caseChar c = satisfy (\x -> toUpper x == toUpper c)

parseIdentifier :: Parser String
parseIdentifier = idBacktick <|> id1
  where
    idBacktick = do {
      _ <- char '`';
      s <- many1 $ noneOf "`" ; -- satisfy (/= '`');
      _ <- char '`';
      return s}
    id1 = do {
      firstChar <- letter <|> oneOf "_$";
      restChar <- many (alphaNum <|> oneOf "_:$");
      return $ firstChar : restChar}



parseColumnEitherQualified :: Parser ColumnEitherQualified
parseColumnEitherQualified = do {
  str <- parseIdentifier;
  option (Right (CA str))
    (do {_<-string ".";
         qq <- parseIdentifier;
         return $ Left $ CQ (TA str) (CN qq)
        })}


parseColumnQualified :: Parser ColumnQualified
parseColumnQualified = do {
  tab <- parseTableAlias;
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
    parseWithoutAlias = do {qualified@(CQ (TA table) (CN column)) <- parseColumnQualified;
                            return (CA $  table ++ "." ++
                                    column, qualified)}
    -- alias is given.
    parseWithAlias = parseAsPair parseColumnQualified parseColumnAlias


parseMathExpr :: Parser a -> Parser (MathExpr a)
parseMathExpr f = _start
  where
    ss s p = do{_<-string s; return p}
    _start = _sum
    -- TODO: add support for negative sign!
    -- TODO: add function calls!
    _number = do {x <- naturalOrFloat haskell;
                  return (case x of (Left i) -> I i; (Right d) -> D d)}
    _string = S <$> stringLiteral haskell
    _col    = Read <$> f
    _sum    = chainl1 _prod (ss "+" Add <|> ss "-" Sub)
    _prod   = chainl1 _ll   (ss "*" Mul <|> ss "/" Div)
    _atom   = parens haskell _sum <|> _col <|> _number<|>_string
    _ll     = do{spaces; x <- _atom; spaces; return x} --parens haskell _sum <|> _col <|>_number <|> _string


data LogicTree a = And (LogicTree a) (LogicTree a)
                 | Or  (LogicTree a) (LogicTree a)
                 | Not (LogicTree a)
                 | Leaf a
                 deriving (Eq, Show, Ord, Functor)


instance Foldable LogicTree where
  foldMap f (Leaf x) = f x
  foldMap f (And a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Or a b) = foldMap f a `mappend` foldMap f b
  foldMap f (Not a)  = foldMap f a


parseLogicTree :: Parser a -> Parser (LogicTree a)
parseLogicTree pa = _start
  where
    ss s p = do{spaces; _<-stringI s; spaces; return p}
    _start = _or
    _or  = chainl1 _and (ss "or" Or)
    _and = chainl1 _ll   (ss "and" And)
    _not = do {_<-stringI "not"; spaces; x<-_ll; return $ Not x}
    _pp  = do {spaces; x <- pa; return $ Leaf x}
    _ll  = parens haskell _start <|> _not <|> _pp

-- tryParser "a and not c or b" (parseLogicTree parseColumnName)

parseWhereClause1 :: forall a. Parser a -> Parser (LogicTree (Comp (MathExpr a)))
parseWhereClause1 p = unfoldLogicTree <$> parseLogicTree (try parse_between <|> (Leaf <$> pc))
  where
    pc :: Parser (Comp (MathExpr a))
    pc = parseComp $ parseMathExpr p

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

unfoldLogicTree :: LogicTree (LogicTree a) -> LogicTree a
unfoldLogicTree (And a b) = And (unfoldLogicTree a) (unfoldLogicTree b)
unfoldLogicTree (Or a b) = Or (unfoldLogicTree a) (unfoldLogicTree b)
unfoldLogicTree (Not a) = Not (unfoldLogicTree a)
unfoldLogicTree (Leaf x) = x


parseWhereClause :: Parser ParsedWhereClause
parseWhereClause = parseWhereClause1 parseColumnQualified

parseQuery :: Parser ParsedQueryTree
parseQuery = try parseSimpleQuery <|> parseAliasedQuery

parseAliasedQuery :: Parser ParsedQueryTree
parseAliasedQuery =
  do
    _<-stringI "SELECT";
    spaces;
    selectClause <- parseSelectClause
    spaces;
    _<-stringI "FROM";
    spaces;
    fromClause <- parseFromClause
    spaces;
    _<-stringI "WHERE";
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
    _ <- stringI "AS"
    spaces;
    b <- pb
    return (b, a)


-- parses a query with one tablename/table in it, no aliases
-- todo: maybe also support subQuery
parseSimpleQuery :: Parser ParsedQueryTree
parseSimpleQuery =
  do
    _ <- stringI "SELECT"
    spaces;
    selectClause <- parseSelect
    spaces;
    _ <- stringI "FROM"
    spaces;
    fromTable <- parseFrom;
    spaces;
    _ <- stringI "WHERE"
    spaces;
    whereClause <- parseWhereClause1 parseColumnName;
    let tableName = getTableAlias fromTable in
      return $ PQT (toSelectClause tableName selectClause)
                   (toFromClause fromTable)
                   (toWhereClause tableName whereClause)
  where
    -- alias is either table name or "$" when subquery.
    getTableAlias :: Either ParsedQueryTree TableName -> TableAlias
    getTableAlias (Left _) = TA "$"
    getTableAlias (Right (TN tn)) = TA tn

    toFromClause :: Either ParsedQueryTree TableName -> ParsedFromClause
    toFromClause x = M.insert (getTableAlias x) x M.empty

    toSelectClause :: TableAlias -> [(ColumnAlias, ColumnName)] -> ColumnMap
    toSelectClause t = foldl (\m (a,c) -> M.insert a (CQ t c) m) M.empty

    toWhereClause :: TableAlias -> LogicTree (Comp (MathExpr ColumnName)) -> ParsedWhereClause
    toWhereClause t = fmap $ mapComp1 $ fmap $ CQ t

    parseFrom :: Parser (Either ParsedQueryTree TableName)
    parseFrom = try  (Right <$> parseTableName)
                <|>  (Left <$> parens haskell parseQuery)

    parseSelect :: Parser [(ColumnAlias, ColumnName)]
    parseSelect = commaSep1 haskell part

    part :: Parser (ColumnAlias, ColumnName)
    part = try parseWithAlias <|> parseWithoutAlias

    parseWithoutAlias = do {(CN cn) <- parseColumnName; return (CA cn, CN cn)}
    parseWithAlias = parseAsPair parseColumnName parseColumnAlias

-- a Clause is a disjunction of positive and negatives items.
data Clause a = PosNeg (S.Set a) (S.Set a) deriving (Eq, Show, Read, Ord)
data CNF a = Clauses (S.Set (Clause a)) deriving (Eq, Show,Read, Ord)


oneset :: (Ord a) => a -> S.Set a
oneset x = S.insert x S.empty


toCnf :: (Ord a) => LogicTree a -> CNF a
toCnf (And x y) = Clauses (S.union xs ys)
  where
    Clauses xs = toCnf x
    Clauses ys = toCnf y
toCnf (Not (And x y)) = toCnf (Or (Not x) (Not y))
toCnf (Not (Or x y))  = toCnf (And (Not x) (Not y))
toCnf (Or x y) = Clauses $ S.fromList $ map f ps
  where
    f (PosNeg ee ff, PosNeg gg hh) = PosNeg (S.union ee gg) (S.union ff hh)
    ps = [(p,q) | p <- S.elems xs, q <- S.elems ys]
    Clauses xs = toCnf x
    Clauses ys = toCnf y
toCnf (Not (Not e)) = toCnf e
toCnf (Not (Leaf x)) = Clauses $ oneset (PosNeg S.empty (S.insert x S.empty))
toCnf (Leaf x) = Clauses $ oneset (PosNeg (oneset x) S.empty)


-- disjunction of positive literals
data PosClause a = PosC (S.Set a)
  deriving (Eq, Show, Read, Ord)
-- conjuction of clauses
data PosCNF a = PosClauses (S.Set (PosClause a))
  deriving (Eq, Show, Read, Ord)


toPosCnf :: (Ord a) => CNF (Comp a) -> PosCNF (Comp a)
toPosCnf (Clauses cs) = PosClauses (S.map f cs)
  where f (PosNeg gg hh) = PosC (S.union gg (S.map negateComp hh))

collectPosCnfLiterals :: PosCNF a -> [a]
collectPosCnfLiterals (PosClauses cs) = concatMap (\ (PosC c) -> S.elems c) (S.elems cs)

conjunction :: (Ord a) => PosCNF a -> PosCNF a -> PosCNF a
conjunction (PosClauses x) (PosClauses y) = PosClauses $ S.union x y

-- like `fmap` for PosCNF
mapPosCnfLiterals :: (Ord a) => (Ord b) => (a -> b) -> PosCNF a -> PosCNF b
mapPosCnfLiterals f (PosClauses cs) =
  PosClauses (S.map (\ (PosC c) -> PosC (S.map f c)) cs)

cnfAddClause :: (Ord a) => PosClause a -> PosCNF a -> PosCNF a
cnfAddClause x (PosClauses cs) = PosClauses (S.insert x cs)

-- visitComp :: ((a -> a -> Comp a) -> a -> a -> b) -> Comp a -> b

  -- try to produce left aligned conditions.
maybeLeftAlign :: Comp (MathExpr t) -> Maybe (CompOrder t SomeScalar)
maybeLeftAlign t = f a b
  where
    f (Read c) x = case maybeEvalScalar x of
      Just (DD d)  -> Just $ compToCompOrder t c $ DD d
      Just (II i) -> Just $ compToCompOrder t c $ II i
      Just (SS s) -> Just $ compToCompOrder t c $ SS s
      Nothing ->  Nothing
    f x (Read c) = case maybeEvalScalar x of
      Just (DD d)  -> Just $ compToCompOrder (flipComp t) c $ DD d
      Just (II i) -> Just $ compToCompOrder (flipComp t) c $ II i
      Just (SS s) -> Just $ compToCompOrder (flipComp t) c $ SS s
      Nothing ->  Nothing
    f _  _ = Nothing
    (a, b) = getCompSides t

    compToCompOrder :: Comp a -> b -> c -> CompOrder b c
    compToCompOrder (CST _ _) = CST
    compToCompOrder (CLT _ _) = CLT
    compToCompOrder (CEQ _ _) = CEQ
    compToCompOrder (CNEQ _ _) = CNEQ
    compToCompOrder (CSEQ _ _) = CSEQ
    compToCompOrder (CLEQ _ _) = CLEQ


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
  PosCNF (CompOrder ColumnQualified SomeScalar)
  -> (Maybe (PosCNF (CompOrder ColumnQualified SomeScalar)),
      M.Map TableAlias (PosCNF (CompOrder ColumnName SomeScalar)))
splitPosCnfCompOrder (PosClauses pcnf) = (common, spec)
  where
    common = liftM (PosClauses . S.fromList) (M.lookup Nothing m)
    spec :: M.Map TableAlias (PosCNF (CompOrder ColumnName SomeScalar))
    spec =  M.foldlWithKey (\mm k v ->
                              (case k of  -- v is a list
                                 Just a -> M.insert a (mapPosCnfLiterals
                                                       (mapComp (\(CQ _ c) -> c) id)
                                                       (PosClauses (S.fromList v))) mm
                                 Nothing -> mm)) M.empty m

    m :: M.Map (Maybe TableAlias) [PosClause (CompOrder ColumnQualified SomeScalar)]
    m = groupMapBy maybeHomogenClause (S.elems pcnf)

    -- RETURN TableAlias when all literal share the same.
    maybeHomogenClause :: PosClause (CompOrder ColumnQualified SomeScalar) -> Maybe TableAlias
    maybeHomogenClause (PosC clauseSet) =
      maybeAllMapToSame ((\(CQ c _) -> c) . fst . elemsCompOrder) (S.elems clauseSet)


type ParsedComp = Comp (MathExpr ColumnQualified)


-- orders as much conditions as possible.
prepareWhereClauseFlatten
  :: PosCNF ParsedComp
        -> (Maybe (PosCNF ParsedComp), Maybe (PosCNF (CompOrder ColumnQualified SomeScalar)))
prepareWhereClauseFlatten (PosClauses clauses) = case (build bb, build aa) of
  -- if we have conditions to both filter and join and we have an equavalence join condition:
  -- then we create conditions that are implications of the equivalence.
  -- for example:
  -- (a.data==b.data and a.data>1) => (a.data==b.data and a.data>1 and b.data>1)
  (Just joinCnf, Just filterCnf) -> (Just joinCnf, Just (make_cnf joinCnf filterCnf))
  any_other_pair                 -> any_other_pair
  where
    make_eqs (PosClauses joinClauses) = [(l, r) | (PosC clause) <- S.elems joinClauses,
                                         1 == S.size clause,
                                         (CEQ (Read l) (Read r)) <- S.elems clause]
    make_cnf joinCnf = expandEquivalences (make_eqs joinCnf)
    --- Comp to CompOrder -> MaybeLeftAlign
    doClause :: PosClause ParsedComp -> Maybe (PosClause (CompOrder ColumnQualified SomeScalar))
    doClause (PosC clause) = liftM (PosC . S.fromList) $ mapM maybeLeftAlign $ S.elems clause
    build set = if S.null set then Nothing else Just $ PosClauses set
    (aa,bb) = foldl (\(a,b) x -> case doClause x of
                                   Just t  -> (S.insert t a, b);
                                   Nothing -> (a, S.insert x b))
                                                 (S.empty,S.empty) (S.elems clauses)


-- first value: CNF that could either not be left aligned or contains join statemt.
-- second value: left aligned cnf in map by table alias name.
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
    (mixCnfMaybe , orderCnfMaybe) = prepareWhereClauseFlatten $ toPosCnf $ toCnf tree
    convertBack :: PosCNF (CompOrder ColumnQualified SomeScalar) -> PosCNF ParsedComp
    convertBack = mapPosCnfLiterals (mapComp Read someScalarMathExpr)


mapAssoc2 :: (Ord a, Ord b) => a-> b-> c -> M.Map a (M.Map b c) -> M.Map a (M.Map b c)
mapAssoc2 k1 k2 v m = case M.lookup k1 m of
  Nothing -> M.insert k1 (M.insert k2 v M.empty) m
  Just m2 -> M.insert k1 (M.insert k2 v m2)      m


data ProcessError = PE String deriving (Eq, Show, Ord)


instance PrClj ProcessError where
  pr (PE s) = "{:error " ++ show s ++"}"


-- parse and move names, aliases, expressions to right layer.
processTree :: ParsedQueryTree -> Either ProcessError ResultQueryTree

-- an unknown table alias is used in the WHERE clause
processTree (PQT _ tableMap whereClause)
  | (Just (TA tAlias)) <- msum $ f <$> collectCQ whereClause
  = Left $ PE $ "Unexpected table name in WHERE clause: " ++ tAlias
  where f (CQ t _) = if not $ M.member t tableMap then Just t else Nothing

-- an unknown table alias is used in SELECT clause
processTree (PQT columnMap tableMap _)
  | (Just (TA tAlias)) <- msum $ f <$> M.elems columnMap
  = Left $ PE $ "Unecpected table name in SELECT clause: " ++ tAlias
  where f (CQ t _) = if not $ M.member t tableMap then Just t else Nothing

processTree (PQT columnMap tableMap whereClause)
  --- => SELECT ... FROM tname WHERE ...
  | [(tAlias, Right tName)] <- M.assocs tableMap,
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
          columnsFromJoinClause = concatMap collectReads $ concatMap (\(x,y) -> [x,y]) $ map getCompSides $ collectPosCnfLiterals parentJoin
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
  | [(tAlias, Right (TN tName))] <- M.assocs tableMap,
    Nothing <- M.lookup tAlias whereMap -- maybe alias for full table name too.
  = Left $ PE $ "No WHERE conditions for table name: " ++ tName
  | Nothing <- whereJoin
  = Left $ PE "Missing JOIN conditions!"
  | (Left b) <- subTables
  = Left b   -- when error while crating subtable.
  -- general case:
  --- => SELECT t1, ... FROM ... WHERE ...
  | (Right tts)           <- subTables,
    (Just joinConditions) <- whereJoin
    -- here: filter aliases from select and condition and replace them with aliases from subtables.
  = let columnsFromJoinClause = concatMap collectReads $ concatMap (\(x,y) -> [x,y]) $ map getCompSides $ collectPosCnfLiterals joinConditions
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
  -- where newColumnMap = columnMap
  | otherwise = Left $ PE "Unexpected case"
  where

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
            (Right (NestedRQT as tsm cnf2)) -> Right (NestedRQT asSimple tsm mergedWhereClause)
              where
                cnfColNameToAlias = mapPosCnfLiterals $ mapComp (\(CN x) -> CA x) id
                aliasToQualified x = cq where (Just cq) = M.lookup x columnMap -- what if!
                asSimple = M.fromList $ map (\ (CA _, CQ ta (CN cn)) -> (CA cn, CQ ta (CN cn))) $ M.assocs as
                -- TODO: maybe map back col aliases in cnf to col names (using `as`)
                mergedWhereClause = conjunction cnf2
                                      (mapPosCnfLiterals
                                        (mapComp (Read . aliasToQualified)
                                         scalarToMathExpr) (cnfColNameToAlias cnf))
            (Right (SimpleRQT as tsm cnf2)) -> Right $ SimpleRQT asSimple tsm (conjunction cnfRenamed cnf2)
              where
                -- we map back column aliases in the WHERE clause
                cnfRenamed = mapPosCnfLiterals (mapComp mapColName id) cnf
                mapColName :: ColumnName -> ColumnName
                mapColName (CN colName) = case M.lookup (CA colName) as of
                  (Just cn) -> cn
                  Nothing   -> CN colName
                -- we map back column aliases in the SELECT clause.
                asSimple = M.fromList $ map (\ (CA _, CN cn) -> (nameToAlias (CN cn), CN cn)) $ M.assocs as
                nameToAlias :: ColumnName -> ColumnAlias
                nameToAlias (CN cn) = case find (\(_, CN v) -> v == cn) (M.assocs as) of
                                        Nothing -> CA cn
                                        Just (k, _) -> k
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


-- tries to merge two FromClause maps, return Nothing when keys overlap.
mergeFromClauses :: ParsedFromClause -> ParsedFromClause -> Maybe ParsedFromClause
mergeFromClauses a b = if M.null $ M.intersection a b then Just $ M.union a b else Nothing


parseJoin :: Parser (ParsedFromClause, ParsedWhereClause)
parseJoin = do
  xs <- sepBy1 parseJoin1 spaces
  return (M.fromList $ map fst xs, foldl1 And $ map snd xs)

-- JOIN tableNameOrTable [AS tableAlias] ON conditions
parseJoin1 :: Parser ((TableAlias, Either ParsedQueryTree TableName), ParsedWhereClause)
parseJoin1 = do
  _ <- stringI "JOIN";
  spaces;
  (tAlias, t) <- parseFromClause1;
  spaces;
  _<- stringI "ON";
  spaces;
  onClause <- parseWhereClause;
  return ((tAlias, t), onClause)


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

    clauses :: [PosClause (CompOrder a SomeScalar)]
    clauses = S.elems cs where (PosClauses cs) = cnf

    equivalences :: [(a,a)]
    equivalences = spanEquations equivs -- equivs ++ map swap equivs

      -- decides if this clause should be extended to other relations
    maybeRel :: PosClause (CompOrder a SomeScalar) -> Maybe a
    maybeRel clause -- when all left sides are the same, no column name on right side.
      | (PosC literals) <- clause,
        xs <- S.elems literals,
        leftSides <- map (fst . getCompSides) xs,
        allTheSame leftSides
        = listToMaybe leftSides
      | otherwise = Nothing

        -- maps to clauses that only have key on left side (and no column on right)
    homogenClausesMap :: M.Map a [PosClause (CompOrder a SomeScalar)]
    homogenClausesMap = foldl rf M.empty clauses where
      -- rf :: M.Map a (PosClause (CompOrder a SomeScalar))
      rf m clause = case maybeRel clause of
        Nothing -> m
        (Just colName) -> M.alter alter colName m where
          -- alter :: Maybe v -> Maybe v
          alter Nothing = Just [clause]
          alter (Just xs) = Just (clause : xs)

    reClause :: a -> PosClause (CompOrder a SomeScalar) -> PosClause (CompOrder a SomeScalar)
    reClause newKey (PosC clause) = PosC $ S.map (mapComp (const newKey) id) clause

    newCnf :: PosCNF (CompOrder a SomeScalar)
    newCnf = foldl (flip cnfAddClause) cnf kk where
      kk = [reClause k2 clause
           | (k1, k2) <- equivalences,
             clause <- Data.Foldable.concat $ M.lookup k1 homogenClausesMap]

    allTheSame :: [a] -> Bool
    allTheSame [] = True
    allTheSame [_] = True
    allTheSame (x:xs) = all (== x) xs


handleLine :: String -> IO ()
handleLine line =
  case runParser parseQuery () "" line of
    (Left pe) -> putStrLn $ ":error"  ++ show pe
    (Right b) -> case processTree b of
                   (Left err) -> putStrLn $ pr err
                   (Right tree) -> putStrLn $ pr tree

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering;
  c <- getContents;
  forM_ (lines c) handleLine

-- == types required: integer, double, string, date
-- TODO: Date support.
-- TODO: JOIN ON support.
-- TODO: See http://dev.mysql.com/doc/refman/5.7/en/expressions.html
