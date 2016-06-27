{-# OPTIONS_GHC -Wall -Werror #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}

module SelectDSLParser (
   MathExpr(..),  ResultQueryTree(..), ParsedQueryTree(..),
    negateComp, Column(..), ColumnQualified(..), main, to_cnf,toPosCnf,flipComp, CompOrder(..),
    maybeLeftAlign, parseQuery,
    processTree, collectReads, parseLogicTree,
    tryParser, maybeEquation,visitComp, compToCompOrder, getCompSides,maybeEvalMath
    ) where

import qualified Data.Set as S(Set, union, empty, insert, elems, fromList,map)
import qualified Data.Map.Strict as M(Map, fromList)

import Control.Monad

import Data.Either()
import Data.List()

import Text.Parsec as TP( chainl1, (<|>), string,runParser, ParseError,  spaces)
import Text.Parsec.Combinator (option)
import Text.Parsec.Language
import Text.Parsec.String as TPS
import Text.Parsec.Token as TPT

-- import Prelude (Eq)
--import Text.Parsec.Token (float, parens)
--import Text.Parsec.String
--import Text.Parsec.Expr
--import Text.Parsec.Char as TPC(string, letter,char)


data Column = ColName deriving (Eq, Show, Ord)

data MathExpr a = D Double | I Integer | Read a
                | Add (MathExpr a) (MathExpr a)
                | Sub (MathExpr a) (MathExpr a)
                | Mul (MathExpr a) (MathExpr a)
                | Div (MathExpr a) (MathExpr a)
                | Pow (MathExpr a) (MathExpr a)
                | Log (MathExpr a)
	        deriving (Eq, Show, Ord)

-- toSamePrecision :: Either Integer Double -> Either Integer Double -> Either Integer Double


maybeEvalMath :: MathExpr t -> Maybe (Either Integer Double)
maybeEvalMath (D d) = Just $ Right d
maybeEvalMath (I i) = Just $ Left i
maybeEvalMath (Read _) = Nothing
maybeEvalMath (Add a b) = liftM2 op (maybeEvalMath a) (maybeEvalMath b)
  where
    op :: Either Integer Double -> Either Integer Double -> Either Integer Double
    op (Left i) (Left j) = Left $ i + j
    op (Left i) (Right d) = Right $ fromIntegral i + d
    op (Right d) (Left i) = Right $ d + fromIntegral i
    op (Right d) (Right dr) = Right $ d + dr
maybeEvalMath (Sub a b) = liftM2 op (maybeEvalMath a) (maybeEvalMath b)
  where
    op :: Either Integer Double -> Either Integer Double -> Either Integer Double
    op (Left i) (Left j) = Left $ i - j
    op (Left i) (Right d) = Right $ fromIntegral i - d
    op (Right d) (Left i) = Right $ d - fromIntegral i
    op (Right d) (Right dr) = Right $ d - dr
maybeEvalMath (Mul a b) = liftM2 op (maybeEvalMath a) (maybeEvalMath b)
  where
    op :: Either Integer Double -> Either Integer Double -> Either Integer Double
    op (Left i) (Left j) = Left $ i * j
    op (Left i) (Right d) = Right $ fromIntegral i * d
    op (Right d) (Left i) = Right $ d * fromIntegral i
    op (Right d) (Right dr) = Right $ d * dr
maybeEvalMath (Div a b) = liftM2 op (maybeEvalMath a) (maybeEvalMath b)
  where
    op :: Either Integer Double -> Either Integer Double -> Either Integer Double
    op (Left i) (Left j) = Right $ fromIntegral i / fromIntegral j
    op (Left i) (Right d) = Right $ fromIntegral i / d
    op (Right d) (Left i) = Right $ d / fromIntegral i
    op (Right d) (Right dr) = Right $ d / dr
maybeEvalMath (Pow a b) = liftM2 op (maybeEvalMath a) (maybeEvalMath b)
  where
    op :: Either Integer Double -> Either Integer Double -> Either Integer Double
    op (Left i) (Left j) = Left $ i ^ j
    op (Left i) (Right d) = Right $ fromIntegral i ** d
    op (Right d) (Left i) = Right $ d ** fromIntegral i
    op (Right d) (Right dr) = Right $ d ** dr
maybeEvalMath (Log a) = liftM op (maybeEvalMath a)
  where
    op :: Either Integer Double -> Either Integer Double
    op (Left i) = Right $ log $ fromIntegral i
    op (Right d) = Right $ log d

collectReads :: MathExpr a -> [a]
collectReads (Read a) = [a]
collectReads (Add a b) = collectReads a ++ collectReads b
collectReads (Sub a b) = collectReads a ++ collectReads b
collectReads (Mul a b) = collectReads a ++ collectReads b
collectReads (Div a b) = collectReads a ++ collectReads b
collectReads (Pow a b) = collectReads a ++ collectReads b
collectReads (Log a) = collectReads a
collectReads _ = []


-- eval locally
data Comp a = CST a a
            | CLT a a
            | CSEQ a a
            | CLEQ a a
            | CEQ  a a
            | CNEQ a a
	    deriving (Eq, Show, Ord)

getCompSides :: Comp a -> (a,a)
getCompSides (CEQ p q) = (p,q)
getCompSides (CNEQ p q) = (p,q)
getCompSides (CST p q) = (p,q)
getCompSides (CLT p q) = (p,q)
getCompSides (CLEQ p q) = (p,q)
getCompSides (CSEQ p q) = (p,q)

visitComp :: ((a -> a -> Comp a) -> a -> a -> b) -> Comp a -> b
visitComp f (CST x y) = f CST x y
visitComp f (CLT x y) = f CLT x y
visitComp f (CSEQ x y) = f CSEQ x y
visitComp f (CLEQ x y) = f CLEQ x y
visitComp f (CEQ x y) = f CEQ x y
visitComp f (CNEQ x y) = f CNEQ x y


parseComp :: Parser a -> Parser (Comp a)
parseComp f = do {a <- f; spaces; c <- op; spaces; b <- f; return (c a b)}
  where
    op :: Parser (a -> a -> Comp a)
    x p q = string p >> return q
    op =  x "<=" CSEQ
      <|> x ">=" CLEQ
      <|> x "==" CEQ
      <|> x "!=" CNEQ
      <|> x "<" CST
      <|> x ">" CLT

-- eval in cloud
data CompOrder a b = CO_ST a b
                   | CO_LT a b
                   | CO_EQ a b
                   | CO_LEQ a b
                   | CO_SEQ a b
                   | CO_NEQ a b
                   deriving (Eq, Show, Ord)


negateComp :: Comp t -> Comp t
negateComp x = case x of
  (CST a b) -> CLEQ a b
  (CLT a b) -> CSEQ a b
  (CEQ a b) -> CNEQ a b
  (CNEQ a b) -> CEQ a b
  (CSEQ a b) -> CLT a b
  (CLEQ a b) -> CST a b

flipComp :: Comp t -> Comp t
flipComp x = case x of
  (CST a b) -> CLT b a
  (CLT a b) -> CST b a
  (CEQ a b) -> CEQ b a
  (CNEQ a b) -> CNEQ b a
  (CSEQ a b) -> CLEQ b a
  (CLEQ a b) -> CSEQ b a


type ColumnName = String

type ColumnAlias = String
data ColumnQualified = CQ TableAlias ColumnName deriving (Show, Eq)

type TableName = String
type TableAlias = String

type ColumnEitherQualified = Either ColumnQualified ColumnName

type ColumnMap         = M.Map ColumnAlias ColumnQualified
type ParsedFromClause  = (M.Map TableAlias (Either ParsedQueryTree TableName))
type ParsedWhereClause = (LogicTree (Comp (MathExpr ColumnEitherQualified)))

-- get it from parser
data ParsedQueryTree = PQT ColumnMap ParsedFromClause ParsedWhereClause deriving (Eq, Show)

-- this is the output. also holds info on evaluation order
data ResultQueryTree = NestedRQT
                         (M.Map ColumnAlias ColumnQualified)
                         (M.Map TableAlias (Either ResultQueryTree TableName))
                         (PosCNF (Comp (MathExpr ColumnQualified)))
                     |  SimpleRQT
                        [ColumnName]
                        TableName
                        (PosCNF (CompOrder ColumnName Double))
                     deriving (Eq, Show)


parseFromClause :: Parser ParsedFromClause
parseFromClause =
  do { xs <- commaSep1 haskell ps;
       return $ M.fromList xs}
  where
    ps :: Parser (TableAlias, Either ParsedQueryTree TableName)
    ps = ps2 <|> ps1 <|> ps3
    ps1 = do {x <- parseTableName;
              return (x, Right x)}
    ps2 = do {x <- parseTableName;
              _ <- string "AS";
              y <- parseTableAlias;
              return (x, Right y)}
    ps3 = do {t <- parseQuery;
              _ <- string "AS";
              a <- parseTableAlias;
              return (a, Left t)}

parseColumnAlias :: Parser ColumnAlias
parseColumnAlias = identifier haskell

parseColumnName :: Parser ColumnName
parseColumnName = identifier haskell

parseTableAlias :: Parser TableAlias
parseTableAlias = identifier haskell

parseTableName :: Parser TableName
parseTableName = identifier haskell

  -- x <- TPT.reserved "SELECT";

--parseColumnName :: Parser ColumnName
--parseColumnName = TP.many1 TPC.letter

--parseColumnAlias :: Parser ColumnAlias
--parseColumnAlias = TP.many1 TPC.letter

--parseTableAlias :: Parser TableAlias
--parseTableAlias = TP.many1 TPC.letter

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
parseSelectClause =
  do { xs <- commaSep1 haskell part;
       return $ M.fromList xs}
  where

    part :: Parser (ColumnAlias, ColumnQualified)
    part = part2 <|> part1

    -- no alias is given: alis will be full qualified name with dot.
    part1 = do {qualified@(CQ table column) <- parseColumnQualified;
                return (table ++ "." ++ column, qualified)}

    -- alias is given.
    part2 = do {pq <- parseColumnQualified;
                spaces;
                _ <- string "AS";
                spaces;
                ali <- parseColumnAlias;
                return (ali, pq)
              }


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
	deriving (Eq, Show, Ord)

parseLogicTree :: Parser a -> Parser (LogicTree a)
parseLogicTree pa = _start
  where
    ss s p = do{spaces; _<-string s; spaces; return p}
    _start = _or
    _or  = chainl1 _and (ss "or" Or)
    _and = chainl1 _ll   (ss "and" And)
    _not = do {spaces; _<-string "not"; x<-_ll; return $ Not x}
    _pp  = do {spaces; x <- pa; return $ Leaf x}
    _ll  = parens haskell _start <|> _not <|> _pp

parseWhereClause :: Parser ParsedWhereClause
parseWhereClause = parseLogicTree $ parseComp $ parseMathExpr parseColumnEitherQualified


parseQuery :: Parser ParsedQueryTree
parseQuery =
  do
    _<-string "SELECT";
    selectClause <- parseSelectClause
    _<-string "FROM";
    fromClause <- parseFromClause
    _<-string "WHERE";
    whereClause <- parseWhereClause
    return (PQT selectClause fromClause whereClause)

--data LogicTree_Disjunction a = AndD (LogicTree_Disjunction a) | NotD a | LeafD a
--	deriving (Eq)

-- a Clause is a disjunction of positive and negatives items.
data Clause a = PosNeg (S.Set a) (S.Set a)
	deriving (Eq, Show, Read, Ord)
data CNF a = Clauses (S.Set (Clause a))
	deriving (Eq, Show,Read, Ord)


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


toPosCnf :: (Ord a) => CNF (Comp a) -> PosCNF (Comp a)
toPosCnf (Clauses cs) = PosClauses (S.map f cs)
  where f (PosNeg gg hh) = PosC (S.union gg (S.map negateComp hh))


compToCompOrder :: Comp a -> b -> c -> CompOrder b c
compToCompOrder (CST _ _) = CO_ST
compToCompOrder (CLT _ _) = CO_LT
compToCompOrder (CEQ _ _) = CO_EQ
compToCompOrder (CNEQ _ _) = CO_NEQ
compToCompOrder (CSEQ _ _) = CO_SEQ
compToCompOrder (CLEQ _ _) = CO_LEQ

-- visitComp :: ((a -> a -> Comp a) -> a -> a -> b) -> Comp a -> b

  -- try to produce left aligned conditions.
-- TODO: simplify expressions by evaling
maybeLeftAlign :: Comp (MathExpr Column) -> Maybe (CompOrder Column (Either Integer Double))
maybeLeftAlign t = f a b --x = undefined -- visitComp f x
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

maybeEquation :: Comp (MathExpr t) -> Maybe (t,t)
maybeEquation (CEQ (Read a) (Read b)) = Just (a,b)
maybeEquation _ = Nothing

tryParser :: String -> Parser a -> Either ParseError a
tryParser s p = runParser p () "" s


main :: IO ()
main = undefined

-- parse and move names, aliases, expressions to right layer.
processTree :: ParsedQueryTree -> ResultQueryTree
processTree =undefined --(PQT columnMap fromClause whereClause)=undefined
  -- TODO:
  -- - see if all column names could be resolved in conditions
  -- - in conditions: if col name is not resolved -> die
  -- - left align conditions, create sub op with em.
  -- - split where to diff clauses based on column name qualifs involved.create subtrees on cond.
  -- step by step;
  -- 1. cnf where. throw err on unresolved itms.
  -- 2. left align cnf, subexpressions (eq partitions in em).
