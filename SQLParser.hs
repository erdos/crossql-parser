{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall -Werror #-}

module SQLParser (QuerySpec(SFW, SFWG, SFWGH), ColumnName, ColumnAlias, ColumnMath, TableName, TableAlias, SQLParser.parse, runParser, SQLParser.parseLogicTree, SelectClause, WhereClause, FromClause, SubQuery) where

import CNF
import MathExpr
import Comp
import Util

import Text.Parsec as TP ((<|>), string, spaces, sepBy1, try, runParser, chainl1)
import Text.Parsec.Combinator (between, optionMaybe)
-- import Text.Parsec.Error (Message(..), errorMessages)
import Text.Parsec.Language (haskell)
import Text.Parsec.String as TPS
import Text.Parsec.Token as TPT (commaSep1, parens)

-- import Control.Monad
--import Data.Char(toUpper)

import Control.Applicative ((<$>))
import Data.Maybe ()


type TableName = String
type TableAlias = String

type ColumnName = String
type ColumnAlias = String
type ColumnMath = MathExpr ColumnAlias -- sum(1), etc.

parseColumnAlias :: Parser ColumnAlias
parseColumnAlias = parseIdentifier

parseColumnName :: Parser ColumnName
parseColumnName = parseIdentifier

parseTableAlias :: Parser TableAlias
parseTableAlias = parseIdentifier

parseTableName :: Parser TableName
parseTableName = parseIdentifier



-- ha subquery -> zarojelben van.
type TableReference = (Either TableName SubQuery, Maybe TableAlias)

parseTableReference :: Parser TableReference
parseTableReference
  =
  do
    -- _<- spaces;
    _ <- string "("
    q <- parseSubQuery
    _ <- string ")"
    t <- as
    return (Right q, t)
  <|>
  do
    t <- parseTableName
    a <- as
    return (Left t, a)
    where
      as = optionMaybe $ try $ do
        spaces;
        _ <- stringI "AS"
        spaces;
        parseTableAlias

-- zarojel subquery (with opt order by) zarojel
  -- sth with optional as

-- a szokozokkel meg meg fogok szenvedni.

type JoinCond = (LogicTree (Comp (MathExpr ColumnName)))

type JoinedTable = (TableReference,
                    [(TableReference,  Maybe JoinCond)])

--

flattenJoin :: [(TableReference, Maybe (TableReference, JoinCond))]
            -> Maybe JoinedTable
flattenJoin [] = Nothing
flattenJoin ((tr, a) : xs) = Just (tr, rest)
  where
    rest = reverse $ foldl fr (ini a) xs
    fr ys (gg, Nothing) = (gg, Nothing) : ys
    fr ys (gg, Just (p, q)) =  (p, Just q) : (gg, Nothing) : ys
    ini Nothing = []
    ini (Just (t, c)) = [(t, Just c)]

parseJoinedTable :: Parser JoinedTable
parseJoinedTable = do
  cs <- commasep1 parseOne
  let Just fj = flattenJoin cs
    in return fj
  where
    parseOne = try $ do
      kk <- parseTableReference
      spaces;
      tt <- optionMaybe $ try parseJoinTail
      case tt of
        (Just (tr, eff)) -> return (kk, Just (tr, eff))
        Nothing          -> return (kk, Nothing)
    parseJoinTail = do
      _ <- stringI "JOIN"
      spaces
      tr <- parseTableReference
      spaces
      _ <- stringI "ON"
      spaces
      eff <- CNF.parseLogicTree (Comp.parse1 (parseMathExpr parseColumnName))
      return (tr, eff)

-- TODO: ide johetnek a halmazmuveletek is!
type SubQuery = QuerySpec

parseSubQuery :: Parser SubQuery
parseSubQuery = between (string "(") (string ")") parseSubQuery <|> parseQuerySpec


-- ;; JOIN t r ON expr JOIN t r ON expr JOIN t r ON expr

  -- https://docs.oracle.com/cd/B14156_01/doc/B13812/html/sqcmd.htm#i1009110

type FromClause = JoinedTable

  -- TODO: write parsed parser for these types.

parseFromClause :: Parser FromClause
parseFromClause = parseJoinedTable


type WhereClause = LogicTree (CompOrder ColumnName (MathExpr ColumnName))

type GroupByClause = [ColumnAlias]

type HavingClause = LogicTree (CompOrder (AggregateFn ColumnAlias) SomeScalar)

data QuerySpec -- root
  = SFW SelectClause FromClause WhereClause
  | SFWG SelectClause FromClause WhereClause GroupByClause
  | SFWGH SelectClause FromClause WhereClause GroupByClause HavingClause
  deriving (Eq, Ord, Show)

parseWhereClause :: Parser WhereClause;
parseWhereClause = SQLParser.parseLogicTree parseColumnName (parseMathExpr parseColumnName)

type SelectClause = [(ColumnMath, Maybe ColumnAlias)]
--  TODO: add join here also.
-- vesszovel elvalasztva.

-- do add spaces too
commasep1 :: Parser t -> Parser [t]
commasep1 f = sepBy1 f $ do  _ <- string ","; spaces

parseSelectClause :: Parser SelectClause
parseSelectClause = commasep1 $ do
  cm <- parseMathExpr parseColumnAlias
  spaces;
  kk <- try $ optionMaybe $ do
    _<- stringI "AS";
    spaces;
    parseColumnAlias;
  return (cm, kk)

parseGroupBySuffix :: Parser [ColumnName]
parseGroupBySuffix = do
  _ <- stringI "GROUP";
  spaces;
  _ <- stringI "BY";
  spaces;
  commaSep1 haskell parseColumnName;

parseHavingSuffix :: Parser HavingClause
parseHavingSuffix = do
  _ <- stringI "HAVING";
  spaces;
  SQLParser.parseLogicTree (parseAggregateFn parseColumnAlias) parseSomeScalar

parseQuerySpec :: Parser QuerySpec
parseQuerySpec = do
  _ <- stringI "SELECT";
  spaces;
  sc <- parseSelectClause;
  spaces;
  _ <- stringI "FROM";
  spaces;
  fc <- parseFromClause;
  spaces;
  _ <- stringI "WHERE";
  wc <- parseWhereClause;
  spaces;
  gbc <- optionMaybe $ do
    a <- parseGroupBySuffix;
    spaces;
    b <- optionMaybe parseHavingSuffix;
    return (a, b);
  case gbc of
    Nothing -> return $ SFW sc fc wc
    Just (gb, Nothing) -> return $ SFWG sc fc wc gb
    Just (gb, Just hc) -> return $ SFWGH sc fc wc gb hc

parse :: Parser QuerySpec
parse = parseQuerySpec

-- most jo lenne letesztelni
-- + between, + in range, + date, + aliasing (?), + different kinds of joins


parseBetween :: Parser a -> Parser b -> Parser (LogicTree (CompOrder a b))
parseBetween p q = do
      colname <- p
      spaces;
      _ <- stringI "BETWEEN";
      spaces;
      x1 <- q;
      spaces;
      _ <- stringI "AND";
      spaces;
      x2 <- q;
      return $ And (Leaf (CLEQ colname x1)) (Leaf (CSEQ colname x2))

-- also handler BETWEEN ... AND ... clause.
parseLogicTree :: Parser a -> Parser b -> Parser (LogicTree (CompOrder a b))
-- parseLogicTree g h = CNF.parseLogicTree $ Comp.parse g h
parseLogicTree g h = _start
  where
    bw = parseBetween g h
    comp = Leaf <$> Comp.parse g h
    ss s p = do{spaces; _<-stringI s; spaces; return p}
    _start = _or
    _or  = chainl1 _and (ss "or" Or)
    _and = chainl1 _ll   (ss "and" And)
    _not = do {_<-stringI "not"; spaces; Not <$> _ll}
    _pp  = do {spaces; try bw <|> comp}
    _ll  = parens haskell _start <|> _not <|> _pp

-- parseLogicTree1 :: Parser a -> Parser (LogicTree (Comp a))
-- parseLogicTree1 g = SQLParser.parseLogicTree g g
