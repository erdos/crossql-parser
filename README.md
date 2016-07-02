## Select DSL Parser

_An SQL query rewrite engine_


### Requirements

| name | package | version | description |
| ---- | ------- | ------- | ----------- |
| GHC  | `ghc` | `7.8.5` | Glasgow Haskell Compiler |
| Parsec | `ghc-parsec-devel`, `ghc-parsec` | `3.1.5-2` | parsec library  |


### Usage

0. clone: `git clone https://github.com/erdos/selectdsl`
1. build: `ghc SelectDSLParser.hs`
2. eval: `./SelectDSLParser`
3. communicates on standard input/output line-by-line.


### Example

```Clojure
<= SELECT t.a FROM t WHERE t.x<12 and t.y>=3
=> {:select {t.a a} :from t :where (cnf [(< x 12)] [(>= y 3)])}
```

### Input query syntax

All query should fit a single line and comments are not supported.
The basic sql query syntax is the following:

*query*: `SELECT columns FROM tables WHERE conditions`

*columns*: comma separated list of column names or
           `column-name AS column-alias` expressions.
*tables*: a comma separated list of tables or `table AS table-alias`
          expressions.`. A table can be either a table name or a subquery
          (between parentheses).

*conditions* ::= Logic tree of column relations of literals.
                 Logic relations `and`, `or`, `not`, are supported.

*column predicates*: `<`, `<=`, `>`, `>=`, `<>` or `!=`, `BETWEEN _ AND _`

*literals*: strings between double quotes, signed/unsigned long/double numbers.

*column/table name*: A single identifier.

After rewriting, a column name is a simple identifier as a symbol. A qualified column name has both a table alias (as symbol namespace) and a column alias (symbol name) in `table-alias/column-alias` format. Column names without `/` are unqualified.


### Output format

The output is hierarchic maps in single line EDN format. One map can be simple or nested.

#### Map syntax:

```
{:select SELECT, :from FROM, :where WHERE}
```

On single maps:

- *SELECT*: Map of column alias to column name (both symbols).
- *FROM*: Table name to select from (symbol).
- *WHERE*: CNF of safe literals (positive, left-aligned relations between column literals and constants).

On nested maps:

- *SELECT*: Map of column alias to fully qualified column name (latter in `tableAlias/columnAlias` format).
- *FROM*: Map of subqueries. Keys are table aliases (symbol), values are subquery maps.
- *WHERE*: CNF of unsafe literals (nualigned relations of math expressions on column names).

#### CNF syntax:

The parser transforms all math formulas to positive CNF format. This is a _Conjuctive Normal Form_ with only positive literals. Every literal is a relation (see later).

An EDN representation of a CNF is in the form:
`(cnf [lit-1-1 lit-1-2 ... lit-1-n] [lit-2-1 lit-2-2 ... lit-2-k] ...)`.
The top level represents a conjunction and the vectors represent the disjunction of literals.



### License
