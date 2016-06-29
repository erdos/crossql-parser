## Select DSL Parser
__A minimalist SQL Select query parser__

**Requirements**

| name | package | version | description |
-------------------
| GHC | `ghc` | `7.8.5` | Glasgow Haskell Compiler                 |
| Parsec | `ghc-parsec-devel`, `ghc-parsec` | `` | parsec library  |

**Execute**
1. build: `ghc SelectDSLParser.hs`
2. eval: `./SelectDSLParser`
3. communicates on standard input/output line-by-line.

### Output

*QUERY*
```Clojure
{:select {symbol symbol}
 :from   {symbol QUERY}
 :where  CNF
 }
```

*CNF*
`(and (or LIT LIT ...) (or LIT LIT ...) ...)`

*LIT*
`(OP VAL VAL)`
