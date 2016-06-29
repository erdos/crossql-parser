## Select DSL Parser
__A minimalist SQL Select query parser__

**Requirements**
- GHC: `Glasgow Haskell Compiler, Version 7.8.4`
- Parsec module

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
