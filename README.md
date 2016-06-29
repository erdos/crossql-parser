## Select DSL Parser
__A minimalist SQL Select query parser__

### Requirements

| name | package | version | description |
| ---- | ------- | ------- | ----------- |
| GHC | `ghc` | `7.8.5` | Glasgow Haskell Compiler                 |
| Parsec | `ghc-parsec-devel`, `ghc-parsec` | `` | parsec library  |

### try it
0. clone: `git clone https://github.com/erdos/selectdsl`
1. build: `ghc SelectDSLParser.hs`
2. eval: `./SelectDSLParser`
3. communicates on standard input/output line-by-line.

### example

```Clojure
<= SELECT t.a FROM t WHERE t.x<12 and t.y>=3
=> {:select {t.a a} :from t :where (and (or (> x 12)) (or (>= y 3)))}
```
