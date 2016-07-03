## Select DSL Parser

_An SQL query rewrite engine_


### Requirements

| name | package | version | description |
| ---- | ------- | ------- | ----------- |
| GHC  | `ghc` | `7.8.5` | Glasgow Haskell Compiler |
| Parsec | `ghc-parsec-devel`, <br/> `ghc-parsec` | `3.1.5-2` | parsec library |
| boot | - | `2.6.0` | Build tool for Clojure - needed to run the test suite. <br/> See: _boot-clj.com_ |

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

More examples and expected results can be found in the `test.clj` file. You may need to install `boot` to run the test suite.

### <a href="Input.md">Input format</a>

### <a href="Output.md">Output format</a>

### License
