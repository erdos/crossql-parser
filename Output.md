# Output format

The response of the program is printed to the standard output in EDN format.


## 1. simple query

```
{:select {column-alias column-name}
 :from table-name
 :where cnf-of-left-aligned-relations}
```

## 2. complex query

```
{:select {column-alias column-name}
  :from {table-alias sub-query}
  :where cnf-of-mixed-relations}
```

## Relations

1. Left-aligned relations have an identifier on the left side and a scalar expression (number or string) on the right.

2. Mixed relations have mathematical expressions on both sides.

**Syntax:** `(op left-side right-side)` where `op` is one of `<, >, <=, >=, <>, !=, ==`.

## CNF forms

The parser transforms all math formulas to positive CNF format. This is a _Conjuctive Normal Form_ with only positive literals. Every literal is a relation.

An EDN representation of a CNF is in the form:
`(cnf [lit-1-1 lit-1-2 ... lit-1-n] [lit-2-1 lit-2-2 ... lit-2-k] ...)`.

The top level represents a conjunction and the vectors represent the disjunction of literals.
