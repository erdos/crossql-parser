# Output format

The response of the program is printed to the standard output as a nested one-line EDN map.

A query map can be one of the following two formats.

## 1. simple query

A simple query describes a selection from a single data source.

```
{:select {column-alias column-name}
 :from table-name
 :where cnf-of-left-aligned-relations}
```

## 2. complex query

This type of query can be used to join computed selections.

```
{:select {column-alias column-name}
 :from {table-alias query}
 :where cnf-of-mixed-relations}
```


## Identifiers

The values in `table-alias`, `table-name`, `column-alias`, `column-name` are simple symbol objects. A qualified identifier has a non-empty namespace field denoting the alias of the subquery that contains the column referenced by the identifier.


## Scalar values

The following scalar values are supported: signed/unsigned double/long and string literals.


## Mathematical expressions

Mathematical expressions are binary trees with the following nodes:

- Addition and subtraction: `(+ left right)` and `(- left right)`
- Multiplication and division: `(* left right)` and `(/ left right)`
- Leaf nodes are simple values (scalar or identifier).


## Relations

1. Left-aligned relations have an identifier on the left side and a scalar value (number or string) on the right.

2. Mixed relations have mathematical expressions on both sides.

**Syntax:** `(op left-side right-side)` where `op` is one of `<, >, <=, >=, <>, !=, ==`.


## CNF forms

The parser transforms all math formulas to positive CNF format. This is a _Conjuctive Normal Form_ with only positive literals. Every literal is a relation.

An EDN representation of a CNF is in the form:
`(cnf [lit-1-1 lit-1-2 ... lit-1-n] [lit-2-1 lit-2-2 ... lit-2-k] ...)`.

The top level represents a conjunction and the vectors represent the disjunction of literals.
