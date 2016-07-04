# Collection of Use Cases

This is a collection of valid SQL queries to be considered for later implementation.

## Required Features

- expressions in select list (projection)
- order by clause
- `NATURAL JOIN`: we do not specify join column name.
-

## Sources

- wiki: https://en.wikipedia.org/wiki/SQL
- SQL2 bnf: http://www.contrib.andrew.cmu.edu/~shadow/sql/sql2bnf.aug92.txt


## Examples

source: wiki

1. select all + order by.
`SELECT * FROM  Book WHERE price > 100.00 ORDER BY title`

2. join on + group by + count(*)

``` sql
SELECT Book.title AS Title,
       count(*) AS Authors
 FROM  Book
 JOIN  Book_author
   ON  Book.isbn = Book_author.isbn
 GROUP BY Book.title;
```

3. natural join (without on) + group by + count(*)

``` sql
SELECT title,
       count(*) AS Authors
 FROM  Book
 NATURAL JOIN Book_author
 GROUP BY title;
```

4. subexpression + order by

``` sql
SELECT isbn,
       title,
       price,
       price * 0.06 AS sales_tax
 FROM  Book
 WHERE price > 100.00
 ORDER BY title
```
