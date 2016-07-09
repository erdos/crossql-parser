# Ideas

## GROUP BY

GROUP BY is needed for databases like Facebook's Insights where a column value can be a nested structure. The solution is creating a new column for every nesting level. However, this way grouping becomes a necessity.

**Functions**

The following aggreate functions should be accepted:
- First: `avg`, `count` and `count(*)`, `sum`
- All: AVG MIN CHECKSUM_AGG SUM COUNT STDEV COUNT_BIG STDEVP GROUPING VAR GROUPING_ID VARP MAX

Originally, aggr functions could be nested, we may not need it. Also, we may only support aggr functions inside group by clauses.

**Empty group by (optional)**

Empty group  by clauses can be used when we
wish to aggregate every row to one group.

**HAVING (optional)**

Having is like Where with aggr functions. Thus having could be transported to a nesting selection's where clause. In this case, `SELECT` clause is lifted and `FROM` clause contains the original grouping.

**Examples**

`SELECT sum(likes) FROM t WHERE date between 'now' and 'then' GROUP BY city`

`SELECT `

`SELECT sum`

**Sources**
- https://blog.jooq.org/2014/12/04/do-you-really-understand-sqls-group-by-and-having-clauses/
