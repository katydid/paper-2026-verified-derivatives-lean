# IfExpr

When evaluating all the symbols by applying mapping the predicate over the Vector of symbols,
if care is not taken, this will trigger a heap allocation, which is costly in the context of this algorithm.
There are several ways to avoid this heap allocation. 
In Golang, one can pre-allocate a reusable buffer. 
In Lean, we define an alternative to the memoized enter function, IfExpr.enter, 
which returns a nested if expression over the symbols and all possible boolean Vector combinations.
The drawback of IfExpr.enter is an exponential blow-up in the space required for memoization.

In this folder we show how this alternative implementation could work in Lean.
We also prove correctness of this algorithm with respect to regular expressions.
The proofs for regular hedge grammars would not be very different, but this is not the ideal algorithm, so we do not include them.