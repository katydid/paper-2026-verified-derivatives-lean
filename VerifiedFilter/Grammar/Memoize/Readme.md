# Memoize

This folder contains the optimized Katydid algorithm with memoization including proofs of correctness for derive, validate and filter.

* [Memoize](./Memoize.lean) contains the algorithm used by derive, validate and filter.
* [StateMemoize](./StateMemoize.lean) contains proofs of correctness via instantiating the memoize algorithm with the state monad, for derive, validate and filter.
* [StateMemoizeExamples](./StateMemoizeExamples.lean) provides examples of how to use StateMemoize to filter efficiently.