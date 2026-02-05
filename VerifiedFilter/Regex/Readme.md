# Regex

In this folder we define a regular expression types, derivatives, validation and filtering algorithms.

We define semantics for the regular expression language in [Lang](./Lang.lean).

The create several implementations of regular expression algorithms:
* A regular expression over [Char](./Char.lean) and the equivalence proof to symbolic regular expressions.
* Symbolic regular expressions [Regex](./Regex.lean) with the usual derive, validate and filter functions and proofs of their correctness, based on the denotation that is also found here.
* The optimized [Katydid](./Katydid.lean) algorithm (without memoization) with derive, validate and filter functions and proofs of their correctness.
* In the [Memoize](./Memoize/Readme.md) subfolder we define the optimized Katydid algorithm with memoization.
* In the [IfExpr](./IfExpr/Readme.md) subfolder we define an alternative implementation without any heap allocations, but with exponential memoization space blowup.

The Katydid algorithm is built on top of some foundational functions and theorems:
* [Map](./Map.lean) defines the regular expression as a functor that can be mapped over.
* [Point](./Point.lean) defines an alternative derive function and shows how it is equivalent to the normal derive.
* [Extract](./Extract.lean) shows how can extract symbols from regular expressions.
* [Replace](./Replace.lean) shows how we can replace symbols back into regular expressions.
* [ExtractReplace](./ExtractReplace.lean) shows how we can use extract and replace to apply a function and that it is equivalent to mapping over a regular expression as a functor.
* [RegexID](./RegexID.lean) is an abbrevation for `Regex (Fin n)` used for a regular expression containing symbol indexes.
* [Num](./Num.lean) defines a function that returns the number of symbols.
