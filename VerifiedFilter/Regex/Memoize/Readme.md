# Regex Memoize

In this folder we define the memoized Katydid algorithm, applied to regular expressions.

* [Memoize](./Memoize.lean) uses [Enter](./Enter.lean) and [Leave](./Leave.lean) to build a memoize class for Katydid and defines derive, validate and filter.
* [StateMemoize](./StateMemoize.lean) proves that those [Memoize](./Memoize.lean) functions are correct, when instantiated with a state monad.
* [UncurriedDerive](./UncurriedDerive.lean) shows how a normal derivative function can be uncurried and memoized as was mentioned in the introduction of the paper.