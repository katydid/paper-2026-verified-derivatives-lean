# Verified Derivatives for Fast Filtering and Schema Validation of Semi-Structured Data 

Proofs written in [Lean4](https://leanprover.github.io/) of the core [katydid](http://katydid.org.za/) filtering algorithm for the paper: Verified Derivatives for Fast Filtering and Schema Validation of Semi-Structured Data.

![Check Proofs](https://github.com/katydid/paper-2026-verified-filter/workflows/Check%20Proofs/badge.svg)

## Goal

The goal is to formalize the core [katydid](http://katydid.org.za/) filtering algorithm.
This algorithm allows us to filtering through millions of serialized data structures per second on a single core.

## Outline

* [Grammar](./VerifiedFilter/Grammar): Regular Hedge Grammar's definitions and proofs.
* [Regex](./VerifiedFilter/Regex): Regular expression's definitions and proofs.
* [Related](./VerifiedFilter/Related): Experiments with Related work.
* [Std](./VerifiedFilter/Std): Definitions and proofs that we might expect to be in a standard library.
* [Pred](./VerifiedFilter/Pred): Example predicate types that are used by both `Grammar` and `Regex`.

## Setup

  - [Install Lean4](https://lean-lang.org/install/).
  - Remember to also add `lake` (the build system for lean) to your `PATH`.  You can do this on mac by adding `export PATH=~/.elan/bin/:${PATH}` to your  `~/.zshrc` file
