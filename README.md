# Verified Derivatives for Fast Filtering and Schema Validation of Semi-Structured Data 

Proofs written in [Lean4](https://leanprover.github.io/) for the core [katydid](https://katydid.github.io/) validation algorithm.

![Check Proofs](https://github.com/katydid/paper-2026-verified-derivatives/workflows/Check%20Proofs/badge.svg)

## Goal

The goal is to formalize the core [katydid](https://katydid.github.io/) validation algorithm.
This algorithm allows us to validate millions of serialized data structures per second on a single core.
You can play around with the validation language on its [playground](http://katydid.github.io/play/).

## Setup

  - Lean4 has exceptional [instructions for installing Lean4 in VS Code](https://lean-lang.org/install/).
  - Remember to also add `lake` (the build system for lean) to your `PATH`.  You can do this on mac by adding `export PATH=~/.elan/bin/:${PATH}` to your  `~/.zshrc` file
  - Use mathlib's cache to speed up building time by running: `$ lake exe cache get`
