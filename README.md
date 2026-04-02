# Workshop: Introduction to Lean

Materials for the Lean workshop delivered at [CS Exebit 2026](https://www.csexebit.page/), IIT Madras, by [Pranav Ramesh](https://github.com/pranavramesh2003).

[Lean](https://lean-lang.org/) is both a functional programming language and an interactive theorem prover. This workshop introduces Lean through hands-on exercises covering types, programs, proofs, and formal verification.

## Contents

### `LoVe/` — Logic and Verification Exercises
Adapted from the [LoVe course](https://github.com/blanchette/logical_verification_2023), covering:
- **Types and Terms** — Lean's type system and term-level programming
- **Programs and Theorems** — writing programs and stating properties
- **Backward Proofs** — tactic-based proof construction
- **Functional Programming** — inductive types, pattern matching, recursion

Each topic has a Demo file, an Exercise Sheet, and a Homework Sheet.

### `LeanLangur/` — Language Theory in Lean
Small case studies formalising programming language concepts:
- `LangurLang.lean` — a simple language definition
- `LangurLeaps.lean` — operational semantics
- `TacTicToe.lean` — a fun tactic puzzle

## Getting Started

The repo includes a dev container for a zero-setup environment.

1. Open in [GitHub Codespaces](https://codespaces.new/pranavramesh2003/CS_Exebit_Lean_Workshop) or VS Code with the Dev Containers extension
2. Wait for the container to build — Lean and Mathlib will be installed automatically
3. Open any `.lean` file and start exploring

## Prerequisites

No prior Lean experience needed. Familiarity with functional programming (Haskell, OCaml, or similar) is helpful but not required.

## License

MIT
