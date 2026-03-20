<!--
Suggested GitHub Topics: lean4 functional-programming theorem-proving dependent-types formal-verification proof-assistant
-->

# Lean4 — Functional Programming & Formal Reasoning

A collection of Lean4 implementations and formal proofs spanning functional programming patterns, monad theory, and data structure verification.

## What is Lean4?

Lean4 is a proof assistant and functional programming language developed at Microsoft Research. It uses dependent types to bridge the gap between programming and mathematics — the same language is used to write programs, specify their properties, and prove those properties correct. Lean4 is both a fully featured functional language and an interactive theorem prover.

## What's in this repo

The `src/` directory contains extracted highlights from coursework, organised by concept:

| File | Concept | Description |
|------|---------|-------------|
| `monad-transformers.lean` | Monad Transformers | Custom implementations of InterpState, InterpThrow, and InterpWriter monad transformer stacks with lift operations |
| `red-black-tree-proofs.lean` | Formal Verification | BST invariant proofs for red-black trees: change_bounds, rebuild_respects_BST, make_black, and to_root lemmas |
| `parser-combinators.lean` | Parser Combinators | Monadic parser combinator library built from scratch: Parser monad instance, many/choice/constrain combinators, and parsers for natural numbers and arithmetic expressions |

## Highlights

**Monad Transformer Stack (hw05)**: Implemented three monad transformers from scratch — `InterpState` (stateful computation), `InterpThrow` (typed error propagation), and `InterpWriter` (output accumulation) — and composed them into a single `Interp` monad. The non-trivial part was correctly sequencing effects when all three are stacked, especially implementing `recover` (try-catch) across the full stack.

**Red-Black Tree BST Proofs (hw08)**: Proved that tree restructuring operations (rebalancing, rebuilding from ancestry path, converting to root) all preserve the BST ordering invariant. The `change_bounds` lemma required structural induction over three constructors (leaf, red\_node, black\_node) with careful propagation of the bounds weakening through both subtrees.

**Parser Combinators (hw04)**: Built a full monadic parser combinator library from scratch, implementing `Functor`, `Applicative`, and `Monad` instances for `Parser σ α`. Combinators include `many` (greedy Kleene star), `choice` (non-deterministic alternation), and `constrain` (filtered parsing). Used the library to build parsers for natural numbers and left-associative arithmetic expressions with whitespace handling.

## Raw Assignments

The original homework submissions (complete Lean4 Lake projects) are preserved in [`/raw_assignments`](raw_assignments/README.md). Each is a standalone project buildable with `lake build`.
