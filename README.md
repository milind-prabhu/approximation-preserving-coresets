# Approximation Preserving Coresets

The following results are formalized in Lean:

- **Euclidean APC:** `(1+ε)` approximation preservation with an explicit inverse-cubic size bound, up to a logarithmic factor.
- **Randomized lifting:** an `α(1+ε)` approximation from an `α`-approximate summary solver.
- **Finite-metric APC:** a `(4+ε)` approximation using subset enumeration.

[Paper](https://arxiv.org/abs/2606.17316) by Milind Prabhu, Chris Schwiegelshohn,
and Sudarshan Shyam.

## Explore the proof

View the [interactive Lean proof dependency graph](https://milind-prabhu.github.io/approximation-preserving-coresets/).
Hover for a summary; click a theorem or lemma to see its Lean statement, proof,
and dependencies. Use the view menu to explore different parts of the proof.

[![Lean proof dependency graph](blueprint/generated/APC_Dependency_Graph.svg)](https://milind-prabhu.github.io/approximation-preserving-coresets/)

## Build and verify

Install [elan](https://github.com/leanprover/elan), clone this repository, and run:

```bash
bash bootstrap.sh
bash check.sh
```

The project pins Lean 4.24.0 and mathlib. The check builds the proofs and runs the
axiom audit. [Build status](https://github.com/milind-prabhu/approximation-preserving-coresets/actions/workflows/lean.yml).

See the [formalization notes](FORMALIZATION.md) for precise theorem statements,
assumptions, and correspondence with the paper.
