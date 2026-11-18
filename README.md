# Approximation Preserving Coresets

The **Euclidean and finite-metric coreset guarantees**, including randomized
lifting, are formalized in Lean.

[Paper](https://arxiv.org/abs/2606.17316) by Milind Prabhu, Chris Schwiegelshohn,
and Sudarshan Shyam.

## Explore the proof

Open the [interactive proof graph](https://milind-prabhu.github.io/approximation-preserving-coresets/).
Click a theorem or lemma to see its Lean statement, proof, and dependencies.

[![Lean proof dependency graph](blueprint/generated/APC_Dependency_Graph.svg)](https://milind-prabhu.github.io/approximation-preserving-coresets/)

## Build and verify

Install [elan](https://github.com/leanprover/elan), clone this repository, and run:

```bash
bash bootstrap.sh
bash check.sh
```

Lean **4.24.0** and mathlib are pinned. The check builds the proofs and runs
the axiom audit. [Build status](https://github.com/milind-prabhu/approximation-preserving-coresets/actions/workflows/lean.yml).

See the [formalization notes](FORMALIZATION.md) for theorem statements, assumptions,
and scope.

This formalization was achieved using **ChatGPT-6 Astra**.
