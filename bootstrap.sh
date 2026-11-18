#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake exe cache get \
  Mathlib.Analysis.Complex.Exponential \
  Mathlib.Data.Nat.Choose.Bounds \
  Mathlib.Data.Finset.Image \
  Mathlib.Data.Fintype.Card \
  Mathlib.Analysis.SpecialFunctions.Pow.Real \
  Mathlib.Algebra.BigOperators.Field \
  Mathlib.Analysis.InnerProductSpace.Basic \
  Mathlib.Tactic.Abel \
  Mathlib.Tactic.Linarith \
  Mathlib.Tactic.Ring \
  Mathlib.Algebra.Order.BigOperators.Group.Finset \
  Mathlib.Data.Nat.Log \
  Mathlib.Data.Real.Archimedean \
  Mathlib.Algebra.BigOperators.Ring.Finset \
  Mathlib.Analysis.SpecialFunctions.Log.Basic \
  Mathlib.Tactic.Positivity \
  Mathlib.Data.Finset.Powerset \
  Mathlib.Data.Fintype.EquivFin \
  Mathlib.Data.Real.Basic \
  Mathlib.Tactic.FieldSimp
