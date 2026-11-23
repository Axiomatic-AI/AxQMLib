/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoLevelLowerBound

/-!
# Nielsen & Chuang, Exercise 4.38

Prove there is a dxd unitary not decomposable into fewer than d-1 two-level unitaries.

This exercise is a statement about complex matrices in `Matrix.unitaryGroup`.

## The formalisation

`AxQM/Concrete/TwoLevelLowerBound.lean`:

* `AxQM.Concrete.exists_unitary_two_level_decomposition_length_ge` — **the exercise**: for
  every `d`, there is `U ∈ Matrix.unitaryGroup (Fin d) ℂ` such that any list `L` of two-level
  unitaries with `L.prod = U` has `d − 1 ≤ L.length`.
* `AxQM.Concrete.allOnesReflection` — the witness `U = 1 − (2/d) • J` (the Householder
  reflection through the hyperplane orthogonal to `(1,…,1)`), with
  `allOnesReflection_mem_unitaryGroup` and `allOnesReflection_apply_zero_ne_zero`.
* `AxQM.Concrete.edgeSpan` / `diffSpan` and
  `stdVec_sub_mem_edgeSpan_of_prod_apply_ne_zero`, `finrank_edgeSpan_le_length`,
  `finrank_diffSpan_le_one` — the connectivity/dimension-count machinery driving the lower bound.

The predicate `AxQM.Concrete.IsTwoLevelUnitary` is the one defined for Exercise 4.37 in
`AxQM/Concrete/QFTTwoLevel.lean`.
-/
