/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The ℓ²-triangle (Minkowski) inequality in `Real.sqrt` form

`Real.sqrt_sum_sq_le_sqrt_sum_sub_sq_add`: for real families `u v : ι → ℝ` on a finite index set
`W`,
`√(∑ᵢ uᵢ²) ≤ √(∑ᵢ (uᵢ − vᵢ)²) + √(∑ᵢ vᵢ²)`.

This is the reverse-triangle form of the finite-dimensional `ℓ²` triangle inequality
`‖u‖₂ ≤ ‖u − v‖₂ + ‖v‖₂`. It is the `p = 2`, `Real.sqrt`-shaped corollary of Mathlib's finite-sum
Minkowski inequality `Real.Lp_add_le` (applied to `u − v` and `v`, whose sum is `u`), packaged in
the `∑ ·²`/`Real.sqrt` vocabulary that arises when the entries are norms. It saves callers from
re-deriving Minkowski from Cauchy–Schwarz by hand.
-/

@[expose] public section

/-- **The ℓ²-triangle (Minkowski) inequality, `Real.sqrt` form.** For real families `u v : ι → ℝ`
on a finite index set `W`,
`√(∑ᵢ uᵢ²) ≤ √(∑ᵢ (uᵢ − vᵢ)²) + √(∑ᵢ vᵢ²)`.
A `Real.sqrt`-shaped restatement of `Real.Lp_add_le` at `p = 2` with the summands `u − v` and `v`
(whose sum is `u`): rewriting each `√` as a `(·) ^ (1/2)` rpow reduces the goal to that lemma. -/
theorem Real.sqrt_sum_sq_le_sqrt_sum_sub_sq_add {ι : Type*} (W : Finset ι) (u v : ι → ℝ) :
    Real.sqrt (∑ i ∈ W, u i ^ 2)
      ≤ Real.sqrt (∑ i ∈ W, (u i - v i) ^ 2) + Real.sqrt (∑ i ∈ W, v i ^ 2) := by
  have h := Real.Lp_add_le W (fun i => u i - v i) v (by norm_num : (1 : ℝ) ≤ 2)
  simp only [sub_add_cancel] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa using h

end
