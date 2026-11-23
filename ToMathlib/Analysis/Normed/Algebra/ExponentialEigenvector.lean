/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The exponential of an operator acts on an eigenvector by the scalar exponential

For a continuous linear endomorphism `g : E →L[ℂ] E` of a complex Banach space and a vector `v`
that is an eigenvector of `g` with eigenvalue `μ` (`g v = μ • v`), the operator exponential
`NormedSpace.exp g` acts on `v` by the *scalar* exponential of the eigenvalue:

`(NormedSpace.exp g) v = Complex.exp μ • v`.

This is the analytic form of the elementary fact that an eigenvector of `g` is an eigenvector of
every power `gⁿ` (with eigenvalue `μⁿ`), and hence of the exponential series `∑ₙ (n!)⁻¹ • gⁿ`,
which sums termwise to `Complex.exp μ • v`. Physically it is why an energy eigenstate evolves
only by a global phase under `exp(-iHt)`.
-/

@[expose] public section

open scoped Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **The exponential of an operator sends an eigenvector to the scaled eigenvector.**
If `g v = μ • v`, then `(NormedSpace.exp g) v = Complex.exp μ • v`. The proof expands
`NormedSpace.exp g = ∑ₙ (n!)⁻¹ • gⁿ` (`NormedSpace.exp_eq_tsum`), evaluates the sum at `v`
through the continuous evaluation map `T ↦ T v` (`ContinuousLinearMap.apply`, commuting with the
sum via `ContinuousLinearMap.map_tsum`), uses `gⁿ v = μⁿ • v`, and re-collects the scalar series
`∑ₙ (n!)⁻¹ • μⁿ = Complex.exp μ` (pulling `v` back out through
`ContinuousLinearMap.toSpanSingleton`). -/
theorem exp_apply_of_apply_eq_smul (g : E →L[ℂ] E) (v : E) (μ : ℂ) (h : g v = μ • v) :
    (NormedSpace.exp g) v = Complex.exp μ • v := by
  have hpow : ∀ n : ℕ, (g ^ n) v = μ ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, mul_apply_eq_comp, h, map_smul, ih, smul_smul, ← pow_succ']
  have hsum : Summable (fun n : ℕ => ((Nat.factorial n : ℂ)⁻¹) • g ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) g
  have hsumμ : Summable (fun n : ℕ => ((Nat.factorial n : ℂ)⁻¹) • μ ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) μ
  simp only [NormedSpace.exp_eq_tsum ℂ]
  rw [← ContinuousLinearMap.apply_apply (𝕜 := ℂ) (v := v), ContinuousLinearMap.map_tsum _ hsum]
  simp only [ContinuousLinearMap.apply_apply, _root_.smul_apply, hpow, smul_smul]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ,
    ← ContinuousLinearMap.toSpanSingleton_apply ℂ v, ContinuousLinearMap.map_tsum _ hsumμ]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]

end ContinuousLinearMap
