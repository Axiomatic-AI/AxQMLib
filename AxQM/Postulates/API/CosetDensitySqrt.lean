/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CosetDensityState
import AxQM.Concrete.CosetStateOverlap
import ToMathlib.Analysis.InnerProductSpace.CFC

/-!
# AxQM.Postulates.API — the operator square root of the coset density state `σ_K`

The operator square root of `σ_K`, needed for the *fidelity-metric* distinguishability of the
Nielsen & Chuang Problem 5.5 reduced states. Because `σ_K = (|K|/|G|) Π_K` is a scalar multiple of
the coset projector (`Concrete.cosetDensity_mul_self`: `σ_K² = (|K|/|G|) σ_K`), its operator square
root is again a scalar multiple of `σ_K`: `√σ_K = √(|G|/|K|) · σ_K`
(`cosetDensityState_op_cfc_sqrt`). The affinity theorems in `AxQM/NC/Ch5/Problem5_5.lean` use this:
it turns `√σ_K √σ_{K'}` into a scalar multiple of `σ_K σ_{K'}`, so `A(σ_K, σ_{K'}) = tr(√σ_K
√σ_{K'})` reduces to the Hilbert–Schmidt overlap `|K∩K'|/|G|`. Both statements are about `State.op`
and `cfc Real.sqrt`.
-/

noncomputable section

open scoped ComplexOrder

namespace AxQM

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable (K : Subgroup G) [DecidablePred (· ∈ K)]

/-- **The coset density state's operator is a scalar multiple of a projector**:
`σ_K.op · σ_K.op = (|K|/|G|) · σ_K.op`. The operator form of `Concrete.cosetDensity_mul_self`,
transported through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM` (`map_mul`, `map_smul`). -/
theorem cosetDensityState_op_mul_self :
    (cosetDensityState K).op * (cosetDensityState K).op
      = ((Nat.card ↥K : ℝ) / Fintype.card G : ℂ) • (cosetDensityState K).op := by
  have h1 : (cosetDensityState K).op * (cosetDensityState K).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G)
          (Concrete.cosetDensity K * Concrete.cosetDensity K) := by
    rw [cosetDensityState_op]
    exact (map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G)) _ _).symm
  have h2 : ((Nat.card ↥K : ℝ) / Fintype.card G : ℂ) • (cosetDensityState K).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G)
          (((Nat.card ↥K : ℝ) / Fintype.card G : ℂ) • Concrete.cosetDensity K) := by
    rw [cosetDensityState_op]
    exact (map_smul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G)) _ _).symm
  rw [h1, h2, Concrete.cosetDensity_mul_self]

/-- **The operator square root of the coset density state is a scalar multiple of it**:
`√σ_K = √(|G|/|K|) · σ_K`. Since `σ_K.op² = (|K|/|G|) σ_K.op` (`cosetDensityState_op_mul_self`), the
element `b = √(|G|/|K|) · σ_K.op` is positive (a nonnegative scalar times the positive `σ_K.op`) and
squares to `b² = (|G|/|K|)·(|K|/|G|)·σ_K.op = σ_K.op`; by uniqueness of the positive square root
(`CFC.sqrt_unique`) it *is* `√σ_K`.

This closed form is what makes the affinity of two coset reduced states computable: `√σ_K √σ_{K'}`
is a scalar multiple of `σ_K σ_{K'}`, reducing the quantum affinity to the Hilbert–Schmidt overlap
`Concrete.cosetDensity_trace_mul`. -/
theorem cosetDensityState_op_cfc_sqrt :
    cfc Real.sqrt (cosetDensityState K).op
      = ((Real.sqrt (Fintype.card G / Nat.card ↥K) : ℝ) : ℂ) • (cosetDensityState K).op := by
  have hpos : (0 : (groupSystem G) →L[ℂ] (groupSystem G)) ≤ (cosetDensityState K).op :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mpr (cosetDensityState K).isPositive_op
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hK : (0 : ℝ) < Nat.card ↥K := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_pos
  -- `√(|G|/|K|)²·(|K|/|G|) = (|G|/|K|)·(|K|/|G|) = 1`: the scalars in `b·b` collapse.
  have hscal : (((Real.sqrt (Fintype.card G / Nat.card ↥K) : ℝ) : ℂ)
      * ((Real.sqrt (Fintype.card G / Nat.card ↥K) : ℝ) : ℂ))
      * ((Nat.card ↥K : ℝ) / Fintype.card G : ℂ) = (1 : ℂ) := by
    have h1 : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have h2 : (Nat.card ↥K : ℂ) ≠ 0 := by
      rw [Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    field_simp
  set b := ((Real.sqrt (Fintype.card G / Nat.card ↥K) : ℝ) : ℂ) • (cosetDensityState K).op with hb
  have hbpos : (0 : (groupSystem G) →L[ℂ] (groupSystem G)) ≤ b := by
    rw [hb, Complex.coe_smul]; exact smul_nonneg (Real.sqrt_nonneg _) hpos
  have hbb : b * b = (cosetDensityState K).op := by
    rw [hb, smul_mul_smul_comm, cosetDensityState_op_mul_self, smul_smul, hscal, one_smul]
  calc cfc Real.sqrt (cosetDensityState K).op
      = cfc Real.sqrt (b * b) := by rw [hbb]
    _ = b := ContinuousLinearMap.cfc_real_sqrt_mul_self_eq_self_of_nonneg hbpos

end AxQM
