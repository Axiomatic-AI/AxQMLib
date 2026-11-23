/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import ToMathlib.Analysis.SpecialFunctions.Log.RpowTendsto
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import ToMathlib.Analysis.Convex.FunctionTopology
public import ToMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Operator convexity of `x ↦ x log x`

`Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order` now contains
`CFC.concaveOn_log` (the logarithm is operator concave) itself. This file adds the remaining
`CFC.convexOn_mul_log` (`x ↦ x * log x` is operator convex), obtained as a pointwise limit of
`cfc`-level identities as in the existing operator-monotonicity proof.
-/

public section

open Filter Topology

section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Classical Real in
/-- The cfc-arithmetic identity underlying the operator analogue of
`log x = lim_{p → 0} p⁻¹ * (x^p − 1)`: for a strictly positive operator `a` and `p : ℝ`,
`cfc (fun x ↦ p⁻¹ * (x^p − 1)) a = p⁻¹ • (a^p − 1)`. -/
lemma CFC.cfc_p_inv_rpow_sub_one_eq (p : ℝ) {a : A}
    (ha : IsStrictlyPositive a := by cfc_tac) :
    cfc (fun x : ℝ => p⁻¹ * (x ^ p - 1)) a = p⁻¹ • (a ^ p - 1) := by
  have hne : ∀ x ∈ spectrum ℝ a, x ≠ 0 := fun x hx => (ha.spectrum_pos hx).ne'
  have hrpow : ContinuousOn (fun x : ℝ => x ^ p) (spectrum ℝ a) :=
    ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (hne x hx))
  have hsub : ContinuousOn (fun x : ℝ => x ^ p - 1) (spectrum ℝ a) := hrpow.sub continuousOn_const
  simp only [← smul_eq_mul]
  rw [cfc_smul _ (hf := hsub), cfc_sub _ _ (hf := hrpow), cfc_const_one .., rpow_eq_cfc_real ..]

open Filter in
lemma CFC.tendsto_cfc_rpow_succ_sub_self_mul_log {a : A}
    (ha : IsStrictlyPositive a := by cfc_tac) :
    Tendsto (fun p : ℝ => cfc (fun x => p⁻¹ * (x ^ (p + 1) - x)) a) (𝓝[>] 0)
      (𝓝 (cfc (fun x : ℝ => x * Real.log x) a)) :=
  tendsto_cfc_fun
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi).mp
      Real.tendstoLocallyUniformlyOn_rpow_succ_sub_self_mul_log
      (spectrum ℝ a) (by grind) (by grind))
    (.of_forall fun p ↦ by
      have hne : ∀ x ∈ spectrum ℝ a, x ≠ 0 := fun x hx => (ha.spectrum_pos hx).ne'
      have hrpow : ContinuousOn (fun x : ℝ => x ^ (p + 1)) (spectrum ℝ a) :=
        ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (hne x hx))
      exact (hrpow.sub continuousOn_id).const_mul p⁻¹)

open Classical Real in
/-- The cfc-arithmetic identity underlying the operator analogue of
`x * log x = lim_{p ↘ 0} p⁻¹ * (x^(p+1) − x)`: for a strictly positive operator `a` and `p : ℝ`,
`cfc (fun x ↦ p⁻¹ * (x^(p+1) − x)) a = p⁻¹ • (a^(p+1) − a)`. -/
lemma CFC.cfc_p_inv_rpow_succ_sub_self_eq (p : ℝ) {a : A}
    (ha : IsStrictlyPositive a := by cfc_tac) :
    cfc (fun x : ℝ => p⁻¹ * (x ^ (p + 1) - x)) a = p⁻¹ • (a ^ (p + 1) - a) := by
  have hne : ∀ x ∈ spectrum ℝ a, x ≠ 0 := fun x hx => (ha.spectrum_pos hx).ne'
  have hrpow : ContinuousOn (fun x : ℝ => x ^ (p + 1)) (spectrum ℝ a) :=
    ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (hne x hx))
  have hsub : ContinuousOn (fun x : ℝ => x ^ (p + 1) - x) (spectrum ℝ a) :=
    hrpow.sub continuousOn_id
  simp only [← smul_eq_mul]
  rw [cfc_smul _ (hf := hsub), cfc_sub _ _ (hf := hrpow), cfc_id' ℝ .., rpow_eq_cfc_real ..]

open Classical Real in
/-- `x ↦ x * log x` is operator convex.

`x * log x = lim_{p ↘ 0} p⁻¹ * (x^(p+1) − x)` locally uniformly on `Ioi 0`, so the same identity
holds at the cfc level (`tendsto_cfc_rpow_succ_sub_self_mul_log`); each `x^(p+1) − x` is operator
convex on the strictly positive elements (`CFC.convexOn_rpow` on `[1, 2]` minus the affine
`id`); and `ConvexOn.of_tendsto_pointwise_on` passes convexity through the pointwise limit. -/
lemma CFC.convexOn_mul_log :
    ConvexOn ℝ {a : A | IsStrictlyPositive a} (cfc (fun x : ℝ ↦ x * Real.log x)) := by
  refine .of_tendsto_pointwise_on (l := (𝓝[>] 0)) convex_isStrictlyPositive ?_
    fun _ ha ↦ tendsto_cfc_rpow_succ_sub_self_mul_log ha
  filter_upwards [(nhdsGT_basis 0).mem_of_mem (zero_lt_one (α := ℝ))] with p ⟨hp, hp'⟩
  refine ConvexOn.congr ?_ fun _ ha ↦ (cfc_p_inv_rpow_succ_sub_self_eq p ha).symm
  exact (((CFC.convexOn_rpow ⟨by linarith, by linarith⟩).subset
    (s := {a : A | IsStrictlyPositive a}) (fun _ ha ↦ IsStrictlyPositive.nonneg ha)
    convex_isStrictlyPositive).sub (concaveOn_id convex_isStrictlyPositive)).smul (by positivity)

end
