/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Module

/-!
# Convexity of `CFC.rpow` on `[1, 2]`, and the `Y ≤ √Z` abs-detour

`Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order` now contains
`CFC.concaveOn_nnrpow`/`CFC.concaveOn_rpow` (operator concavity on `p ∈ [0,1]`). This file adds
the missing convexity companions on `p ∈ [1,2]`, plus the `√`-detour inequality:

+ `CFC.convexOn_nnrpow`, `CFC.convexOn_rpow`: `a ↦ a ^ p` is operator convex on the
  nonnegative cone for `p ∈ [1,2]`
+ `CFC.le_sqrt_of_mul_self_le`: for self-adjoint `Y` with `Y * Y ≤ Z`, `Y ≤ √Z`.

## References

+ [carlen2010] Eric A. Carlen, "Trace inequalities and quantum entropies: An introductory course"
  (see Lemma 2.8)
-/

public section

open Set
open scoped NNReal

namespace CFC

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Real MeasureTheory

/-- This is an intermediate result; use the more general `CFC.convexOn_nnrpow` instead. -/
private lemma convexOn_nnrpow_Ioo {p : ℝ≥0} (hp : p ∈ Ioo 1 2) :
    ConvexOn ℝ (Ici (0 : A)) (fun a ↦ a ^ p) := by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂ A hp
  have h₃' : (Ici 0).EqOn (fun a : A ↦ a ^ p)
      (fun a : A ↦ ∫ t in Ioi 0, cfcₙ (rpowIntegrand₁₂ p t) a ∂μ) :=
    fun a ha ↦ (hμ a ha).2
  refine ConvexOn.congr ?_ h₃'.symm
  refine integral_convexOn_of_integrand_ae (convex_Ici 0) ?_ fun a ha ↦ (hμ a ha).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact convexOn_cfcₙ_rpowIntegrand₁₂ ht

/-- `a ↦ a ^ p` is operator convex on the nonnegative cone for `p ∈ [1,2]`. -/
lemma convexOn_nnrpow {p : ℝ≥0} (hp : p ∈ Icc 1 2) :
    ConvexOn ℝ (Ici (0 : A)) (fun a ↦ a ^ p) := by
  have hIcc : Icc (1 : ℝ≥0) 2 = Ioo 1 2 ∪ {1} ∪ {2} := by ext; simp
  rw [hIcc] at hp
  obtain (hp | hp) | hp := hp
  · exact convexOn_nnrpow_Ioo hp
  · simp only [mem_singleton_iff] at hp
    subst hp
    refine ⟨convex_Ici 0, fun a (ha : 0 ≤ a) b (hb : 0 ≤ b) α β hα hβ hαβ ↦ ?_⟩
    have hab : (0 : A) ≤ α • a + β • b := add_nonneg (smul_nonneg hα ha) (smul_nonneg hβ hb)
    simp [nnrpow_one a, nnrpow_one b, nnrpow_one (α • a + β • b)]
  · simp only [mem_singleton_iff] at hp
    subst hp
    refine ⟨convex_Ici 0, fun a (ha : 0 ≤ a) b (hb : 0 ≤ b) α β hα hβ hαβ ↦ ?_⟩
    have hab : (0 : A) ≤ α • a + β • b := add_nonneg (smul_nonneg hα ha) (smul_nonneg hβ hb)
    beta_reduce
    rw [nnrpow_two a, nnrpow_two b, nnrpow_two (α • a + β • b)]
    calc (α • a + β • b) * (α • a + β • b)
        = α • (a * a) + β • (b * b) - (α * β) • ((a - b) * (a - b)) := by
          have h_sq : ((a - b : A) * (a - b)) = a * a - a * b - b * a + b * b := by noncomm_ring
          have h_prod : (α • a + β • b) * (α • a + β • b)
              = (α * α) • (a * a) + (α * β) • (a * b) + (β * α) • (b * a) + (β * β) • (b * b) := by
            simp only [mul_add, add_mul, smul_mul_smul_comm]; abel
          have hβα : β = 1 - α := by linarith
          rw [h_sq, h_prod]; subst hβα; match_scalars <;> ring
      _ ≤ α • (a * a) + β • (b * b) := sub_le_self _ <| smul_nonneg (mul_nonneg hα hβ)
          (IsSelfAdjoint.sub ha.isSelfAdjoint hb.isSelfAdjoint).mul_self_nonneg

end NonUnitalCStarAlgebra

section UnitalCStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `a ↦ a ^ p` is operator convex on the nonnegative cone for `p ∈ [1,2]`. -/
lemma convexOn_rpow {p : ℝ} (hp : p ∈ Icc 1 2) :
    ConvexOn ℝ (Ici (0 : A)) (fun a ↦ a ^ p) := by
  let q : ℝ≥0 := ⟨p, by linarith [hp.1]⟩
  change ConvexOn ℝ (Ici (0 : A)) (fun a ↦ a ^ (q : ℝ))
  have hq_pos : 0 < q := by change (0 : ℝ) < p; linarith [hp.1]
  simp_rw [← CFC.nnrpow_eq_rpow hq_pos]
  exact convexOn_nnrpow hp

/-- Abs-detour: for self-adjoint `Y` with `Y * Y ≤ Z`, `Y ≤ √Z`. The argument routes via
`Y ≤ |Y| = √(Y²) ≤ √Z`. -/
lemma le_sqrt_of_mul_self_le {Y Z : A} (hY : IsSelfAdjoint Y) (h : Y * Y ≤ Z) :
    Y ≤ sqrt Z :=
  calc Y ≤ CFC.abs Y := by
        rw [← sub_nonneg, CFC.abs_sub_self Y hY]
        exact nsmul_nonneg (CFC.negPart_nonneg Y) 2
    _ = sqrt (Y * Y) := by rw [CFC.abs, hY.star_eq]
    _ ≤ sqrt Z := sqrt_le_sqrt _ _ h

end UnitalCStarAlgebra

end CFC
