/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import ToMathlib.Analysis.Normed.Algebra.Spectrum

/-! # Continuity of `rpow` in the exponent

This file collects continuity results for `CFC.rpow` when the exponent, rather than the base,
varies: `a ^ y` is continuous (indeed continuous at every point) as a function of the real
exponent `y` for a strictly positive `a`, and consequently `a ^ (1 - p) * b ^ p` is continuous
in `p` and tends to `a` as `p → 0`. This last fact is the operator-level convergence underlying
Lindblad's limit form of the quantum relative entropy.
-/

public section

open scoped NNReal Topology

namespace CFC

section unital

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

open scoped ContinuousFunctionalCalculus in
/-- For a strictly positive element of a unital C⋆-algebra, the operator power `a ^ y` is
continuous in the real exponent `y` at every point. -/
lemma continuousAt_const_rpow {a : A} (ha : IsStrictlyPositive a) {y₀ : ℝ} :
    ContinuousAt (fun y : ℝ ↦ a ^ y) y₀ := by
  have h0 : (0 : ℝ≥0) ∉ spectrum ℝ≥0 a := by
    exact_mod_cast spectrum.zero_notMem ℝ ha.isUnit
  refine continuousAt_cfc_fun ?_
    (.of_forall fun y _ hz ↦ (NNReal.continuousAt_rpow_const
      (Or.inl fun hz0 ↦ h0 (hz0 ▸ hz))).continuousWithinAt)
  rw [tendstoUniformlyOn_iff_restrict]
  exact Continuous.tendstoUniformly _ (continuous_iff_continuousAt.mpr fun ⟨_, z⟩ ↦
    Filter.Tendsto.nnrpow (continuous_subtype_val.comp continuous_snd).continuousAt
      continuous_fst.continuousAt (Or.inl fun heq ↦ h0 (heq ▸ z.2))) y₀

/-- For a strictly positive element of a unital C⋆-algebra, the operator power `a ^ y` is
continuous in the real exponent `y`. This is the companion to `continuousOn_rpow`, which varies
the base for a fixed exponent. -/
lemma continuous_const_rpow {a : A} (ha : IsStrictlyPositive a) :
    Continuous (fun y : ℝ ↦ a ^ y) :=
  continuous_iff_continuousAt.mpr fun _ ↦ continuousAt_const_rpow ha

/-- For strictly positive elements `a, b` of a unital C⋆-algebra, the operator product
`a ^ (1 - p) * b ^ p` is continuous in the real exponent `p`. -/
lemma continuous_rpow_one_sub_mul_rpow {a b : A} (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) :
    Continuous (fun p : ℝ ↦ a ^ (1 - p) * b ^ p) :=
  ((continuous_const_rpow ha).comp (by fun_prop)).mul (continuous_const_rpow hb)

open Filter in
/-- For strictly positive elements `a, b` of a unital C⋆-algebra, the operator product
`a ^ (1 - p) * b ^ p` converges to `a` as the real exponent `p` tends to `0`.

This is the operator-level convergence underlying Lindblad's limit form of the quantum
relative entropy `H(a | b) = lim_{p → 0⁺} p⁻¹ · (Tr a - Tr (a ^ (1 - p) * b ^ p))`. -/
lemma tendsto_rpow_one_sub_mul_rpow {a b : A} (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) :
    Tendsto (fun p : ℝ ↦ a ^ (1 - p) * b ^ p) (𝓝 0) (𝓝 a) := by
  simpa [CFC.rpow_one a ha.nonneg, CFC.rpow_zero b hb.nonneg]
    using (continuous_rpow_one_sub_mul_rpow ha hb).tendsto 0

open Filter in
/-- **Regularization limit for the operator real power.** For a nonnegative element `a` and an
exponent `p ≥ 0`, the strictly-positive regularizations `(a + ε • 1) ^ p` converge to `a ^ p` as
`ε → 0⁺`. Whereas `continuousOn_rpow` varies the base over the *open* strictly-positive cone, this
approaches the *boundary* of the positive cone along the regularizing path `ε ↦ a + ε • 1`: since
`a + ε • 1 → a` and `x ↦ x ^ p` is continuous on the compact interval `[0, (‖a‖ + ‖1‖)‖1‖]` — which
contains the real spectrum of `a` and of every `a + ε • 1` (`0 < ε ≤ 1`) by
`spectrum.subset_Icc_norm_mul_of_nonneg` — `Filter.Tendsto.cfc` transports the convergence through
the continuous functional calculus, using `a ^ p = cfc (· ^ p) a` (`CFC.rpow_eq_cfc_real`). -/
lemma tendsto_rpow_add_smul_one [ContinuousStar A] [CompleteSpace A] [PosSMulMono ℝ A]
    {a : A} (ha : 0 ≤ a) {p : ℝ} (hp : 0 ≤ p) :
    Tendsto (fun ε : ℝ => (a + ε • (1 : A)) ^ p) (𝓝[>] (0 : ℝ)) (𝓝 (a ^ p)) := by
  have hone : (0 : ℝ) ≤ ‖(1 : A)‖ := norm_nonneg _
  have hf_cont : ContinuousOn (fun x : ℝ => x ^ p) (Set.Icc 0 ((‖a‖ + ‖(1 : A)‖) * ‖(1 : A)‖)) :=
    fun x _ => (Real.continuousAt_rpow_const x p (Or.inr hp)).continuousWithinAt
  have h_elem : Tendsto (fun ε : ℝ => a + ε • (1 : A)) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    have hc : Continuous (fun ε : ℝ => a + ε • (1 : A)) := by fun_prop
    have h2 := hc.tendsto 0
    simp only [zero_smul, add_zero] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have h1 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with ε hε
    exact le_of_lt hε
  have h_nonneg_ev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ a + ε • (1 : A) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact add_nonneg ha (smul_nonneg (le_of_lt hε) zero_le_one)
  have h_spec_ev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      spectrum ℝ (a + ε • (1 : A)) ⊆ Set.Icc 0 ((‖a‖ + ‖(1 : A)‖) * ‖(1 : A)‖) := by
    filter_upwards [h1, h_nonneg_ev, self_mem_nhdsWithin] with ε hε1 hn hεpos
    refine (spectrum.subset_Icc_norm_mul_of_nonneg hn).trans (Set.Icc_subset_Icc_right ?_)
    have hnorm : ‖a + ε • (1 : A)‖ ≤ ‖a‖ + ‖(1 : A)‖ := by
      calc ‖a + ε • (1 : A)‖ ≤ ‖a‖ + ‖ε • (1 : A)‖ := norm_add_le _ _
        _ = ‖a‖ + ε * ‖(1 : A)‖ := by rw [norm_smul, Real.norm_of_nonneg (le_of_lt hεpos)]
        _ ≤ ‖a‖ + ‖(1 : A)‖ := by nlinarith [hone]
    exact mul_le_mul_of_nonneg_right hnorm hone
  have h_sa_ev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), IsSelfAdjoint (a + ε • (1 : A)) := by
    filter_upwards [h_nonneg_ev] with ε hn using hn.isSelfAdjoint
  have h_spec_a : spectrum ℝ a ⊆ Set.Icc 0 ((‖a‖ + ‖(1 : A)‖) * ‖(1 : A)‖) :=
    (spectrum.subset_Icc_norm_mul_of_nonneg ha).trans (Set.Icc_subset_Icc_right
      (mul_le_mul_of_nonneg_right (by nlinarith [hone]) hone))
  have key := Filter.Tendsto.cfc (X := ℝ) isCompact_Icc (fun x : ℝ => x ^ p)
    h_elem h_spec_ev h_sa_ev h_spec_a ha.isSelfAdjoint
  rw [← CFC.rpow_eq_cfc_real ha] at key
  refine key.congr' ?_
  filter_upwards [h_nonneg_ev] with ε hn using (CFC.rpow_eq_cfc_real hn).symm

end unital

end CFC
