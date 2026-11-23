/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import ToMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
public import ToMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import ToMathlib.Analysis.SpecialFunctions.Log.IntegralRepresentation
public import ToMathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Integral representation of the continuous-functional-calculus logarithm

For a strictly positive element `a` of a C⋆-algebra (nonnegative and invertible) the operator
logarithm `cfc Real.log a` has the improper-integral representation

`cfc Real.log a = ∫₀^∞ ((1 + s)⁻¹ • 1 - Ring.inverse (a + s • 1)) ds`,

the operator lift of the scalar Frullani-type identity
`log x = ∫₀^∞ ((1 + s)⁻¹ - (x + s)⁻¹) ds` (`Real.log_eq_integral_Ioi_inv_add_sub_inv_add`). The
integrand `(1 + s)⁻¹ • 1 - Ring.inverse (a + s • 1)` is exactly `cfc` applied to the scalar
integrand `x ↦ (1 + s)⁻¹ - (x + s)⁻¹` (the reference term `(1 + s)⁻¹ • 1 = cfc (fun _ ↦ (1+s)⁻¹) a`,
the resolvent term `Ring.inverse (a + s • 1) = cfc (fun x ↦ (x + s)⁻¹) a`), so the identity is the
statement that the continuous functional calculus commutes with the Bochner integral over `s`.

## Method

The commutation is Mathlib's `cfc_setIntegral`, applied to `f s x = (1 + s)⁻¹ - (x + s)⁻¹` on
`Ioi 0 ×ˢ spectrum ℝ a`. Its hypotheses are discharged from strict positivity:
* the spectrum is a compact subset of `Ioi 0`, hence bounded in `Icc m ‖a‖` with `0 < m` its
  (attained) minimum — used both for continuity of the integrand and for the dominating bound;
* `‖(1 + s)⁻¹ - (x + s)⁻¹‖` is dominated, uniformly over `x ∈ spectrum ℝ a`, by
  `|(1 + s)⁻¹ - (m + s)⁻¹| + |(1 + s)⁻¹ - (‖a‖ + s)⁻¹|`, since the integrand is monotone in `x`;
  the dominating function is integrable on `Ioi 0` by two applications of the scalar
  `Real.integrableOn_Ioi_inv_add_sub_inv_add`.
On the resulting `cfc (fun x ↦ ∫₀^∞ ((1+s)⁻¹ - (x+s)⁻¹) ds) a` the inner integral equals
`Real.log x` for every spectral point `x` (all positive), so `cfc_congr` collapses it to
`cfc Real.log a`; each integrand `cfc (fun x ↦ (1+s)⁻¹ - (x+s)⁻¹) a` is unfolded to the resolvent
form with `cfc_sub`, `cfc_const`, `cfc_comp`, and `cfc_ringInverse_id` (`a + s • 1` a unit by
`isStrictlyPositive_add_smul_one`).

## Main results

* `cfc_log_eq_integral_Ioi_resolvent` — the integral representation itself.

This is an analysis foundation for the second-derivative proof of concavity of the von Neumann
entropy (Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 11.22): the
representation, differentiated along a mixing line `s ↦ (ω_p + s)⁻¹` via the resolvent derivative
`hasDerivAt_ringInverse_add_smul`, yields the parametric derivative of the operator logarithm.
-/

@[expose] public section

open MeasureTheory Set

/-- **Integral representation of the operator logarithm.** For a strictly positive element `a` of
a C⋆-algebra (`0 ≤ a` and `a` invertible),

`cfc Real.log a = ∫₀^∞ ((1 + s)⁻¹ • 1 - Ring.inverse (a + s • 1)) ds`.

This is the operator lift of the scalar identity
`log x = ∫₀^∞ ((1 + s)⁻¹ - (x + s)⁻¹) ds` (`Real.log_eq_integral_Ioi_inv_add_sub_inv_add`): the
integrand is `cfc` applied to `x ↦ (1 + s)⁻¹ - (x + s)⁻¹`, so the identity states that the
continuous functional calculus commutes with the Bochner integral over `s` (`cfc_setIntegral`). See
the module docstring for the discharge of the domination/continuity hypotheses. -/
theorem cfc_log_eq_integral_Ioi_resolvent
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    {a : A} (ha : IsStrictlyPositive a) :
    cfc Real.log a
      = ∫ s in Set.Ioi (0 : ℝ), ((1 + s)⁻¹ • (1 : A) - Ring.inverse (a + s • 1)) := by
  have hsa : IsSelfAdjoint a := ha.1.isSelfAdjoint
  -- The spectrum is a compact subset of `Icc m ‖a‖` with `0 < m` its attained minimum.
  have hsub : spectrum ℝ a ⊆ Set.Icc 0 ‖a‖ := spectrum.subset_Icc_norm_of_nonneg ha.1
  have h0 : (0 : ℝ) ∉ spectrum ℝ a := (spectrum.zero_notMem_iff ℝ).mpr ha.isUnit
  have hcompact : IsCompact (spectrum ℝ a) := spectrum.isCompact a
  have hne : (spectrum ℝ a).Nonempty := ContinuousFunctionalCalculus.spectrum_nonempty a hsa
  obtain ⟨m, hm_mem, hm_min⟩ := hcompact.exists_isMinOn hne continuousOn_id
  have hm_pos : 0 < m := by
    rcases lt_or_eq_of_le (hsub hm_mem).1 with h | h
    · exact h
    · exact absurd (h ▸ hm_mem) h0
  have hM_pos : 0 < ‖a‖ := lt_of_lt_of_le hm_pos (hsub hm_mem).2
  have hpos : ∀ x ∈ spectrum ℝ a, (0 : ℝ) < x := fun x hx => lt_of_lt_of_le hm_pos (hm_min hx)
  have hsp : ∀ x ∈ spectrum ℝ a, (0 : ℝ) ≤ x := fun x hx => (hpos x hx).le
  -- The dominating function `bound` and its integrability on `Ioi 0`.
  set bound : ℝ → ℝ := fun s => |(1 + s)⁻¹ - (m + s)⁻¹| + |(1 + s)⁻¹ - (‖a‖ + s)⁻¹| with hbound_def
  have hbound_int : IntegrableOn bound (Set.Ioi 0) :=
    ((Real.integrableOn_Ioi_inv_add_sub_inv_add hm_pos).abs).add
      ((Real.integrableOn_Ioi_inv_add_sub_inv_add hM_pos).abs)
  -- Uniform (in the spectral point) domination: the integrand is monotone in `z`, so its value
  -- lies between the endpoints `z = m` and `z = ‖a‖`.
  have hdom : ∀ s : ℝ, 0 < s → ∀ z : ℝ, m ≤ z → z ≤ ‖a‖ →
      |(1 + s)⁻¹ - (z + s)⁻¹| ≤ bound s := by
    intro s hs z hmz hzM
    have hms : 0 < m + s := by linarith
    have hzs : 0 < z + s := by linarith
    have hMs : 0 < ‖a‖ + s := by linarith
    have h1 : (z + s)⁻¹ ≤ (m + s)⁻¹ := (inv_le_inv₀ hzs hms).mpr (by linarith)
    have h2 : (‖a‖ + s)⁻¹ ≤ (z + s)⁻¹ := (inv_le_inv₀ hMs hzs).mpr (by linarith)
    set c := (1 + s)⁻¹
    set P := c - (m + s)⁻¹ with hP
    set Q := c - (‖a‖ + s)⁻¹ with hQ
    have hlo : P ≤ c - (z + s)⁻¹ := by rw [hP]; linarith
    have hhi : c - (z + s)⁻¹ ≤ Q := by rw [hQ]; linarith
    rw [show |(1 + s)⁻¹ - (z + s)⁻¹| = |c - (z + s)⁻¹| from rfl, abs_le]
    exact ⟨by linarith [neg_abs_le P, abs_nonneg Q], by linarith [le_abs_self Q, abs_nonneg P]⟩
  -- Joint continuity of the scalar integrand on `Ioi 0 ×ˢ spectrum ℝ a`.
  have hcont : ContinuousOn (Function.uncurry (fun (s r : ℝ) => (1 + s)⁻¹ - (r + s)⁻¹))
      (Set.Ioi 0 ×ˢ spectrum ℝ a) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.inv₀ (by fun_prop)
      rintro ⟨s, r⟩ ⟨hs, hr⟩; simp only [Set.mem_Ioi] at hs; positivity
    · apply ContinuousOn.inv₀ (by fun_prop)
      rintro ⟨s, r⟩ ⟨hs, hr⟩; simp only [Set.mem_Ioi] at hs
      have := hsp r hr; positivity
  -- The a.e. domination hypothesis for `cfc_setIntegral`.
  have hbnd : ∀ᵐ (s : ℝ) ∂(volume.restrict (Set.Ioi 0)), ∀ z ∈ spectrum ℝ a,
      ‖(fun (s r : ℝ) => (1 + s)⁻¹ - (r + s)⁻¹) s z‖ ≤ bound s := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ ?_)
    intro s hs z hz
    simp only [Set.mem_Ioi] at hs
    rw [Real.norm_eq_abs]
    exact hdom s hs z (hm_min hz) (hsub hz).2
  -- The continuous functional calculus commutes with the integral over `s`.
  have key := cfc_setIntegral (𝕜 := ℝ) (μ := volume) measurableSet_Ioi
    (fun (s r : ℝ) => (1 + s)⁻¹ - (r + s)⁻¹) bound a hcont hbnd
    hbound_int.hasFiniteIntegral hsa
  -- The left-hand cfc is `cfc Real.log a`: on the (positive) spectrum the inner integral is `log`.
  have hLHS : cfc (fun r => ∫ s in Set.Ioi (0 : ℝ), ((1 + s)⁻¹ - (r + s)⁻¹)) a
      = cfc Real.log a := by
    apply cfc_congr
    intro r hr
    exact (Real.log_eq_integral_Ioi_inv_add_sub_inv_add (hpos r hr)).symm
  rw [← hLHS, key]
  -- Each cfc integrand is the resolvent form.
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  simp only [Set.mem_Ioi] at hs
  have hunit : IsUnit (a + s • 1) := (isStrictlyPositive_add_smul_one ha.1 hs).isUnit
  have hc2 : ContinuousOn (fun r : ℝ => (r + s)⁻¹) (spectrum ℝ a) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro r hr; have := hsp r hr; positivity
  rw [cfc_sub _ _ a continuousOn_const hc2]
  congr 1
  · rw [cfc_const _ _ (p := IsSelfAdjoint) hsa, Algebra.algebraMap_eq_smul_one]
  · have hshift : cfc (fun r : ℝ => r + s) a = a + s • 1 := by
      rw [cfc_add a (fun x => x) (fun _ => s) continuousOn_id continuousOn_const,
        cfc_id' ℝ a, cfc_const _ _ (p := IsSelfAdjoint) hsa, Algebra.algebraMap_eq_smul_one]
    have himg : ContinuousOn (fun y : ℝ => y⁻¹) ((fun r : ℝ => r + s) '' spectrum ℝ a) := by
      apply ContinuousOn.inv₀ (by fun_prop)
      rintro _ ⟨r, hr, rfl⟩; have := hsp r hr; positivity
    rw [show (fun r : ℝ => (r + s)⁻¹) = (fun y : ℝ => y⁻¹) ∘ (fun r : ℝ => r + s) from rfl,
      cfc_comp (fun y => y⁻¹) (fun r => r + s) a hsa himg (by fun_prop), hshift,
      cfc_ringInverse_id (a + s • 1) hunit]
