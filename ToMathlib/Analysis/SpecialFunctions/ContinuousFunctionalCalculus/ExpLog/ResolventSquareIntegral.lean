/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.ResolventBounds

/-!
# Integral of the squared resolvent: `∫₀^∞ (a + s • 1)⁻² ds = a⁻¹`

For a strictly positive element `a` of a C⋆-algebra the squared resolvent integrates to the
inverse:

`∫₀^∞ (Ring.inverse (a + s • 1)) ^ 2 ds = Ring.inverse a`.

This is the operator lift of the scalar identity `∫₀^∞ (x + s)⁻² ds = x⁻¹` (`x > 0`), but is proved
directly at the operator level by the (second) fundamental theorem of calculus: the squared
resolvent is, up to sign, the `s`-derivative of the resolvent,
`d/ds Ring.inverse (a + s • 1) = -(Ring.inverse (a + s • 1)) ^ 2`
(`hasDerivAt_ringInverse_add_smul` with direction `1`), which decays like `s⁻¹` to `0` as
`s → ∞`; the improper fundamental theorem of calculus
(`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`) then evaluates the integral of the
derivative to `0 - (-Ring.inverse a) = Ring.inverse a`.

## Method

Apply `integral_Ioi_of_hasDerivAt_of_tendsto` to the antiderivative
`g s = -Ring.inverse (a + s • 1)`, whose derivative on `(0, ∞)` is the squared resolvent
`Ring.inverse (a + s • 1) ^ 2`. Its hypotheses use, throughout, the positive lower bound `m` on the
spectrum of `a` (`(algebraMap ℝ A) m ≤ a`, `0 < m`, from `CFC.exists_pos_algebraMap_le_iff`):
* continuity of `g` at the left endpoint `0`, from the resolvent derivative at `0` (`a` a unit);
* integrability of the squared resolvent on `(0, ∞)`, from the resolvent norm bound
  `‖Ring.inverse (a + s • 1)‖ ≤ (m + s)⁻¹` (`CStarAlgebra.norm_ringInverse_le_of_algebraMap_le`)
  squared and dominated by the integrable `integrableOn_Ioi_inv_add_sq`;
* `Ring.inverse (a + s • 1) → 0` as `s → ∞`, since `‖·‖ ≤ (m + s)⁻¹ → 0`.

## Main results

* `integral_Ioi_ringInverse_add_smul_one_sq` — `∫₀^∞ (Ring.inverse (a + s • 1)) ^ 2 ds =
  Ring.inverse a`.

This is the operator normalization underlying the trace-derivative identity
`tr(ω_p · d/dp cfc Real.log ω_p) = tr(ρ - σ)` in the second-derivative proof of concavity of the von
Neumann entropy (Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 11.22):
the parametric logarithm derivative `d/dp cfc Real.log ω_p = ∫₀^∞ (ω_p + s)⁻¹ Δ (ω_p + s)⁻¹ ds`,
contracted against `ω_p` under the trace and cyclically rearranged, collapses via
`∫₀^∞ (ω_p + s)⁻² ds = ω_p⁻¹` to `tr(Δ)` with `Δ = ρ - σ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

/-- **Integral of the squared resolvent.** For a strictly positive element `a` of a C⋆-algebra,
`∫₀^∞ (Ring.inverse (a + s • 1)) ^ 2 ds = Ring.inverse a`. The squared resolvent is, up to sign, the
`s`-derivative of the resolvent (`hasDerivAt_ringInverse_add_smul` in direction `1`), which decays
to `0` as `s → ∞`, so the improper fundamental theorem of calculus
(`integral_Ioi_of_hasDerivAt_of_tendsto`) evaluates the integral to
`0 - (-Ring.inverse a) = Ring.inverse a`. See the module docstring. -/
theorem integral_Ioi_ringInverse_add_smul_one_sq
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    {a : A} (ha : IsStrictlyPositive a) :
    ∫ s in Set.Ioi (0 : ℝ), Ring.inverse (a + s • (1 : A)) ^ 2 = Ring.inverse a := by
  -- A positive lower bound `m` on the spectrum of `a`.
  obtain ⟨m, hm, hma⟩ : ∃ m, 0 < m ∧ (algebraMap ℝ A) m ≤ a :=
    (CFC.exists_pos_algebraMap_le_iff (a := a)).mpr
      (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp ha).2
  -- `a + s • 1` is a unit for `s ≥ 0`, with resolvent norm `≤ (m + s)⁻¹`.
  have hunit : ∀ s : ℝ, 0 ≤ s → IsUnit (a + s • (1 : A)) :=
    fun s hs => (ha.add_nonneg (smul_nonneg hs zero_le_one)).isUnit
  have hnorm : ∀ s : ℝ, 0 ≤ s → ‖Ring.inverse (a + s • (1 : A))‖ ≤ (m + s)⁻¹ := by
    intro s hs
    refine CStarAlgebra.norm_ringInverse_le_of_algebraMap_le (m := m + s) (by linarith) ?_
    rw [map_add, Algebra.algebraMap_eq_smul_one (R := ℝ) (A := A) s]
    gcongr
  -- The resolvent is continuous at every `s ≥ 0` (a unit there).
  have hResCont : ∀ s : ℝ, 0 ≤ s →
      ContinuousAt (fun t : ℝ => Ring.inverse (a + t • (1 : A))) s :=
    fun s hs => (hasDerivAt_ringInverse_add_smul (hunit s hs)).continuousAt
  -- The antiderivative `g s = -Ring.inverse (a + s • 1)` has derivative `(Ring.inverse ·) ^ 2`.
  have hderiv : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivAt (fun t : ℝ => -Ring.inverse (a + t • (1 : A)))
        (Ring.inverse (a + s • (1 : A)) ^ 2) s := by
    intro s hs
    simp only [mem_Ioi] at hs
    have hu := hunit s hs.le
    have hinv : Ring.inverse (a + s • (1 : A)) = ↑hu.unit⁻¹ := by
      conv_lhs => rw [← hu.unit_spec]
      rw [Ring.inverse_unit]
    have h := (hasDerivAt_ringInverse_add_smul (a := a) (b := (1 : A)) (t₀ := s) hu).neg
    simp only [neg_neg, mul_one] at h
    rw [hinv, sq]
    exact h
  -- The squared resolvent is integrable on `(0, ∞)`, dominated by `(m + s)⁻²`.
  have hint : IntegrableOn (fun s : ℝ => Ring.inverse (a + s • (1 : A)) ^ 2) (Ioi 0) := by
    have hmeas : AEStronglyMeasurable
        (fun s : ℝ => Ring.inverse (a + s • (1 : A)) ^ 2) (volume.restrict (Ioi 0)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact fun s hs => (((hResCont s (le_of_lt hs)).continuousWithinAt).pow 2)
    refine (integrableOn_Ioi_inv_add_sq hm).mono' hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ ?_)
    intro s hs
    simp only [mem_Ioi] at hs
    calc ‖Ring.inverse (a + s • (1 : A)) ^ 2‖
        = ‖Ring.inverse (a + s • (1 : A)) * Ring.inverse (a + s • (1 : A))‖ := by rw [sq]
      _ ≤ ‖Ring.inverse (a + s • (1 : A))‖ * ‖Ring.inverse (a + s • (1 : A))‖ := norm_mul_le _ _
      _ ≤ (m + s)⁻¹ * (m + s)⁻¹ :=
            mul_le_mul (hnorm s hs.le) (hnorm s hs.le) (norm_nonneg _) (by positivity)
      _ = (m + s)⁻¹ ^ 2 := (sq _).symm
  -- Continuity of `g` at `0` and its limit `0` at `∞`.
  have hcont0 : ContinuousWithinAt (fun t : ℝ => -Ring.inverse (a + t • (1 : A))) (Ici 0) 0 :=
    ((hResCont 0 le_rfl).continuousWithinAt).neg
  have htend : Tendsto (fun t : ℝ => -Ring.inverse (a + t • (1 : A))) atTop (𝓝 0) := by
    have hg : Tendsto (fun s : ℝ => (m + s)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop m tendsto_id)
    have hres : Tendsto (fun t : ℝ => Ring.inverse (a + t • (1 : A))) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hg
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs using hnorm s hs
    simpa using hres.neg
  -- The improper fundamental theorem of calculus.
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto hcont0 hderiv hint htend
