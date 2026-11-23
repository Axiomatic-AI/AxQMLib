/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.IntegralRepresentation
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.ResolventBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Parametric derivative of the operator logarithm along an affine line

For a strictly positive element `a + p₀ • b` of a C⋆-algebra (with `b` self-adjoint) the operator
logarithm along the affine line `p ↦ cfc Real.log (a + p • b)` is differentiable at `p₀`, with the
"resolvent-Bochner-integral" derivative

`d/dp cfc Real.log (a + p • b) |_{p₀}
  = ∫₀^∞ (a + p₀ • b + s • 1)⁻¹ * b * (a + p₀ • b + s • 1)⁻¹ ds`.

This is obtained by differentiating the integral representation
`cfc Real.log a = ∫₀^∞ ((1 + s)⁻¹ • 1 - Ring.inverse (a + s • 1)) ds`
(`cfc_log_eq_integral_Ioi_resolvent`) under the integral sign: the `s`-integrand
`(1 + s)⁻¹ • 1 - Ring.inverse (a + p • b + s • 1)` has `p`-derivative
`(a + p • b + s • 1)⁻¹ * b * (a + p • b + s • 1)⁻¹` (the resolvent "sandwich" derivative
`hasDerivAt_ringInverse_add_smul`, with the leading minus sign from differentiating the
*subtracted* resolvent term), dominated uniformly in `p` near `p₀` by the integrable
`‖b‖ (m + s)⁻²`.

## Method

The differentiation-under-the-integral is Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, applied with `μ = volume.restrict (Ioi 0)`,
`F p s = (1 + s)⁻¹ • 1 - Ring.inverse (a + p • b + s • 1)` and
`F' p s = Ring.inverse (a + p • b + s • 1) * b * Ring.inverse (a + p • b + s • 1)`. Its hypotheses
are discharged from a **local uniform lower bound** on the line: for `a + p₀ • b` strictly
positive and `b` self-adjoint there are `m > 0` and a ball around `p₀` on which
`(algebraMap ℝ A) m ≤ a + p • b`
(`exists_forall_mem_ball_algebraMap_le_add_smul`, from `CFC.exists_pos_algebraMap_le_iff` and the
self-adjoint perturbation bound `IsSelfAdjoint.neg_algebraMap_norm_le_self`). On that ball:
* each `a + p • b` is strictly positive, so the base-point integrand is integrable
  (`integrableOn_Ioi_inv_smul_one_sub_ringInverse`) and `cfc Real.log (a + p • b)` equals `∫ F p ·`
  (`cfc_log_eq_integral_Ioi_resolvent`, used to identify the differentiated function via
  `HasDerivAt.congr_of_eventuallyEq`);
* `a + p • b + s • 1` is a unit (`s > 0`), giving the pointwise `p`-derivative of `F` from
  `HasDerivAt.ringInverse`;
* `‖F' p s‖ ≤ ‖b‖ (m + s)⁻²` uniformly in `p`, via the resolvent norm bound
  `CStarAlgebra.norm_ringInverse_le_of_algebraMap_le`
  (`(algebraMap ℝ A) (m + s) ≤ a + p • b + s • 1`) and submultiplicativity, dominated by the
  integrable `integrableOn_Ioi_inv_add_sq`.

## Main results

* `exists_forall_mem_ball_algebraMap_le_add_smul` — a local uniform positive lower bound on an
  affine line of self-adjoint perturbations of a strictly positive element.
* `eventually_isStrictlyPositive_add_smul` — the affine line `p ↦ a + p • b` stays strictly
  positive on a neighbourhood of any point where it is (the strict-positivity corollary of the
  previous lemma).
* `hasDerivAt_cfc_log_add_smul` — the parametric derivative of the operator logarithm along the
  affine line.

This is the differentiation step of the second-derivative proof of concavity of the von Neumann
entropy (Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 11.22): with
`b = ρ - σ` and `a + p • b = p ρ + (1 - p) σ` the mixing line, it supplies
`d/dp cfc Real.log ω_p = ∫₀^∞ (ω_p + s)⁻¹ (ρ - σ) (ω_p + s)⁻¹ ds`.
-/

@[expose] public section

open MeasureTheory Set

/-- **Local uniform lower bound along an affine line of self-adjoint perturbations.** If
`a + p₀ • b` is strictly positive and `b` is self-adjoint, then there are `m > 0` and `ε > 0` such
that `(algebraMap ℝ A) m ≤ a + p • b` for every `p` in the ball of radius `ε` about `p₀`. Since
`a + p • b = (a + p₀ • b) + (p - p₀) • b`, a positive lower bound `m₀` on `a + p₀ • b`
(`CFC.exists_pos_algebraMap_le_iff`) is preserved up to the perturbation
`(p - p₀) • b ≥ -(algebraMap ℝ A) ‖(p - p₀) • b‖` (`IsSelfAdjoint.neg_algebraMap_norm_le_self`);
for `|p - p₀|` small enough (`ε = m₀ / (2 (‖b‖ + 1))`) the perturbation is `≤ m₀ / 2` in norm,
leaving the uniform lower bound `m = m₀ / 2`. -/
theorem exists_forall_mem_ball_algebraMap_le_add_smul
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    {a b : A} {p₀ : ℝ} (h : IsStrictlyPositive (a + p₀ • b)) (hb : IsSelfAdjoint b) :
    ∃ m > 0, ∃ ε > 0, ∀ p ∈ Metric.ball p₀ ε, (algebraMap ℝ A) m ≤ a + p • b := by
  obtain ⟨m, hm, hmle⟩ : ∃ m > 0, (algebraMap ℝ A) m ≤ a + p₀ • b :=
    (CFC.exists_pos_algebraMap_le_iff (a := a + p₀ • b)).mpr
      (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp h).2
  refine ⟨m / 2, by positivity, m / (2 * (‖b‖ + 1)), by positivity, ?_⟩
  intro p hp
  rw [Metric.mem_ball, Real.dist_eq] at hp
  have hsa : IsSelfAdjoint ((p - p₀) • b) := (IsSelfAdjoint.all (p - p₀)).smul hb
  have hb0 : (0 : ℝ) ≤ ‖b‖ := norm_nonneg b
  have hnb : ‖(p - p₀) • b‖ ≤ m / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    refine (mul_le_mul_of_nonneg_right hp.le hb0).trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (‖b‖ + 1))]
    nlinarith [hb0, hm.le]
  calc (algebraMap ℝ A) (m / 2)
      ≤ (algebraMap ℝ A) (m - ‖(p - p₀) • b‖) := algebraMap_mono A (by linarith)
    _ = (algebraMap ℝ A) m - (algebraMap ℝ A) ‖(p - p₀) • b‖ := map_sub _ _ _
    _ ≤ (a + p₀ • b) + (p - p₀) • b := by
        rw [sub_eq_add_neg]; exact add_le_add hmle hsa.neg_algebraMap_norm_le_self
    _ = a + p • b := by rw [sub_smul]; abel

/-- **Local strict positivity along an affine line.** If `a + p₀ • b` is strictly positive and `b`
is self-adjoint in a C⋆-algebra, then `a + p • b` is strictly positive for every `p` in a
neighbourhood of `p₀`. Immediate from the local uniform lower bound
`exists_forall_mem_ball_algebraMap_le_add_smul`: on the ball,
`a + p • b = (algebraMap ℝ A) m + ((a + p • b) - (algebraMap ℝ A) m)` is the sum of a strictly
positive and a non-negative element. -/
theorem eventually_isStrictlyPositive_add_smul
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    {a b : A} {p₀ : ℝ} (h : IsStrictlyPositive (a + p₀ • b)) (hb : IsSelfAdjoint b) :
    ∀ᶠ p in nhds p₀, IsStrictlyPositive (a + p • b) := by
  obtain ⟨m, hm, ε, hε, hlb⟩ := exists_forall_mem_ball_algebraMap_le_add_smul h hb
  filter_upwards [Metric.ball_mem_nhds p₀ hε] with p hp
  have key : (algebraMap ℝ A) m + ((a + p • b) - (algebraMap ℝ A) m) = a + p • b := by abel
  rw [← key]
  exact (isStrictlyPositive_algebraMap hm).add_nonneg (sub_nonneg.mpr (hlb p hp))

/-- **Parametric derivative of the operator logarithm along an affine line.** For `b` self-adjoint
and `a + p₀ • b` strictly positive in a C⋆-algebra, `p ↦ cfc Real.log (a + p • b)` is differentiable
at `p₀` with derivative

`∫₀^∞ Ring.inverse (a + p₀ • b + s • 1) * b * Ring.inverse (a + p₀ • b + s • 1) ds`.

This differentiates the integral representation
`cfc Real.log (a + p • b) = ∫₀^∞ ((1 + s)⁻¹ • 1 - Ring.inverse (a + p • b + s • 1)) ds`
(`cfc_log_eq_integral_Ioi_resolvent`) under the integral sign: the resolvent term has derivative
`-(a + p • b + s • 1)⁻¹ b (a + p • b + s • 1)⁻¹` (`hasDerivAt_ringInverse_add_smul`, the direction
of the affine line being `b`), whose negation is the sandwich in the conclusion; the differentiation
is
justified by `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the uniform dominating function
`‖b‖ (m + s)⁻²`. See the module docstring. -/
theorem hasDerivAt_cfc_log_add_smul
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    {a b : A} (hb : IsSelfAdjoint b) {p₀ : ℝ} (h : IsStrictlyPositive (a + p₀ • b)) :
    HasDerivAt (fun p : ℝ => cfc Real.log (a + p • b))
      (∫ s in Set.Ioi (0 : ℝ),
        Ring.inverse (a + p₀ • b + s • 1) * b * Ring.inverse (a + p₀ • b + s • 1)) p₀ := by
  obtain ⟨m, hm, ε, hε, hlb⟩ := exists_forall_mem_ball_algebraMap_le_add_smul h hb
  -- On the ball `a + p • b` is strictly positive, so `a + p • b + s • 1` is a unit for `s > 0`.
  have hstrict : ∀ p ∈ Metric.ball p₀ ε, IsStrictlyPositive (a + p • b) := by
    intro p hp
    have key : (algebraMap ℝ A) m + ((a + p • b) - (algebraMap ℝ A) m) = a + p • b := by abel
    rw [← key]
    exact (isStrictlyPositive_algebraMap hm).add_nonneg (sub_nonneg.mpr (hlb p hp))
  have hunit : ∀ p ∈ Metric.ball p₀ ε, ∀ s : ℝ, 0 < s → IsUnit (a + p • b + s • (1 : A)) := by
    intro p hp s hs
    exact ((hstrict p hp).add_nonneg (smul_nonneg hs.le zero_le_one)).isUnit
  -- Continuity (hence a.e.-measurability) of the resolvent, the integrand and its derivative.
  have hres : ∀ p ∈ Metric.ball p₀ ε,
      ContinuousOn (fun s : ℝ => Ring.inverse (a + p • b + s • (1 : A))) (Ioi (0 : ℝ)) := by
    intro p hp s hs
    simp only [mem_Ioi] at hs
    exact (hasDerivAt_ringInverse_add_smul (hunit p hp s hs)).continuousAt.continuousWithinAt
  have hFcont : ∀ p ∈ Metric.ball p₀ ε, ContinuousOn
      (fun s : ℝ => (1 + s)⁻¹ • (1 : A) - Ring.inverse (a + p • b + s • 1)) (Ioi (0 : ℝ)) := by
    intro p hp
    refine ContinuousOn.sub ?_ (hres p hp)
    have hinv : ContinuousOn (fun s : ℝ => (1 + s)⁻¹) (Ioi 0) := by
      refine ContinuousOn.inv₀ (by fun_prop) ?_
      intro s hs; simp only [mem_Ioi] at hs; positivity
    exact hinv.smul continuousOn_const
  have hF'cont : ∀ p ∈ Metric.ball p₀ ε, ContinuousOn
      (fun s : ℝ => Ring.inverse (a + p • b + s • (1 : A)) * b
        * Ring.inverse (a + p • b + s • 1)) (Ioi (0 : ℝ)) :=
    fun p hp => ((hres p hp).mul continuousOn_const).mul (hres p hp)
  -- Differentiate the integral representation under the integral sign.
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (bound := fun s => ‖b‖ * (m + s)⁻¹ ^ 2)
    (F := fun p s => (1 + s)⁻¹ • (1 : A) - Ring.inverse (a + p • b + s • 1))
    (F' := fun p s => Ring.inverse (a + p • b + s • 1) * b * Ring.inverse (a + p • b + s • 1))
    (x₀ := p₀) (s := Metric.ball p₀ ε)
    (Metric.ball_mem_nhds p₀ hε)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds p₀ hε)
      (fun p hp => (hFcont p hp).aestronglyMeasurable (μ := volume) measurableSet_Ioi))
    (integrableOn_Ioi_inv_smul_one_sub_ringInverse h)
    ((hF'cont p₀ (Metric.mem_ball_self hε)).aestronglyMeasurable (μ := volume) measurableSet_Ioi)
    (by
      -- Uniform (in `p`) domination of the derivative integrand by `‖b‖ (m + s)⁻²`.
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun s hs => ?_)
      simp only [mem_Ioi] at hs
      intro p hp
      have hle : (algebraMap ℝ A) (m + s) ≤ a + p • b + s • (1 : A) := by
        rw [map_add, Algebra.algebraMap_eq_smul_one s]
        gcongr
        exact hlb p hp
      have hres_norm : ‖Ring.inverse (a + p • b + s • (1 : A))‖ ≤ (m + s)⁻¹ :=
        CStarAlgebra.norm_ringInverse_le_of_algebraMap_le (by linarith) hle
      calc ‖Ring.inverse (a + p • b + s • (1 : A)) * b * Ring.inverse (a + p • b + s • 1)‖
          ≤ ‖Ring.inverse (a + p • b + s • (1 : A)) * b‖ * ‖Ring.inverse (a + p • b + s • 1)‖ :=
            norm_mul_le _ _
        _ ≤ (‖Ring.inverse (a + p • b + s • (1 : A))‖ * ‖b‖)
              * ‖Ring.inverse (a + p • b + s • 1)‖ := by gcongr; exact norm_mul_le _ _
        _ ≤ ((m + s)⁻¹ * ‖b‖) * (m + s)⁻¹ := by gcongr
        _ = ‖b‖ * (m + s)⁻¹ ^ 2 := by ring)
    ((integrableOn_Ioi_inv_add_sq hm).const_mul ‖b‖)
    (by
      -- The pointwise `p`-derivative of the integrand, for every `p` in the ball.
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun s hs => ?_)
      simp only [mem_Ioi] at hs
      intro p hp
      have hu := hunit p hp s hs
      have hg : HasDerivAt (fun p : ℝ => a + p • b + s • (1 : A)) b p := by
        simpa using (((hasDerivAt_id p).smul_const b).const_add a).add_const (s • 1)
      have hinv : Ring.inverse (a + p • b + s • (1 : A)) = ↑hu.unit⁻¹ := by
        conv_lhs => rw [← hu.unit_spec]
        rw [Ring.inverse_unit]
      have hF := (hasDerivAt_const p ((1 + s)⁻¹ • (1 : A))).fun_sub (hg.ringInverse hu)
      simp only [zero_sub, neg_neg] at hF
      simpa only [hinv] using hF)
  -- On the ball the differentiated function is `cfc Real.log (a + p • b)`.
  refine key.2.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds p₀ hε] with p hp
  exact cfc_log_eq_integral_Ioi_resolvent (hstrict p hp)
