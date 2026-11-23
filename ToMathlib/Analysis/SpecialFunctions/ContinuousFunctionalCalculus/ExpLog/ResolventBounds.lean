/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.Calculus.Deriv.RingInverse
public import ToMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Resolvent norm bound and integrability of the operator-logarithm integrand

This file collects two analytic estimates for the resolvent `Ring.inverse (a + s • 1)` of a strictly
positive element `a` of a C⋆-algebra, needed to differentiate the operator-logarithm integral
representation `cfc Real.log a = ∫₀^∞ ((1 + s)⁻¹ • 1 - Ring.inverse (a + s • 1)) ds`
(`cfc_log_eq_integral_Ioi_resolvent`) along a parameter, and hence for the second-derivative
proof of concavity of the von Neumann entropy (Nielsen & Chuang, *Quantum Computation and
Quantum Information*, Exercise 11.22).

* `CStarAlgebra.norm_ringInverse_le_of_algebraMap_le` — the **resolvent norm bound**: if
  `(algebraMap ℝ A) m ≤ a` with `0 < m` (a positive lower bound on the spectrum), then
  `‖Ring.inverse a‖ ≤ m⁻¹`. Applied to `a + s • 1` (whose lower bound is `m + s`) it controls the
  resolvent uniformly in `s`, and it is the elementary bound underlying the domination hypothesis of
  the differentiation-under-the-integral step.
* `integrableOn_Ioi_inv_smul_one_sub_ringInverse` — **integrability of the operator-log integrand**:
  for `a` strictly positive the map `s ↦ (1 + s)⁻¹ • 1 - Ring.inverse (a + s • 1)` is integrable on
  `(0, ∞)`. Although neither term is individually integrable, the difference telescopes: writing
  `u = a + s • 1`, one has the algebraic identity
  `(1 + s)⁻¹ • 1 - u⁻¹ = (1 + s)⁻¹ • (u⁻¹ * (a - 1))`, so the norm is bounded by
  `‖a - 1‖ · (1 + s)⁻¹ (m + s)⁻¹ ≤ ‖a - 1‖ · (min 1 m + s)⁻²`, which decays like `s⁻²` and is
  integrable. This is exactly the hypothesis `Integrable (F p₀)` that the parametric-integral
  derivative lemma requires of the base-point integrand.

The scalar helper `integrableOn_Ioi_inv_add_sq` (`s ↦ (c + s)⁻²` is integrable on `(0, ∞)` for
`0 < c`) supplies the dominating function.

## Main results

* `integrableOn_Ioi_inv_add_sq`
* `CStarAlgebra.norm_ringInverse_le_of_algebraMap_le`
* `integrableOn_Ioi_inv_smul_one_sub_ringInverse`
-/

@[expose] public section

open MeasureTheory Set

/-- The function `s ↦ (c + s)⁻²` is integrable on `(0, ∞)` for `0 < c`: it is the derivative of the
bounded, monotone antiderivative `s ↦ -(c + s)⁻¹` (increasing from `-c⁻¹` to `0`). -/
theorem integrableOn_Ioi_inv_add_sq {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s => (c + s)⁻¹ ^ 2) (Ioi 0) := by
  have hcont : ContinuousWithinAt (fun s => -(c + s)⁻¹) (Ici 0) 0 :=
    (ContinuousWithinAt.inv₀ (by fun_prop) (by simpa using hc.ne')).neg
  have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt (fun t => -(c + t)⁻¹) ((c + s)⁻¹ ^ 2) s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hne : c + s ≠ 0 := by positivity
    have e : HasDerivAt (fun t : ℝ => c + t) 1 s := by simpa using (hasDerivAt_id s).const_add c
    convert (e.inv hne).neg using 1
    rw [neg_div, neg_neg, one_div, inv_pow]
  have htend : Filter.Tendsto (fun s => -(c + s)⁻¹) Filter.atTop (nhds 0) := by
    rw [show (0 : ℝ) = -0 by ring]
    exact (Filter.Tendsto.inv_tendsto_atTop
      (Filter.tendsto_atTop_add_const_left _ c Filter.tendsto_id)).neg
  exact integrableOn_Ioi_deriv_of_nonneg hcont hderiv (fun s _ => sq_nonneg _) htend

namespace CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

/-- **Resolvent norm bound.** If `a` dominates the scalar `(algebraMap ℝ A) m` with `0 < m` (so `m`
is a positive lower bound on the spectrum of `a`), then `‖Ring.inverse a‖ ≤ m⁻¹`. Proof:
`Ring.inverse` is order-reversing on strictly positive elements
(`CStarAlgebra.ringInverse_le_ringInverse`), so `Ring.inverse a ≤ Ring.inverse (algebraMap ℝ A m)
= m⁻¹ • 1`, and the C⋆-norm is monotone on nonnegative elements. -/
theorem norm_ringInverse_le_of_algebraMap_le {a : A} {m : ℝ} (hm : 0 < m)
    (h : (algebraMap ℝ A) m ≤ a) : ‖Ring.inverse a‖ ≤ m⁻¹ := by
  have hmsp : IsStrictlyPositive ((algebraMap ℝ A) m) := by
    rw [Algebra.algebraMap_eq_smul_one]
    simpa using isStrictlyPositive_add_smul_one (a := (0 : A)) le_rfl hm
  have hasp : IsStrictlyPositive a := by
    have key : (algebraMap ℝ A) m + (a - (algebraMap ℝ A) m) = a := by abel
    rw [← key]; exact hmsp.add_nonneg (sub_nonneg.mpr h)
  have hle : Ring.inverse a ≤ Ring.inverse ((algebraMap ℝ A) m) :=
    CStarAlgebra.ringInverse_le_ringInverse h
  have hu : IsUnit ((algebraMap ℝ A) m) := hmsp.isUnit
  have hval : Ring.inverse ((algebraMap ℝ A) m) = m⁻¹ • (1 : A) := by
    have h1 : ((algebraMap ℝ A) m) * (m⁻¹ • (1 : A)) = 1 := by
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hm.ne',
        one_smul]
    calc Ring.inverse ((algebraMap ℝ A) m)
        = Ring.inverse ((algebraMap ℝ A) m) * (((algebraMap ℝ A) m) * (m⁻¹ • (1 : A))) := by
          rw [h1, mul_one]
      _ = (Ring.inverse ((algebraMap ℝ A) m) * ((algebraMap ℝ A) m)) * (m⁻¹ • (1 : A)) := by
          rw [mul_assoc]
      _ = m⁻¹ • (1 : A) := by rw [Ring.inverse_mul_cancel _ hu, one_mul]
  have h0 : (0 : A) ≤ Ring.inverse a := hasp.ringInverse.nonneg
  calc ‖Ring.inverse a‖ ≤ ‖Ring.inverse ((algebraMap ℝ A) m)‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg (a := Ring.inverse a) hle h0
    _ = m⁻¹ := by
        rw [hval, norm_smul, norm_one, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]

end CStarAlgebra

/-- **Integrability of the operator-logarithm integrand.** For a strictly positive element `a` of a
C⋆-algebra the map `s ↦ (1 + s)⁻¹ • 1 - Ring.inverse (a + s • 1)` is integrable on `(0, ∞)`. This is
the integrand of the integral representation `cfc_log_eq_integral_Ioi_resolvent`, and is the
`Integrable`-of-the-base-point hypothesis needed to differentiate that representation under the
integral sign. The two terms are individually non-integrable, but with `u = a + s • 1` the
telescoping identity `(1 + s)⁻¹ • 1 - u⁻¹ = (1 + s)⁻¹ • (u⁻¹ * (a - 1))` and the resolvent norm
bound `‖u⁻¹‖ ≤ (m + s)⁻¹` (where `(algebraMap ℝ A) m ≤ a`) give
`‖·‖ ≤ ‖a - 1‖ · (1 + s)⁻¹ (m + s)⁻¹ ≤ ‖a - 1‖ · (min 1 m + s)⁻²`, an integrable dominating
function. -/
theorem integrableOn_Ioi_inv_smul_one_sub_ringInverse
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A] {a : A}
    (ha : IsStrictlyPositive a) :
    IntegrableOn (fun s : ℝ => (1 + s)⁻¹ • (1 : A) - Ring.inverse (a + s • 1)) (Ioi 0) := by
  -- A positive lower bound `m` on the spectrum of `a`.
  obtain ⟨m, hm, hma⟩ : ∃ m, 0 < m ∧ (algebraMap ℝ A) m ≤ a := by
    obtain ⟨m, hm0, hle⟩ := (CFC.exists_pos_algebraMap_le_iff (a := a)).mpr
      (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp ha).2
    exact ⟨m, hm0, hle⟩
  have hcpos : 0 < min 1 m := lt_min one_pos hm
  -- The integrand is continuous on `(0, ∞)`, hence a.e. strongly measurable.
  have hcont : ContinuousOn
      (fun s : ℝ => (1 + s)⁻¹ • (1 : A) - Ring.inverse (a + s • 1)) (Ioi 0) := by
    refine ContinuousOn.sub ?_ ?_
    · have hinv : ContinuousOn (fun s : ℝ => (1 + s)⁻¹) (Ioi 0) := by
        refine ContinuousOn.inv₀ (by fun_prop) ?_
        intro s hs; simp only [mem_Ioi] at hs; positivity
      exact hinv.smul continuousOn_const
    · intro s hs
      simp only [mem_Ioi] at hs
      have hunit : IsUnit (a + s • (1 : A)) :=
        (ha.add_nonneg (smul_nonneg hs.le zero_le_one)).isUnit
      exact (hasDerivAt_ringInverse_add_smul hunit).continuousAt.continuousWithinAt
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => (1 + s)⁻¹ • (1 : A) - Ring.inverse (a + s • 1)) (volume.restrict (Ioi 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  -- The dominating function `‖a - 1‖ · (min 1 m + s)⁻²`.
  have hbound_int : IntegrableOn (fun s : ℝ => ‖a - 1‖ * (min 1 m + s)⁻¹ ^ 2) (Ioi 0) :=
    (integrableOn_Ioi_inv_add_sq hcpos).const_mul ‖a - 1‖
  refine hbound_int.mono' hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ ?_)
  intro s hs
  simp only [mem_Ioi] at hs
  -- Pointwise domination via the telescoping identity and the resolvent norm bound.
  have hunit : IsUnit (a + s • (1 : A)) := (ha.add_nonneg (smul_nonneg hs.le zero_le_one)).isUnit
  have hiu : Ring.inverse (a + s • (1 : A)) * (a + s • (1 : A)) = 1 :=
    Ring.inverse_mul_cancel _ hunit
  have hs1 : (1 : ℝ) + s ≠ 0 := by positivity
  have hia : Ring.inverse (a + s • (1 : A)) * a = 1 - s • Ring.inverse (a + s • (1 : A)) := by
    have expand : a = (a + s • (1 : A)) - s • (1 : A) := by abel
    calc Ring.inverse (a + s • (1 : A)) * a
        = Ring.inverse (a + s • (1 : A)) * ((a + s • (1 : A)) - s • (1 : A)) := by rw [← expand]
      _ = Ring.inverse (a + s • (1 : A)) * (a + s • (1 : A))
            - Ring.inverse (a + s • (1 : A)) * (s • (1 : A)) := by rw [mul_sub]
      _ = 1 - s • Ring.inverse (a + s • (1 : A)) := by rw [hiu, mul_smul_comm, mul_one]
  have hia1 : Ring.inverse (a + s • (1 : A)) * (a - 1)
      = 1 - (1 + s) • Ring.inverse (a + s • (1 : A)) := by
    rw [mul_sub, hia, mul_one, add_smul, one_smul]; abel
  have hid : (1 + s)⁻¹ • (1 : A) - Ring.inverse (a + s • 1)
      = (1 + s)⁻¹ • (Ring.inverse (a + s • 1) * (a - 1)) := by
    rw [hia1, smul_sub, smul_smul, inv_mul_cancel₀ hs1, one_smul]
  have hres : ‖Ring.inverse (a + s • (1 : A))‖ ≤ (m + s)⁻¹ := by
    apply CStarAlgebra.norm_ringInverse_le_of_algebraMap_le (m := m + s) (by linarith)
    rw [map_add, Algebra.algebraMap_eq_smul_one (R := ℝ) (A := A) s]
    gcongr
  have hcm0 : min 1 m ≤ m := min_le_right 1 m
  have hc10 : min 1 m ≤ 1 := min_le_left 1 m
  have hcs : 0 < min 1 m + s := by linarith
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (1 + s)⁻¹)]
  have e1 : (1 + s)⁻¹ ≤ (min 1 m + s)⁻¹ := (inv_le_inv₀ (by positivity) hcs).mpr (by linarith)
  have e2 : (m + s)⁻¹ ≤ (min 1 m + s)⁻¹ := (inv_le_inv₀ (by positivity) hcs).mpr (by linarith)
  calc (1 + s)⁻¹ * ‖Ring.inverse (a + s • 1) * (a - 1)‖
      ≤ (1 + s)⁻¹ * ((m + s)⁻¹ * ‖a - 1‖) := by
        gcongr
        exact (norm_mul_le _ _).trans (by gcongr)
    _ = ‖a - 1‖ * ((1 + s)⁻¹ * (m + s)⁻¹) := by ring
    _ ≤ ‖a - 1‖ * (min 1 m + s)⁻¹ ^ 2 := by
        gcongr
        calc (1 + s)⁻¹ * (m + s)⁻¹
            ≤ (min 1 m + s)⁻¹ * (min 1 m + s)⁻¹ :=
              mul_le_mul e1 e2 (by positivity) (by positivity)
          _ = (min 1 m + s)⁻¹ ^ 2 := (sq _).symm
