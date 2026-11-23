/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The improper integral `∫ sin²x / x² = π`

This file evaluates the absolutely convergent improper integral of `(1 - cos x)/x²`
(hence of `sin²x/x²`) over the real line.

* `Real.integral_Ioi_one_sub_cos_div_sq` : `∫ x in Ioi 0, (1 - cos x)/x² = π/2`
* `Real.integral_one_sub_cos_div_sq` : `∫ x, (1 - cos x)/x² = π`

The proof avoids the (only conditionally convergent) Dirichlet integral `∫ sin x / x`.
It uses the absolutely convergent representation
`(1 - cos x)/x² = ∫₀^∞ (1 - cos x) · t · e^{-x t} dt` (from the moment
`∫₀^∞ t · e^{-x t} dt = 1/x²`) and a nonnegative Tonelli swap, after which
the inner integral is a Laplace transform
(`∫₀^∞ e^{-t x} dx = 1/t`, `∫₀^∞ e^{-t x} cos x dx = t/(t²+1)`) and the outer integral
is `∫₀^∞ 1/(t²+1) dt = π/2`.
-/

public section

open MeasureTheory Real Set intervalIntegral

namespace Real

/-- `∫₀^∞ t · e^{-(x t)} dt = 1/x²` for `x > 0` — the `a = 2` instance of the
scaled `Γ`-moment `Real.integral_rpow_mul_exp_neg_mul_Ioi`. -/
theorem integral_Ioi_id_mul_exp_neg {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0:ℝ), t * Real.exp (-(x * t)) = 1 / x ^ 2 := by
  have hΓ : Real.Gamma 2 = 1 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one]; ring
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := x) (by norm_num) hx
  rw [hΓ, mul_one, show ((2:ℝ) - 1) = 1 by norm_num] at h
  simp only [Real.rpow_one] at h
  rw [h, Real.rpow_two, div_pow, one_pow]

/-- Laplace transform of `1`: `∫₀^∞ e^{-(x t)} dx = 1/t` for `t > 0` — the `a = 1`
instance of the scaled `Γ`-moment `Real.integral_rpow_mul_exp_neg_mul_Ioi`. -/
theorem integral_Ioi_exp_neg_mul {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi (0:ℝ), Real.exp (-(x * t)) = 1 / t := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := t) (by norm_num) ht
  rw [Real.Gamma_one, mul_one, Real.rpow_one, show ((1:ℝ) - 1) = 0 by norm_num] at h
  simp only [Real.rpow_zero, one_mul] at h
  rw [← h]
  exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by rw [mul_comm]

/-- Laplace transform of cosine: `∫₀^∞ e^{-(x t)} cos x dx = t/(t²+1)` for `t > 0`. -/
theorem integral_Ioi_cos_mul_exp_neg {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi (0:ℝ), Real.cos x * Real.exp (-(x * t)) = t / (t ^ 2 + 1) := by
  have hint : IntegrableOn (fun x : ℝ => Complex.exp (((-t : ℂ) + Complex.I) * x)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_complex_Ioi (a := (-t : ℂ) + Complex.I) (by simp [ht]) 0
  have hcomplex := integral_exp_mul_complex_Ioi (a := (-t : ℂ) + Complex.I) (by simp [ht]) 0
  have hre : (∫ x in Ioi (0:ℝ), Complex.exp (((-t : ℂ) + Complex.I) * x)).re
      = ∫ x in Ioi (0:ℝ), (Complex.exp (((-t : ℂ) + Complex.I) * x)).re := by
    simp only [← Complex.reCLM_apply]
    exact (ContinuousLinearMap.integral_comp_comm Complex.reCLM hint).symm
  have hpt : ∀ x : ℝ, (Complex.exp (((-t : ℂ) + Complex.I) * x)).re
      = Real.cos x * Real.exp (-(x * t)) := by
    intro x
    have h : ((-t : ℂ) + Complex.I) * x = ((-t * x : ℝ) : ℂ) + (x : ℝ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.exp_add, ← Complex.ofReal_exp, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
    rw [show -t * x = -(x * t) by ring]; ring
  simp only [hpt] at hre
  rw [← hre, hcomplex]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show ((-t:ℂ) + Complex.I) = -((t:ℂ) - Complex.I) by ring, neg_div_neg_eq, Complex.div_re]
  simp [Complex.normSq]
  ring

/-- `x ↦ e^{-(x t)}` is integrable on `(0, ∞)` for `t > 0`. -/
theorem integrableOn_exp_neg_mul {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x => Real.exp (-(x * t))) (Ioi 0) := by
  have := integrableOn_exp_mul_Ioi (a := -t) (by linarith) 0
  simpa only [show ∀ x : ℝ, -t * x = -(x * t) from fun x => by ring] using this

/-- `t ↦ t · e^{-(x t)}` is integrable on `(0, ∞)` for `x > 0` — the `s = 1, p = 1`
instance of `integrableOn_rpow_mul_exp_neg_mul_rpow`. -/
theorem integrableOn_id_mul_exp_neg {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => t * Real.exp (-(x * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := x)
    (by norm_num) one_pos hx
  simpa only [Real.rpow_one, neg_mul] using h

/-- `x ↦ f x · e^{-(x t)}` is integrable on `(0, ∞)` for `t > 0` if `‖f‖ ≤ C`. -/
private theorem integrableOn_bdd_mul_exp_neg {t C : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf : Continuous f) (hb : ∀ x, |f x| ≤ C) :
    IntegrableOn (fun x => f x * Real.exp (-(x * t))) (Ioi 0) := by
  have hexp := integrableOn_exp_neg_mul ht
  apply Integrable.mono' (g := fun x => C * Real.exp (-(x * t))) (hexp.const_mul C)
  · exact (hf.mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_right (hb x) (Real.exp_nonneg _)

/-- `∫₀^∞ (1 - cos x)/x² dx = π/2`, by a nonnegative Tonelli swap of the Laplace
representation `(1 - cos x)/x² = ∫₀^∞ (1 - cos x) · t · e^{-x t} dt`. -/
theorem integral_Ioi_one_sub_cos_div_sq :
    ∫ x in Ioi (0:ℝ), (1 - Real.cos x) / x ^ 2 = Real.pi / 2 := by
  set F : ℝ → ℝ → ℝ := fun x t => (1 - Real.cos x) * (t * Real.exp (-(x * t))) with hFdef
  have hFnn : ∀ x, 0 < x → ∀ t, 0 < t → 0 ≤ F x t := by
    intro x hx t ht
    have h1 : (0:ℝ) ≤ 1 - Real.cos x := by nlinarith [Real.cos_le_one x]
    simp only [hFdef]; positivity
  have hFint_x : ∀ x, 0 < x → IntegrableOn (fun t => F x t) (Ioi 0) := fun x hx => by
    have h : IntegrableOn (fun t => (1 - Real.cos x) * (t * Real.exp (-(x * t)))) (Ioi 0) :=
      (integrableOn_id_mul_exp_neg hx).const_mul (1 - Real.cos x)
    simpa only [hFdef] using h
  have hFint_t : ∀ t, 0 < t → IntegrableOn (fun x => F x t) (Ioi 0) := by
    intro t ht
    have hrw : (fun x => F x t) = (fun x => (1 - Real.cos x) * t * Real.exp (-(x * t))) := by
      funext x; simp only [hFdef]; ring
    rw [hrw]
    refine integrableOn_bdd_mul_exp_neg ht (C := 2 * t) (by fun_prop) (fun x => ?_)
    rw [abs_mul, abs_of_pos ht]
    have h2 : |1 - Real.cos x| ≤ 2 := by
      rw [abs_le]; constructor <;> nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x]
    nlinarith [h2, ht.le]
  have hrep : ∀ x ∈ Ioi (0:ℝ), (∫ t in Ioi (0:ℝ), F x t) = (1 - Real.cos x) / x ^ 2 := by
    intro x hx; simp only [mem_Ioi] at hx
    simp only [hFdef]
    rw [MeasureTheory.integral_const_mul, integral_Ioi_id_mul_exp_neg hx, mul_one_div]
  have hexp : ∀ t : ℝ, 0 < t → IntegrableOn (fun x => Real.exp (-(x * t))) (Ioi 0) :=
    fun t ht => integrableOn_exp_neg_mul ht
  have hinner : ∀ t ∈ Ioi (0:ℝ), (∫ x in Ioi (0:ℝ), F x t) = 1 / (t ^ 2 + 1) := by
    intro t ht; simp only [mem_Ioi] at ht
    have hrw : (fun x => F x t)
        = (fun x => t * (Real.exp (-(x * t)) - Real.cos x * Real.exp (-(x * t)))) := by
      funext x; simp only [hFdef]; ring
    rw [hrw, MeasureTheory.integral_const_mul,
      integral_sub (hexp t ht)
        (integrableOn_bdd_mul_exp_neg ht Real.continuous_cos (fun x => Real.abs_cos_le_one x)),
      integral_Ioi_exp_neg_mul ht, integral_Ioi_cos_mul_exp_neg ht]
    have ht2 : t ^ 2 + 1 ≠ 0 := by positivity
    field_simp
    ring
  -- assemble
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] fun x => (1 - Real.cos x) / x ^ 2 := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    simp only [mem_Ioi] at hx
    have : (0:ℝ) ≤ 1 - Real.cos x := by nlinarith [Real.cos_le_one x]
    positivity
  have haesm : AEStronglyMeasurable (fun x => (1 - Real.cos x) / x ^ 2)
      (volume.restrict (Ioi (0:ℝ))) := (by fun_prop : Measurable _).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hnn haesm]
  have hA : ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal ((1 - Real.cos x) / x ^ 2)
      = ∫⁻ x in Ioi (0:ℝ), ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (F x t) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro x hx; simp only [mem_Ioi] at hx
    change ENNReal.ofReal ((1 - Real.cos x) / x ^ 2)
      = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (F x t)
    rw [← hrep x (mem_Ioi.mpr hx),
      ofReal_integral_eq_lintegral_ofReal (hFint_x x hx) ?_]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact hFnn x hx t (mem_Ioi.mp ht)
  rw [hA, lintegral_lintegral_swap (by
    apply Measurable.aemeasurable
    simp only [hFdef]
    fun_prop)]
  have hB : ∫⁻ t in Ioi (0:ℝ), ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (F x t)
      = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (t ^ 2 + 1)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht; simp only [mem_Ioi] at ht
    change ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (F x t) = ENNReal.ofReal (1 / (t ^ 2 + 1))
    rw [← ofReal_integral_eq_lintegral_ofReal (hFint_t t ht) ?_, hinner t (mem_Ioi.mpr ht)]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact hFnn x (mem_Ioi.mp hx) t ht
  rw [hB]
  have hcast : (fun t : ℝ => (1:ℝ) / (t ^ 2 + 1)) = fun t => (1 + t ^ 2)⁻¹ := by
    funext t; rw [one_div, add_comm]
  have houter : (∫ t in Ioi (0:ℝ), 1 / (t ^ 2 + 1)) = Real.pi / 2 := by
    rw [hcast, integral_Ioi_inv_one_add_sq, Real.arctan_zero]; ring
  rw [← ofReal_integral_eq_lintegral_ofReal ?_ ?_, houter, ENNReal.toReal_ofReal (by positivity)]
  · rw [hcast]
    exact integrable_inv_one_add_sq.integrableOn
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t _
    positivity

/-- `∫_ℝ (1 - cos x)/x² dx = π` (even integrand, twice the half-line integral). -/
theorem integral_one_sub_cos_div_sq : ∫ x : ℝ, (1 - Real.cos x) / x ^ 2 = Real.pi := by
  have he : (fun x : ℝ => (1 - Real.cos x) / x ^ 2)
      = (fun x : ℝ => (1 - Real.cos |x|) / |x| ^ 2) := by
    funext x; rw [Real.cos_abs, sq_abs]
  rw [he, integral_comp_abs (f := fun y => (1 - Real.cos y) / y ^ 2),
    integral_Ioi_one_sub_cos_div_sq]
  ring

/-- `∫_ℝ (1 - cos (c x))/x² dx = π |c|` (change of variables from the `c = 1` case). -/
theorem integral_one_sub_cos_mul_div_sq (c : ℝ) :
    ∫ x : ℝ, (1 - Real.cos (c * x)) / x ^ 2 = Real.pi * |c| := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hcabs : |c| ≠ 0 := abs_ne_zero.mpr hc
    have hg : (fun x : ℝ => (1 - Real.cos (c * x)) / x ^ 2)
        = (fun x => c ^ 2 * ((fun u => (1 - Real.cos u) / u ^ 2) (c * x))) := by
      funext x
      rcases eq_or_ne x 0 with rfl | hx0
      · simp
      · simp only; rw [mul_pow]; field_simp
    rw [hg, MeasureTheory.integral_const_mul,
      MeasureTheory.Measure.integral_comp_mul_left (fun u => (1 - Real.cos u) / u ^ 2) c,
      integral_one_sub_cos_div_sq, smul_eq_mul, abs_inv, ← sq_abs c]
    field_simp

/-- `∫_ℝ sin²(b x)/x² dx = π |b|` — the scaled sinc² integral. -/
theorem integral_sin_sq_mul_div_sq (b : ℝ) :
    ∫ x : ℝ, Real.sin (b * x) ^ 2 / x ^ 2 = Real.pi * |b| := by
  have hs : (fun x : ℝ => Real.sin (b * x) ^ 2 / x ^ 2)
      = (fun x => (1 / 2) * ((1 - Real.cos (2 * b * x)) / x ^ 2)) := by
    funext x
    have hnum : Real.sin (b * x) ^ 2 = (1 - Real.cos (2 * b * x)) / 2 := by
      rw [show 2 * b * x = 2 * (b * x) by ring, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (b * x)]
    rw [hnum]; ring
  rw [hs, MeasureTheory.integral_const_mul, integral_one_sub_cos_mul_div_sq,
    abs_mul, show |(2:ℝ)| = 2 from by norm_num]
  ring

/-- `∫_ℝ sin²x/x² dx = π` — the sinc² integral. -/
theorem integral_sin_sq_div_sq : ∫ x : ℝ, Real.sin x ^ 2 / x ^ 2 = Real.pi := by
  simpa using integral_sin_sq_mul_div_sq 1

end Real
