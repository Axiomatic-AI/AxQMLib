/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integral representation of the real logarithm

For `x > 0` the natural logarithm has the improper-integral representation

`log x = ∫₀^∞ ((1 + s)⁻¹ - (x + s)⁻¹) ds`,

a Frullani-type identity obtained by integrating the antiderivative
`s ↦ log (1 + s) - log (x + s) = log ((1 + s) / (x + s))`, which increases (for `x > 1`) or
decreases (for `x < 1`) from `-log x` at `s = 0` to `0` at `s → ∞`. The reference term `(1 + s)⁻¹`
regularises the otherwise non-integrable `(x + s)⁻¹` — their difference equals
`(x - 1) / ((1 + s)(x + s))`, decaying like `(x - 1) / s²` — and pins the value at the base point
`x = 1`, where both sides vanish.

This is the scalar core of the operator-logarithm integral representation
`cfc Real.log A = ∫₀^∞ ((1 + s)⁻¹ • 1 - (A + s)⁻¹) ds` for a positive operator `A`: applied to each
eigenvalue `λ` of `A` it gives `log λ = ∫₀^∞ ((1 + s)⁻¹ - (λ + s)⁻¹) ds`, and the operator identity
follows by the spectral calculus. That operator representation, differentiated along a mixing line
via the resolvent derivative, is the analytic input of the second-derivative proof of concavity of
the von Neumann entropy (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.22).

## Main results

* `Real.hasDerivAt_log_add_sub_log_add` — the antiderivative `s ↦ log (1 + s) - log (x + s)` has
  derivative `(1 + s)⁻¹ - (x + s)⁻¹` at every `s ≥ 0`.
* `Real.tendsto_log_add_sub_log_add_atTop` — that antiderivative tends to `0` at `+∞`.
* `Real.integrableOn_Ioi_inv_add_sub_inv_add` — the integrand `(1 + s)⁻¹ - (x + s)⁻¹` is integrable
  on `(0, ∞)`.
* `Real.log_eq_integral_Ioi_inv_add_sub_inv_add` — the integral representation itself.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace Real

variable {x : ℝ}

/-- The antiderivative `s ↦ log (1 + s) - log (x + s)` used in the integral representation of the
logarithm has derivative `(1 + s)⁻¹ - (x + s)⁻¹` at every `s ≥ 0` (assuming `x > 0`, so that both
`1 + s` and `x + s` stay away from `0`). -/
theorem hasDerivAt_log_add_sub_log_add (hx : 0 < x) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun t => Real.log (1 + t) - Real.log (x + t)) ((1 + s)⁻¹ - (x + s)⁻¹) s := by
  have h1 : (0 : ℝ) < 1 + s := by linarith
  have h2 : (0 : ℝ) < x + s := by linarith
  have e1 : HasDerivAt (fun t : ℝ => 1 + t) 1 s := by
    simpa using (hasDerivAt_id s).const_add (1 : ℝ)
  have e2 : HasDerivAt (fun t : ℝ => x + t) 1 s := by
    simpa using (hasDerivAt_id s).const_add x
  have d1 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 + s)⁻¹ s := by
    simpa only [one_div] using e1.log h1.ne'
  have d2 : HasDerivAt (fun t : ℝ => Real.log (x + t)) (x + s)⁻¹ s := by
    simpa only [one_div] using e2.log h2.ne'
  exact d1.sub d2

/-- The antiderivative `s ↦ log (1 + s) - log (x + s)` tends to `0` as `s → +∞` (assuming `x > 0`),
because `(1 + s) / (x + s) → 1` and `log` is continuous at `1`. -/
theorem tendsto_log_add_sub_log_add_atTop (hx : 0 < x) :
    Tendsto (fun t => Real.log (1 + t) - Real.log (x + t)) atTop (nhds 0) := by
  have hAt : Tendsto (fun t : ℝ => x + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop x tendsto_id
  have hinv : Tendsto (fun t : ℝ => (x + t)⁻¹) atTop (nhds 0) := hAt.inv_tendsto_atTop
  have h0 : Tendsto (fun t : ℝ => (1 - x) * (x + t)⁻¹) atTop (nhds 0) := by
    simpa using hinv.const_mul (1 - x)
  have hr : Tendsto (fun t : ℝ => (1 + t) / (x + t)) atTop (nhds 1) := by
    have h1 := h0.const_add (1 : ℝ)
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hne : x + t ≠ 0 := (show (0 : ℝ) < x + t by linarith).ne'
    field_simp
    ring
  have hlog : Tendsto (fun t : ℝ => Real.log ((1 + t) / (x + t))) atTop (nhds 0) := by
    have hc := (Real.continuousAt_log one_ne_zero).tendsto.comp hr
    simpa [Function.comp_def, Real.log_one] using hc
  refine hlog.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h1ne : (1 : ℝ) + t ≠ 0 := (show (0 : ℝ) < 1 + t by linarith).ne'
  have h2ne : x + t ≠ 0 := (show (0 : ℝ) < x + t by linarith).ne'
  rw [Real.log_div h1ne h2ne]

/-- The integrand `s ↦ (1 + s)⁻¹ - (x + s)⁻¹` of the logarithm's integral representation is
integrable on `(0, ∞)` (assuming `x > 0`): although neither term is individually integrable, their
difference `(x - 1) / ((1 + s)(x + s))` decays like `(x - 1) / s²`. Proved from the monotonicity of
the antiderivative (its derivative has constant sign, `≥ 0` for `x ≥ 1` and `≤ 0` for `x ≤ 1`)
together with its finite limit at `+∞`. -/
theorem integrableOn_Ioi_inv_add_sub_inv_add (hx : 0 < x) :
    IntegrableOn (fun s => (1 + s)⁻¹ - (x + s)⁻¹) (Ioi 0) := by
  have hcont : ContinuousWithinAt (fun t => Real.log (1 + t) - Real.log (x + t)) (Ici 0) 0 :=
    (hasDerivAt_log_add_sub_log_add hx le_rfl).continuousAt.continuousWithinAt
  have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt (fun t => Real.log (1 + t) - Real.log (x + t))
      ((1 + s)⁻¹ - (x + s)⁻¹) s := fun s hs => hasDerivAt_log_add_sub_log_add hx (le_of_lt hs)
  rcases le_total 1 x with hx1 | hx1
  · refine integrableOn_Ioi_deriv_of_nonneg hcont hderiv (fun s hs => ?_)
      (tendsto_log_add_sub_log_add_atTop hx)
    have hs0 : (0 : ℝ) < s := hs
    have hle : (x + s)⁻¹ ≤ (1 + s)⁻¹ := (inv_le_inv₀ (by linarith) (by linarith)).mpr (by linarith)
    linarith
  · refine integrableOn_Ioi_deriv_of_nonpos hcont hderiv (fun s hs => ?_)
      (tendsto_log_add_sub_log_add_atTop hx)
    have hs0 : (0 : ℝ) < s := hs
    have hle : (1 + s)⁻¹ ≤ (x + s)⁻¹ := (inv_le_inv₀ (by linarith) (by linarith)).mpr (by linarith)
    linarith

/-- **Integral representation of the logarithm.** For `x > 0`,

`log x = ∫₀^∞ ((1 + s)⁻¹ - (x + s)⁻¹) ds`.

The reference term `(1 + s)⁻¹` makes the improper integral converge and fixes the constant so that
the value is exactly `log x` (in particular both sides vanish at `x = 1`). See the module docstring
for the operator-logarithm application. -/
theorem log_eq_integral_Ioi_inv_add_sub_inv_add (hx : 0 < x) :
    Real.log x = ∫ s in Ioi (0 : ℝ), ((1 + s)⁻¹ - (x + s)⁻¹) := by
  have hcont : ContinuousWithinAt (fun t => Real.log (1 + t) - Real.log (x + t)) (Ici 0) 0 :=
    (hasDerivAt_log_add_sub_log_add hx le_rfl).continuousAt.continuousWithinAt
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun s hs => hasDerivAt_log_add_sub_log_add hx (le_of_lt hs))
    (integrableOn_Ioi_inv_add_sub_inv_add hx) (tendsto_log_add_sub_log_add_atTop hx)
  rw [hval]
  simp

end Real
