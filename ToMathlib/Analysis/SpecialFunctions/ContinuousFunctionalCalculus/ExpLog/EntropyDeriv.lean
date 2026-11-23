/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Deriv
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.TraceDeriv
public import ToMathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Second derivative of the entropy `re tr(cfc negMulLog ·)` along an affine line

For operators on a finite-dimensional complex inner product space, the von Neumann entropy of a
self-adjoint operator `T` is `S(T) = re tr(cfc Real.negMulLog T)`
(`ContinuousLinearMap.vonNeumannEntropy_eq_re_trace_cfc_negMulLog`), where
`Real.negMulLog x = -(x · log x)`. This file computes the first and second derivatives of the
entropy along an affine line `p ↦ a + p • b` and shows the second derivative is non-positive
when the line stays strictly positive — the analytic heart of the alternate
(second-derivative) proof of concavity of the von Neumann entropy (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Exercise 11.22).

Writing `Wₚ = a + p • b` (self-adjoint direction `b`) and `f(p) = re tr(cfc negMulLog Wₚ)`, on
the range of `p` where `Wₚ` is strictly positive:

* `f'(p) = -re tr(b · log Wₚ) - re tr(b)`
  (`hasDerivAt_re_trace_cfc_negMulLog_add_smul`);
* `f''(p) = -re tr(b · ∫₀^∞ (Wₚ+s)⁻¹ b (Wₚ+s)⁻¹ ds) ≤ 0`
  (`deriv2_re_trace_cfc_negMulLog_add_smul_nonpos`).

## Method

Since `cfc negMulLog Wₚ = -(Wₚ · cfc log Wₚ)` for `Wₚ` strictly positive
(`cfc_negMulLog_eq_neg_mul_cfc_log`), we have `f(p) = -re tr(Wₚ · log Wₚ)`. Differentiating the
operator product `Wₚ · log Wₚ` by the Leibniz rule (`HasDerivAt.mul`) with

* `d/dp Wₚ = b`, and
* `d/dp cfc log Wₚ = ∫₀^∞ (Wₚ+s)⁻¹ b (Wₚ+s)⁻¹ ds` (`hasDerivAt_cfc_log_add_smul`)

and then applying the continuous linear functional `re ∘ tr`
(`ContinuousLinearMap.reTraceCLM`), the `Wₚ · d/dp log Wₚ` term collapses under the trace via
`tr(Wₚ · ∫₀^∞ (Wₚ+s)⁻¹ b (Wₚ+s)⁻¹ ds) = tr(b)`
(`LinearMap.trace_mul_integral_Ioi_ringInverse_mul_mul_ringInverse`), leaving
`f'(p) = -re tr(b · log Wₚ) - re tr(b)`. Differentiating once more, only the
`-re tr(b · log Wₚ)` term is non-constant, and its derivative is
`-re tr(b · ∫₀^∞ (Wₚ+s)⁻¹ b (Wₚ+s)⁻¹ ds)`, which is `≤ 0` because the trace integral is
non-negative (`LinearMap.re_trace_mul_integral_Ioi_ringInverse_mul_mul_ringInverse_nonneg`, the
Hilbert–Schmidt-square positivity). The passage from `f'` to `f''` uses that `f'` equals the
first-derivative function on the (open) strictly-positive range, via
`Filter.EventuallyEq.deriv_eq`.

## Main results

* `cfc_negMulLog_eq_neg_mul_cfc_log` — `cfc negMulLog W = -(W · cfc log W)` for `W` strictly
  positive.
* `hasDerivAt_re_trace_cfc_negMulLog_add_smul` — the first derivative of the entropy along the
  line.
* `deriv2_re_trace_cfc_negMulLog_add_smul_nonpos` — the second derivative is non-positive.
-/

@[expose] public section

open MeasureTheory Set

/-- **`negMulLog` of a strictly positive operator via `log`.** For a strictly positive element
`W` of a C⋆-algebra, `cfc Real.negMulLog W = -(W * cfc Real.log W)`. Indeed
`Real.negMulLog x = -(x · log x)`, and the continuous functional calculus is multiplicative
(`cfc_mul`) with `cfc id W = W` (`cfc_id'`); `Real.log` is continuous on the (strictly positive)
spectrum of `W`. -/
theorem cfc_negMulLog_eq_neg_mul_cfc_log
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {W : A} (hW : IsStrictlyPositive W) :
    cfc Real.negMulLog W = -(W * cfc Real.log W) := by
  have hspec : ∀ x ∈ spectrum ℝ W, 0 < x :=
    (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp hW).2
  have hlog : ContinuousOn Real.log (spectrum ℝ W) :=
    Real.continuousOn_log.mono fun x hx => ne_of_gt (hspec x hx)
  rw [Real.negMulLog_eq_neg, cfc_neg (fun x => x * Real.log x) W,
    cfc_mul (fun x => x) Real.log W (by fun_prop) hlog, cfc_id' ℝ W]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E] [Nontrivial E]

/-- **First derivative of the entropy along an affine line.** For `b` self-adjoint and
`a + p₀ • b` strictly positive (operators on a finite-dimensional complex inner product space),
the entropy `f(p) = re tr(cfc Real.negMulLog (a + p • b))` is differentiable at `p₀` with

`f'(p₀) = -re tr(b · cfc Real.log (a + p₀ • b)) - re tr(b)`.

Since `cfc negMulLog Wₚ = -(Wₚ · cfc log Wₚ)` (`cfc_negMulLog_eq_neg_mul_cfc_log`), this is the
Leibniz derivative of `Wₚ · cfc log Wₚ` under `re ∘ tr`, with the derivative of `cfc log Wₚ`
supplied by `hasDerivAt_cfc_log_add_smul` and the `Wₚ · d/dp log Wₚ` term collapsing to `tr(b)`
via `LinearMap.trace_mul_integral_Ioi_ringInverse_mul_mul_ringInverse`. See the module
docstring. -/
theorem hasDerivAt_re_trace_cfc_negMulLog_add_smul
    {a b : E →L[ℂ] E} (hb : IsSelfAdjoint b) {p₀ : ℝ}
    (h : IsStrictlyPositive (a + p₀ • b)) :
    HasDerivAt (fun p : ℝ =>
        RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.negMulLog (a + p • b))))
      (-RCLike.re ((LinearMap.trace ℂ E) ↑(b * cfc Real.log (a + p₀ • b)))
        - RCLike.re ((LinearMap.trace ℂ E) ↑b)) p₀ := by
  -- Derivatives of the two factors of `Wₚ · cfc log Wₚ`.
  have hWderiv : HasDerivAt (fun p : ℝ => a + p • b) b p₀ := by
    simpa using ((hasDerivAt_id p₀).smul_const b).const_add a
  have hlogderiv : HasDerivAt (fun p : ℝ => cfc Real.log (a + p • b))
      (∫ s in Ioi (0 : ℝ), Ring.inverse (a + p₀ • b + s • 1) * b
        * Ring.inverse (a + p₀ • b + s • 1)) p₀ :=
    hasDerivAt_cfc_log_add_smul hb h
  -- Leibniz rule for the operator product, then push through `re ∘ tr`.
  have hmul := hWderiv.mul hlogderiv
  have hLderiv := (ContinuousLinearMap.reTraceCLM E).hasFDerivAt.comp_hasDerivAt p₀ hmul
  -- The `Wₚ · d/dp log Wₚ` term collapses to `tr(b)` under the trace.
  have h870 := LinearMap.trace_mul_integral_Ioi_ringInverse_mul_mul_ringInverse h b
  -- Simplify the derivative value.
  have hval : ContinuousLinearMap.reTraceCLM E (b * cfc Real.log (a + p₀ • b)
        + (a + p₀ • b) * ∫ s in Ioi (0 : ℝ), Ring.inverse (a + p₀ • b + s • 1) * b
          * Ring.inverse (a + p₀ • b + s • 1))
      = RCLike.re ((LinearMap.trace ℂ E) ↑(b * cfc Real.log (a + p₀ • b)))
        + RCLike.re ((LinearMap.trace ℂ E) ↑b) := by
    rw [map_add, ContinuousLinearMap.reTraceCLM_apply, ContinuousLinearMap.reTraceCLM_apply, h870]
  -- On the ball the entropy equals `-(re ∘ tr)(Wₚ · cfc log Wₚ)`.
  have heqf : (fun p : ℝ =>
        RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.negMulLog (a + p • b))))
      =ᶠ[nhds p₀] fun p : ℝ =>
        -ContinuousLinearMap.reTraceCLM E ((a + p • b) * cfc Real.log (a + p • b)) := by
    filter_upwards [eventually_isStrictlyPositive_add_smul h hb] with p hp
    rw [cfc_negMulLog_eq_neg_mul_cfc_log hp, ContinuousLinearMap.reTraceCLM_apply,
      ContinuousLinearMap.toLinearMap_neg, map_neg, map_neg]
  -- Assemble.
  have hmain := (hLderiv.neg).congr_of_eventuallyEq heqf
  rwa [hval, neg_add] at hmain

/-- **The first derivative of the entropy, as a differentiable function.** For `b` self-adjoint
and `a + p₀ • b` strictly positive, the first-derivative function
`p ↦ -re tr(b · cfc Real.log (a + p • b)) - re tr(b)` is differentiable at `p₀` with derivative

`-re tr(b · ∫₀^∞ (a + p₀ • b + s)⁻¹ b (a + p₀ • b + s)⁻¹ ds)`.

Only the `-re tr(b · log Wₚ)` summand is non-constant; its derivative comes from applying
`re ∘ tr` and left multiplication by `b` to `hasDerivAt_cfc_log_add_smul`. -/
theorem hasDerivAt_neg_re_trace_mul_cfc_log_add_smul
    {a b : E →L[ℂ] E} (hb : IsSelfAdjoint b) {p₀ : ℝ}
    (h : IsStrictlyPositive (a + p₀ • b)) :
    HasDerivAt (fun p : ℝ =>
        -RCLike.re ((LinearMap.trace ℂ E) ↑(b * cfc Real.log (a + p • b)))
          - RCLike.re ((LinearMap.trace ℂ E) ↑b))
      (-RCLike.re ((LinearMap.trace ℂ E) ↑(b * ∫ s in Ioi (0 : ℝ),
        Ring.inverse (a + p₀ • b + s • 1) * b * Ring.inverse (a + p₀ • b + s • 1)))) p₀ := by
  have hlogderiv : HasDerivAt (fun p : ℝ => cfc Real.log (a + p • b))
      (∫ s in Ioi (0 : ℝ), Ring.inverse (a + p₀ • b + s • 1) * b
        * Ring.inverse (a + p₀ • b + s • 1)) p₀ :=
    hasDerivAt_cfc_log_add_smul hb h
  have hbmul := hlogderiv.const_mul b
  have hLderiv := (ContinuousLinearMap.reTraceCLM E).hasFDerivAt.comp_hasDerivAt p₀ hbmul
  simp only [Function.comp_def, ContinuousLinearMap.reTraceCLM_apply] at hLderiv
  exact (hLderiv.neg).sub_const (RCLike.re ((LinearMap.trace ℂ E) ↑b))

/-- **The second derivative of the entropy along an affine line is non-positive.** For `b`
self-adjoint and `a + p₀ • b` strictly positive (operators on a finite-dimensional complex inner
product space),

`(deriv^[2] fun p => re tr(cfc Real.negMulLog (a + p • b))) p₀ ≤ 0`.

This is the operator-level statement `f''(p) ≤ 0` for the entropy `f(p) = S(a + p • b)`, the
analytic heart of Nielsen & Chuang's alternate proof of concavity of the von Neumann entropy
(Exercise 11.22), in the strictly-positive ("invertible") case. On the ball where `a + p • b`
stays strictly positive, the first derivative equals the function of
`hasDerivAt_re_trace_cfc_negMulLog_add_smul` (`Filter.EventuallyEq.deriv_eq`), whose derivative
(`hasDerivAt_neg_re_trace_mul_cfc_log_add_smul`) is
`-re tr(b · ∫₀^∞ (a+p₀•b+s)⁻¹ b (a+p₀•b+s)⁻¹ ds)`; this is `≤ 0` since the trace integral is
non-negative (`LinearMap.re_trace_mul_integral_Ioi_ringInverse_mul_mul_ringInverse_nonneg`, the
Hilbert–Schmidt-square positivity). -/
theorem deriv2_re_trace_cfc_negMulLog_add_smul_nonpos
    {a b : E →L[ℂ] E} (hb : IsSelfAdjoint b) {p₀ : ℝ}
    (h : IsStrictlyPositive (a + p₀ • b)) :
    (deriv^[2] fun p : ℝ =>
      RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.negMulLog (a + p • b)))) p₀ ≤ 0 := by
  -- On a neighbourhood of `p₀` the first derivative equals the explicit first-derivative function.
  have hderivEq : (deriv fun p : ℝ =>
        RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.negMulLog (a + p • b))))
      =ᶠ[nhds p₀] fun p : ℝ =>
        -RCLike.re ((LinearMap.trace ℂ E) ↑(b * cfc Real.log (a + p • b)))
          - RCLike.re ((LinearMap.trace ℂ E) ↑b) := by
    filter_upwards [eventually_isStrictlyPositive_add_smul h hb] with p hp
    exact (hasDerivAt_re_trace_cfc_negMulLog_add_smul hb hp).deriv
  -- `deriv^[2] f p₀ = deriv (deriv f) p₀ = deriv (first-derivative function) p₀`.
  have hval : (deriv^[2] fun p : ℝ =>
        RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.negMulLog (a + p • b)))) p₀
      = -RCLike.re ((LinearMap.trace ℂ E) ↑(b * ∫ s in Ioi (0 : ℝ),
          Ring.inverse (a + p₀ • b + s • 1) * b * Ring.inverse (a + p₀ • b + s • 1))) := by
    rw [show (deriv^[2] fun p : ℝ =>
          RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.negMulLog (a + p • b)))) p₀
        = deriv (deriv fun p : ℝ =>
          RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.negMulLog (a + p • b)))) p₀ from rfl,
      hderivEq.deriv_eq, (hasDerivAt_neg_re_trace_mul_cfc_log_add_smul hb h).deriv]
  rw [hval, neg_nonpos]
  exact LinearMap.re_trace_mul_integral_Ioi_ringInverse_mul_mul_ringInverse_nonneg h hb
