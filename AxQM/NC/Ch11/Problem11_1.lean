/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.GeneralizedKleinInequality

/-!
# Nielsen & Chuang, Problem 11.1 (Generalized Klein's inequality)

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Problem 11.1, p. 525.

Generalized Klein's inequality tr(f(A)-f(B))>=tr((A-B)f'(B)) for convex f; deduce relative entropy
non-negativity.

## The mathematics

For self-adjoint `A, B` the operator functions `f(A)`, `f(B)`, `f'(B)` are the continuous
functional calculi. Diagonalising `A` and `B` with orthonormal eigenbases, the matrix of squared
overlaps `Wᵢⱼ = ‖⟪eᴬᵢ, eᴮⱼ⟫‖²` is doubly stochastic (Parseval), and the inequality reduces —
term by term, via the tangent-line inequality `f(bⱼ) + f'(bⱼ)(aᵢ − bⱼ) ≤ f(aᵢ)` for convex `f` —
to a scalar doubly-stochastic bound. This is the operator generalisation of the classical
Klein/Gibbs argument.

Non-negativity of the relative entropy is then the instance `A = ρ`, `B = σ`, `f(x) = x·log x`
(so `f'(x) = log x + 1`): since `tr(ρ) = tr(σ) = 1`, the `+1` in `f'` contributes `tr(ρ − σ) = 0`,
and the inequality collapses to `tr(ρ log ρ) ≥ tr(ρ log σ)`, i.e. `D(ρ‖σ) ≥ 0`.

## The setting

The statement is about self-adjoint operators `E →L[ℂ] E`, the continuous functional calculus, and
the trace. Compare the operator Klein/entropy results `ContinuousLinearMap.quantumRelativeEntropy`
and `ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_nonneg`, all in
`ToMathlib/Analysis/InnerProductSpace/`.

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/GeneralizedKleinInequality.lean`:

* `generalized_klein_inequality` — **Problem 11.1**, the operator inequality: for self-adjoint
  `A, B`, a function `f` convex on a set containing the spectra of `A` and `B` with derivative
  `f'` at each eigenvalue of `B`,
  `re tr((cfc f' B) ∘ (A − B)) ≤ re tr(cfc f A) − re tr(cfc f B)`, i.e.
  `tr(f(A) − f(B)) ≥ tr((A − B) f'(B))` (the left-hand trace equals `tr((A − B) f'(B))` by
  cyclicity). Convexity is required only on a set containing the two spectra, the faithful
  generality that admits `x ↦ x·log x` (convex only on `[0, ∞)`).
* `ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_nonneg_of_generalizedKlein` — the
  deduction the problem asks for: `0 ≤ D(ρ‖σ)` for density operators `ρ, σ` (with `σ` full rank),
  obtained from `generalized_klein_inequality` at `f = x·log x`. (Statement-identical to the
  direct log-route `ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_nonneg`; retained as
  the explicit generalized-Klein derivation Problem 11.1 requests.)

Supporting lemmas alongside them, all general mathematics:

* `ConvexOn.add_deriv_mul_sub_le` — the tangent-line inequality
  `f y + f'·(x − y) ≤ f x` for a convex `f` differentiable at `y`.
* `ConvexOn.sum_deriv_doublyStochastic_le` — the scalar generalized-Klein (doubly-stochastic
  convex) bound, the general-`f` sibling of
  `Real.sum_mul_sum_mul_log_le_neg_entropy_of_doubly_stochastic`.
* `IsSelfAdjoint.re_trace_cfc_eq_sum` — `re tr(cfc f T) = ∑ᵢ f(λᵢ)` for self-adjoint `T`.
-/
