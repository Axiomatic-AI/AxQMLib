/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFCSqrtInequality
public import ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# The trace form of the pretty-good-measurement square-root operator inequality

For positive operators `Γ ≥ 0` and `Λ ≥ 0` on a finite-dimensional complex Hilbert space, this file
records the **weighted-trace** consequence of the square-root operator inequality
`2 • (1 - √Γ) ≤ (1 - Γ)² + (1 - Γ)` (`ContinuousLinearMap.two_smul_one_sub_cfc_sqrt_le`):

`2 · re tr((1 - √Γ)·Λ)  ≤  re tr(((1 - Γ)² + (1 - Γ))·Λ)`

(with `√Γ = cfc Real.sqrt Γ` the operator square root).  It is the trace step of the error estimate
for the **pretty-good (square-root) measurement** — Nielsen & Chuang's Box 12.5, the transition from
the operator inequality (12.89)–(12.91) to the trace inequality (12.92)–(12.93), used to bound the
average decoding error in the achievability half of the
**Holevo–Schumacher–Westmoreland theorem** (`χ(E) = C⁽¹⁾(E)`, N&C Theorem 12.8).

There the operator `Γ` is the Gram operator of the (typical-subspace–compressed) codeword
eigenvectors `|Ẽ_c⟩`, `Λ = diag(λ_c) ≥ 0` is the diagonal of codeword eigenvalue weights, and the
"correct-decoding deficit" of the square-root POVM is `∑_c λ_c(1 - α_{cc}) = sp(Λ(1 - Γ^{1/2}))`
where `α = Γ^{1/2}`.  The inequality below is N&C's

`2 · sp(Λ(E - Γ^{1/2}))  ≤  sp(Λ(E - Γ)²) + sp(Λ(E - Γ))`   (N&C eqs. (12.92)–(12.93)),

now with a *general* positive weight `Λ` in place of a diagonal one, and the "spur" `sp` read as
`re tr` on the ambient Hilbert space (by trace cyclicity, `re tr((1 - √Γ)·Λ) = re tr(Λ·(1 - √Γ))`,
so the weight may be placed on either side).

## What this file provides

* `ContinuousLinearMap.two_mul_re_trace_one_sub_cfc_sqrt_mul_le` — the trace inequality
  `2 · re tr((1 - √Γ)·Λ) ≤ re tr(((1 - Γ)² + (1 - Γ))·Λ)` (eqs. (12.92)–(12.93), combined RHS).

* `ContinuousLinearMap.two_mul_re_trace_one_sub_cfc_sqrt_mul_le_add_re_trace` — the same bound with
  the right-hand side split into the two separate traces `re tr((1 - Γ)²·Λ) + re tr((1 - Γ)·Λ)`, as
  N&C write it at (12.93); this is the directly-consumable form (each trace becomes one of the
  physical terms `tr(σ_M(I - P))`, `tr(P σ_M P P_{M'})`, … of the error estimate (12.79)).

## Proof

Both are one step of trace monotonicity on top of the operator inequality.  Pairing against a
positive operator `Λ` is monotone in the Loewner order (`re_trace_mul_mono_left`:
`A ≤ B`, `0 ≤ Λ` ⟹ `re tr(A·Λ) ≤ re tr(B·Λ)`), so applying it to
`two_smul_one_sub_cfc_sqrt_le` with `A = 2 • (1 - √Γ)` and `B = (1 - Γ)² + (1 - Γ)` gives
`re tr((2 • (1 - √Γ))·Λ) ≤ re tr(((1 - Γ)² + (1 - Γ))·Λ)`.  Unfolding `2 • x = x + x`
(`two_smul`) and distributing the trace and the real part (`map_add`) turns the left-hand side into
`2 · re tr((1 - √Γ)·Λ)`.  The split form distributes the trace over the sum `(1 - Γ)² + (1 - Γ)`
once more.

-/

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-- **The trace form of the pretty-good-measurement square-root operator inequality**
(Nielsen & Chuang, Box 12.5, eqs. (12.92)–(12.93)): for positive operators `Γ ≥ 0` and `Λ ≥ 0`,

`2 · re tr((1 - √Γ)·Λ)  ≤  re tr(((1 - Γ)² + (1 - Γ))·Λ)`,

where `√Γ = cfc Real.sqrt Γ`.  It is the weighted trace of the square-root operator inequality
`2 • (1 - √Γ) ≤ (1 - Γ)² + (1 - Γ)` (`two_smul_one_sub_cfc_sqrt_le`), the step that turns the
correct-decoding deficit `sp(Λ(E - Γ^{1/2}))` of the pretty-good (square-root) POVM into the
"false-decoding" cross terms of the HSW random-coding error estimate.

Proof: pairing against `Λ ≥ 0` is monotone in the Loewner order (`re_trace_mul_mono_left`), so it
carries `two_smul_one_sub_cfc_sqrt_le` to `re tr((2 • (1 - √Γ))·Λ) ≤ re tr(((1 - Γ)² + (1 - Γ))·Λ)`;
`two_smul` and the additivity of the trace and the real part then rewrite the left-hand side as
`2 · re tr((1 - √Γ)·Λ)`. -/
theorem two_mul_re_trace_one_sub_cfc_sqrt_mul_le {Γ Λ : E →L[ℂ] E} (hΓ : 0 ≤ Γ) (hΛ : 0 ≤ Λ) :
    2 * RCLike.re (LinearMap.trace ℂ E (((1 - cfc Real.sqrt Γ) * Λ : E →L[ℂ] E) : E →ₗ[ℂ] E))
      ≤ RCLike.re (LinearMap.trace ℂ E
          ((((1 - Γ) ^ 2 + (1 - Γ)) * Λ : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
  have hmono := re_trace_mul_mono_left (two_smul_one_sub_cfc_sqrt_le hΓ) hΛ
  rw [two_smul, add_mul, ContinuousLinearMap.toLinearMap_add, map_add, map_add] at hmono
  linarith [hmono]

/-- **The trace form of the pretty-good-measurement square-root operator inequality, split
right-hand side** (Nielsen & Chuang, Box 12.5, eq. (12.93)): for positive operators `Γ ≥ 0` and
`Λ ≥ 0`,

`2 · re tr((1 - √Γ)·Λ)  ≤  re tr((1 - Γ)²·Λ) + re tr((1 - Γ)·Λ)`.

The right-hand side of `two_mul_re_trace_one_sub_cfc_sqrt_mul_le` split into its two summands
`sp(Λ(E - Γ)²)` and `sp(Λ(E - Γ))`, as N&C write it — the form in which each trace becomes a single
physical term of the random-coding error estimate.  Immediate from
`two_mul_re_trace_one_sub_cfc_sqrt_mul_le` by distributing the trace and the real part over the sum
`(1 - Γ)² + (1 - Γ)`. -/
theorem two_mul_re_trace_one_sub_cfc_sqrt_mul_le_add_re_trace {Γ Λ : E →L[ℂ] E} (hΓ : 0 ≤ Γ)
    (hΛ : 0 ≤ Λ) :
    2 * RCLike.re (LinearMap.trace ℂ E (((1 - cfc Real.sqrt Γ) * Λ : E →L[ℂ] E) : E →ₗ[ℂ] E))
      ≤ RCLike.re (LinearMap.trace ℂ E (((1 - Γ) ^ 2 * Λ : E →L[ℂ] E) : E →ₗ[ℂ] E))
        + RCLike.re (LinearMap.trace ℂ E (((1 - Γ) * Λ : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
  have h := two_mul_re_trace_one_sub_cfc_sqrt_mul_le hΓ hΛ
  rw [add_mul, ContinuousLinearMap.toLinearMap_add, map_add, map_add] at h
  linarith [h]

end ContinuousLinearMap
