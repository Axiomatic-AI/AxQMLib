/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.TraceNormUnitary

/-!
# Nielsen & Chuang, Lemma 9.5 (`|tr(AU)| ≤ tr|A|`, with equality)

For any operator A and unitary U, |tr(AU)| <= tr|A|, equality at U=V† of polar decomposition.

N&C state this "easily proved lemma" (p. 410) as the last ingredient of the proof of
Uhlmann's theorem (`F(ρ, σ) = max |⟨ψ|ϕ⟩|`). Here `tr |A|` is the **trace norm** `‖A‖₁`
(the sum of the singular values, equivalently `re (tr √(A† A))`). The full content of the
lemma is that `‖A‖₁` is the **maximum** of `|tr (A U)|` over all unitaries `U`: the
inequality `(9.63)` is the upper bound, and the equality clause is its attainment.

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/TraceNormUnitary.lean`:

* `ContinuousLinearMap.norm_trace_mul_le_traceNorm` — **Lemma 9.5, inequality `(9.63)`**:
  for an operator `A` and a unitary `U`, `‖tr (A U)‖ ≤ ‖A‖₁`. Proved by rewriting
  `tr (A U) = hsPairing A U†` and applying the norm form of the Hölder bound
  (`norm_hsPairing_le_traceNorm_of_opNorm_le_one`), since the unitary `U†` is a contraction.
* `ContinuousLinearMap.exists_mem_unitary_norm_trace_mul_eq_traceNorm` — **Lemma 9.5,
  equality clause**: the bound is attained, `∃ U ∈ unitary, ‖tr (A U)‖ = ‖A‖₁`. The witness
  is `U₀†` from the left unitary polar decomposition `A = U₀ ∘L |A|`, for which
  `tr (A U₀†) = tr |A| = (‖A‖₁ : 𝕜)`.
* `ContinuousLinearMap.isGreatest_norm_trace_mul_unitary` — the two combined: `‖A‖₁` is the
  `IsGreatest` value of `‖tr (A U)‖` over unitaries `U` (i.e. `tr|A| = max_U |tr(AU)|`).
-/
