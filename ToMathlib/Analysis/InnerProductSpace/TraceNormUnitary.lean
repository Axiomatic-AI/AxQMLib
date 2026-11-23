/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.TraceNorm
public import ToMathlib.Analysis.InnerProductSpace.PolarUnitary

/-!
# Trace-norm duality with unitaries (Nielsen & Chuang, Lemma 9.5)

For an operator `A` on a finite-dimensional inner product space `E` and a unitary `U`,
Nielsen & Chuang, *Quantum Computation and Quantum Information*, Lemma 9.5 (p. 410) states

`|tr (A U)| ≤ tr |A|`,   with equality attained at some unitary,

where `tr |A|` is the trace norm `‖A‖₁` (the sum of the singular values, equivalently
`re (tr √(A† A))`). Equivalently, `‖A‖₁` is the *maximum* of `|tr (A U)|` over all unitaries `U`.
N&C use it as the last ingredient of the proof of Uhlmann's theorem
(`F(ρ, σ) = max |⟨ψ|ϕ⟩|`).

## Main results

* `ContinuousLinearMap.norm_trace_mul_le_traceNorm` — N&C `(9.63)`: `|tr (A U)| ≤ ‖A‖₁` for
  every unitary `U`.
* `ContinuousLinearMap.exists_mem_unitary_norm_trace_mul_eq_traceNorm` — the bound is
  *attained*: some unitary `U` satisfies `|tr (A U)| = ‖A‖₁`.
* `ContinuousLinearMap.isGreatest_norm_trace_mul_unitary` — the two together: `‖A‖₁` is the
  greatest value of `|tr (A U)|` over unitaries `U`.

## Implementation notes

This is the *unitary* specialization of the bundled variational characterization
`ContinuousLinearMap.traceNorm_eq_iSup`, which expresses `‖A‖₁` as the supremum over
*contractions* `W` (`‖W‖ ≤ 1`) of `re (hsPairing A W)`. Two adaptations turn that into the
shape N&C state and use:

* **Modulus, not real part.** Passing to `|tr (A U)|` (rather than `re`) is free: the trace
  connects to the HS pairing by `tr (A U) = hsPairing A U†` (`hsPairing A W = tr (W† ∘ A)`,
  cyclicity of the trace, and `(U†)† = U`), and the *norm* form of the Hölder bound
  `norm_hsPairing_le_traceNorm_of_opNorm_le_one` already carries the absolute value.
* **Maximum, not supremum.** Attainment reuses the left unitary polar decomposition
  `exists_mem_unitary_eq_comp_absoluteValue`, `A = U₀ ∘L |A|`: the witness is `U₀†`, for which
  `tr (A U₀†) = tr |A| = (‖A‖₁ : 𝕜)` by cyclicity and `U₀† U₀ = 1`. (N&C write the polar
  decomposition on the other side, `A = |A| V`, giving witness `V†`; the two conventions
  produce the same maximum, which is all Lemma 9.5 asserts.)

The `[CompleteSpace E]` hypothesis is automatic in finite dimension and matches the ambient
convention of the polar-decomposition and HS-pairing API these proofs build on.
-/

@[expose] public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- **Nielsen & Chuang, Lemma 9.5, inequality `(9.63)`.** For any operator `A` and unitary
`U` on a finite-dimensional inner product space, `|tr (A U)| ≤ ‖A‖₁` (the trace norm `tr |A|`).

The trace of the product `A U` equals the Hilbert–Schmidt pairing `hsPairing A U†` (using
`hsPairing A W = tr (W† ∘ A)`, cyclicity of the trace, and `(U†)† = U`), and the norm form of
the Hölder bound `norm_hsPairing_le_traceNorm_of_opNorm_le_one` bounds it by `‖A‖₁` since the
unitary `U†` is a contraction. -/
theorem norm_trace_mul_le_traceNorm (A : E →L[𝕜] E) {U : E →L[𝕜] E}
    (hU : U ∈ unitary (E →L[𝕜] E)) :
    ‖LinearMap.trace 𝕜 E ↑(A * U)‖ ≤ A.traceNorm := by
  have hbridge : LinearMap.trace 𝕜 E ↑(A * U) = A.hsPairing (star U) := by
    rw [ContinuousLinearMap.hsPairing_eq, ← ContinuousLinearMap.star_eq_adjoint, star_star,
      ← ContinuousLinearMap.mul_def, ContinuousLinearMap.toLinearMap_mul,
          ContinuousLinearMap.toLinearMap_mul,
      LinearMap.trace_mul_comm]
  rw [hbridge]
  refine A.norm_hsPairing_le_traceNorm_of_opNorm_le_one ?_
  -- `star U` is a contraction: a unitary has operator norm at most one.
  have hUU : ‖star U‖ * ‖star U‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, (Unitary.mem_iff.mp (Unitary.star_mem hU)).1,
      ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg (star U)]

/-- **Nielsen & Chuang, Lemma 9.5, attainment.** The trace-norm bound `|tr (A U)| ≤ ‖A‖₁` is
attained by a unitary: there exists `U ∈ unitary` with `|tr (A U)| = ‖A‖₁`.

Take the left unitary polar decomposition `A = U₀ ∘L |A|`
(`exists_mem_unitary_eq_comp_absoluteValue`) and use the witness `U₀†`. Then
`tr (A U₀†) = tr (U₀ |A| U₀†) = tr |A| = (‖A‖₁ : 𝕜)` by cyclicity of the trace and
`U₀† U₀ = 1`; taking the modulus of this nonnegative real recovers `‖A‖₁`. -/
theorem exists_mem_unitary_norm_trace_mul_eq_traceNorm (A : E →L[𝕜] E) :
    ∃ U ∈ unitary (E →L[𝕜] E), ‖LinearMap.trace 𝕜 E ↑(A * U)‖ = A.traceNorm := by
  obtain ⟨U, hU, hAU⟩ := A.exists_mem_unitary_eq_comp_absoluteValue
  refine ⟨star U, Unitary.star_mem hU, ?_⟩
  have hAU' : A = U * A.absoluteValue := by rw [ContinuousLinearMap.mul_def]; exact hAU
  have key : LinearMap.trace 𝕜 E ↑(A * star U) = (A.traceNorm : 𝕜) := by
    conv_lhs => rw [hAU']
    rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul,
        LinearMap.trace_mul_comm,
      ← mul_assoc, ← ContinuousLinearMap.toLinearMap_mul, (Unitary.mem_iff.mp hU).1,
      ContinuousLinearMap.toLinearMap_one, one_mul, ContinuousLinearMap.toLinearMap_absoluteValue,
      ← LinearMap.ofReal_traceNorm_eq_trace_absoluteValue, traceNorm_toLinearMap]
  rw [key, RCLike.norm_ofReal, abs_of_nonneg A.traceNorm_nonneg]

/-- **Nielsen & Chuang, Lemma 9.5** (bundled form): the trace norm `‖A‖₁ = tr |A|` is the
*greatest* value of `|tr (A U)|` over all unitaries `U`. Combines the inequality
`norm_trace_mul_le_traceNorm` (upper bound) with `exists_mem_unitary_norm_trace_mul_eq_traceNorm`
(attainment). -/
theorem isGreatest_norm_trace_mul_unitary (A : E →L[𝕜] E) :
    IsGreatest {r : ℝ | ∃ U ∈ unitary (E →L[𝕜] E), r = ‖LinearMap.trace 𝕜 E ↑(A * U)‖}
      A.traceNorm := by
  refine ⟨?_, ?_⟩
  · obtain ⟨U, hU, hbnd⟩ := A.exists_mem_unitary_norm_trace_mul_eq_traceNorm
    exact ⟨U, hU, hbnd.symm⟩
  · rintro b ⟨U, hU, rfl⟩
    exact A.norm_trace_mul_le_traceNorm hU

end ContinuousLinearMap
