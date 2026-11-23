/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.EigenvalueMonotone
public import ToMathlib.Analysis.InnerProductSpace.TraceNorm
public import ToMathlib.Analysis.InnerProductSpace.PosNegPart
public import ToMathlib.Analysis.InnerProductSpace.Trace

/-!
# Mirsky's inequality: the trace-norm bound on sorted eigenvalue differences

For self-adjoint operators `A, B` on a finite-dimensional complex inner product space, the
`ℓ¹` distance between their sorted eigenvalue spectra is bounded by the trace norm of their
difference:
`∑ᵢ |λᵢ(A) − λᵢ(B)| ≤ ‖A − B‖₁`,
where `λᵢ` denotes the eigenvalues in the common decreasing order
(`LinearMap.IsSymmetric.eigenvalues`) and `‖·‖₁` is `ContinuousLinearMap.traceNorm`.

This is **Mirsky's inequality**; it is the spectral ingredient of Fannes' inequality
(Nielsen & Chuang, *Quantum Computation and Quantum Information*, Theorem 11.6, eq. (11.46)),
where it turns a trace-distance bound between two density operators into a bound on the `ℓ¹`
distance between their eigenvalue spectra, from which continuity of the von Neumann entropy
follows.

## Proof

Following Nielsen & Chuang: write `A − B = Q − R` with `Q = (A−B)⁺`, `R = (A−B)⁻` the positive
and negative parts (both positive operators). The operator `V := A + R = B + Q` dominates both
`A` and `B` in the quadratic-form order (`V − A = R ≥ 0`, `V − B = Q ≥ 0`), so by Weyl's
monotonicity theorem its sorted eigenvalues `tᵢ := λᵢ(V)` satisfy `tᵢ ≥ λᵢ(A)` and
`tᵢ ≥ λᵢ(B)`; hence `2tᵢ ≥ λᵢ(A) + λᵢ(B) + |λᵢ(A) − λᵢ(B)|`. Summing and using
`∑ᵢ λᵢ = re tr` gives
`∑ᵢ |λᵢ(A) − λᵢ(B)| ≤ 2 tr V − tr A − tr B = tr Q + tr R = ‖A − B‖₁`,
the last equality being the trace-norm Jordan split
(`IsSelfAdjoint.traceNorm_eq_re_trace_posPart_add`).

## Main results

* `LinearMap.IsSymmetric.sum_abs_eigenvalues_sub_le`: the eigenvalue core — if a
  symmetric `V` dominates symmetric `A, B` in quadratic-form order, then
  `∑ᵢ |λᵢ(A) − λᵢ(B)| ≤ 2 ∑ᵢ λᵢ(V) − ∑ᵢ λᵢ(A) − ∑ᵢ λᵢ(B)`.
* `IsSelfAdjoint.sum_abs_eigenvalues_sub_le_traceNorm`: Mirsky's inequality itself,
  `∑ᵢ |λᵢ(A) − λᵢ(B)| ≤ ‖A − B‖₁`.
-/

@[expose] public section

open RCLike
open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ}

/-- **Eigenvalue core of Mirsky's inequality.** If a symmetric operator `V` dominates the
symmetric operators `A` and `B` in the quadratic-form order (`V − A` and `V − B` are positive),
then the `ℓ¹` distance between the sorted spectra of `A` and `B` is controlled by the traces:
`∑ᵢ |λᵢ(A) − λᵢ(B)| ≤ 2 ∑ᵢ λᵢ(V) − ∑ᵢ λᵢ(A) − ∑ᵢ λᵢ(B)`.

For each index `i`, Weyl's monotonicity theorem gives `λᵢ(A) ≤ λᵢ(V)` and `λᵢ(B) ≤ λᵢ(V)`, and
the pointwise inequality `|a − b| ≤ 2t − a − b` holds whenever `a ≤ t` and `b ≤ t`. -/
theorem sum_abs_eigenvalues_sub_le {A B V : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hV : V.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n)
    (hVA : (V - A).IsPositive) (hVB : (V - B).IsPositive) :
    ∑ i, |hA.eigenvalues hn i - hB.eigenvalues hn i|
      ≤ 2 * ∑ i, hV.eigenvalues hn i - ∑ i, hA.eigenvalues hn i - ∑ i, hB.eigenvalues hn i := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hAV : hA.eigenvalues hn i ≤ hV.eigenvalues hn i :=
    hA.eigenvalues_mono_of_sub_isPositive hV hVA hn i
  have hBV : hB.eigenvalues hn i ≤ hV.eigenvalues hn i :=
    hB.eigenvalues_mono_of_sub_isPositive hV hVB hn i
  rcases abs_cases (hA.eigenvalues hn i - hB.eigenvalues hn i) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    rw [h] <;> linarith

end LinearMap.IsSymmetric

section Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-- **Mirsky's inequality** (Nielsen & Chuang, Theorem 11.6, eq. (11.46)). For self-adjoint
operators `A, B` on a finite-dimensional complex inner product space, the `ℓ¹` distance between
their sorted eigenvalue spectra is bounded by the trace norm of their difference:
`∑ᵢ |λᵢ(A) − λᵢ(B)| ≤ ‖A − B‖₁`.

The dominating operator is `V := A + (A−B)⁻`; then `V − A = (A−B)⁻ ≥ 0` and
`V − B = (A−B)⁺ ≥ 0`, so `V` dominates `A` and `B`, and `2 tr V − tr A − tr B` collapses to
`re tr (A−B)⁺ + re tr (A−B)⁻ = ‖A − B‖₁`. -/
theorem IsSelfAdjoint.sum_abs_eigenvalues_sub_le_traceNorm {A B : E →L[ℂ] E}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {n : ℕ} (hn : Module.finrank ℂ E = n) :
    ∑ i, |hA.isSymmetric.eigenvalues hn i - hB.isSymmetric.eigenvalues hn i|
      ≤ (A - B).traceNorm := by
  have hM : IsSelfAdjoint (A - B) := hA.sub hB
  set Q : E →L[ℂ] E := (A - B)⁺ with hQ_def
  set R : E →L[ℂ] E := (A - B)⁻ with hR_def
  have hQpos : Q.IsPositive := ContinuousLinearMap.isPositive_posPart (A - B)
  have hRpos : R.IsPositive := ContinuousLinearMap.isPositive_negPart (A - B)
  have hMdecomp : A - B = Q - R := (CFC.posPart_sub_negPart (A - B) hM).symm
  set V : E →L[ℂ] E := A + R with hV_def
  have hVsa : IsSelfAdjoint V := hA.add hRpos.isSelfAdjoint
  -- `V` dominates `A` and `B`: `V − A = R`, `V − B = Q`.
  have hVA_eq : V - A = R := by rw [hV_def]; abel
  have hVB_eq : V - B = Q := by rw [hV_def, add_sub_right_comm, hMdecomp]; abel
  have hVApos : ((V : E →ₗ[ℂ] E) - (A : E →ₗ[ℂ] E)).IsPositive := by
    rw [← ContinuousLinearMap.toLinearMap_sub, hVA_eq]; exact hRpos.toLinearMap
  have hVBpos : ((V : E →ₗ[ℂ] E) - (B : E →ₗ[ℂ] E)).IsPositive := by
    rw [← ContinuousLinearMap.toLinearMap_sub, hVB_eq]; exact hQpos.toLinearMap
  -- The eigenvalue core, applied to the coerced linear maps.
  have hcore := LinearMap.IsSymmetric.sum_abs_eigenvalues_sub_le
    hA.isSymmetric hB.isSymmetric hVsa.isSymmetric hn hVApos hVBpos
  refine hcore.trans (le_of_eq ?_)
  -- Convert eigenvalue sums to real traces and collapse via the trace-norm Jordan split.
  have e1 : RCLike.re (LinearMap.trace ℂ E (V : E →ₗ[ℂ] E))
      = RCLike.re (LinearMap.trace ℂ E (A : E →ₗ[ℂ] E))
        + RCLike.re (LinearMap.trace ℂ E (R : E →ₗ[ℂ] E)) := by
    rw [hV_def, ContinuousLinearMap.toLinearMap_add, map_add, map_add]
  have e2 : RCLike.re (LinearMap.trace ℂ E (A : E →ₗ[ℂ] E))
      - RCLike.re (LinearMap.trace ℂ E (B : E →ₗ[ℂ] E))
      = RCLike.re (LinearMap.trace ℂ E (Q : E →ₗ[ℂ] E))
        - RCLike.re (LinearMap.trace ℂ E (R : E →ₗ[ℂ] E)) := by
    have hcoe : (A : E →ₗ[ℂ] E) - (B : E →ₗ[ℂ] E) = (Q : E →ₗ[ℂ] E) - (R : E →ₗ[ℂ] E) := by
      rw [← ContinuousLinearMap.toLinearMap_sub, ← ContinuousLinearMap.toLinearMap_sub, hMdecomp]
    have := congrArg (fun T => RCLike.re (LinearMap.trace ℂ E T)) hcoe
    simpa [map_sub] using this
  rw [← hVsa.isSymmetric.re_trace_eq_sum_eigenvalues hn,
      ← hA.isSymmetric.re_trace_eq_sum_eigenvalues hn,
      ← hB.isSymmetric.re_trace_eq_sum_eigenvalues hn,
      IsSelfAdjoint.traceNorm_eq_re_trace_posPart_add (A - B) hM]
  linarith [e1, e2]

end Complex
