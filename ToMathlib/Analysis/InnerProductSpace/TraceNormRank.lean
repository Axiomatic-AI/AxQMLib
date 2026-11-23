/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.TraceNorm

/-!
# Trace norm bounded by rank and Hilbert–Schmidt norm

For a linear map `T : E →ₗ[𝕜] F` between finite-dimensional inner product spaces over `𝕜`
(`ℝ` or `ℂ`), this file records the **Schatten 1–2 comparison**: the trace (Schatten-1) norm is
bounded by the square root of the rank times the Hilbert–Schmidt (Schatten-2) norm,
```
‖T‖₁ ≤ √(rank T) · ‖T‖₂,   i.e.   ‖T‖₁² ≤ (rank T) · ‖T‖₂².
```
Here `rank T = finrank 𝕜 (range T)` and the Hilbert–Schmidt norm squared is
`‖T‖₂² = ∑ᵢ σᵢ² = re tr(T† ∘ T)`.

Both norms are read off the singular values `σᵢ = T.singularValues i`: the trace norm is `∑ᵢ σᵢ`
(`LinearMap.traceNorm_eq`) and the Hilbert–Schmidt norm squared is `∑ᵢ σᵢ²`. Only the first
`rank T` singular values are nonzero (`LinearMap.support_singularValues`), so the bound is exactly
Cauchy–Schwarz applied to those `rank T` nonzero singular values against the all-ones vector — the
factor is the *rank*, not the ambient dimension `finrank 𝕜 E`.

The rank-sharp form is what makes the bound useful: for an operator whose range is small (e.g. a
product of low-rank projectors), it is far stronger than the ambient-dimension Cauchy–Schwarz
`‖T‖₁² ≤ (finrank 𝕜 E) · ‖T‖₂²`.

## Main results

* `LinearMap.sum_sq_singularValues_eq_re_trace_adjoint_comp_self` — the Hilbert–Schmidt norm
  squared as a trace: `∑ᵢ σᵢ² = re tr(T† ∘ T)`.
* `LinearMap.traceNorm_sq_le_finrank_range_mul_re_trace_adjoint_comp_self` — the Schatten 1–2
  comparison in squared form: `‖T‖₁² ≤ (finrank 𝕜 (range T)) · re tr(T† ∘ T)`.
* `ContinuousLinearMap.traceNorm_sq_le_finrank_range_mul_re_trace_adjoint_comp_self` — the same
  bound for a continuous linear map, obtained from the `LinearMap` version through the
  trace-norm/adjoint coercion bridges. This is the operator form the applications consume.
-/

public section

open Module (finrank)

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **The Hilbert–Schmidt norm squared is the trace of `T† ∘ T`.** For a linear map `T` between
finite-dimensional inner product spaces, the sum of the squared singular values equals the real
part of the trace of `T† ∘ T`:

`∑ᵢ σᵢ² = re tr(T† ∘ T)`.

The operator `T† ∘ T` is positive (hence symmetric), so its (real) trace is the sum of its
eigenvalues (`LinearMap.IsSymmetric.re_trace_eq_sum_eigenvalues`), and each eigenvalue is a squared
singular value (`LinearMap.sq_singularValues_fin`). -/
theorem sum_sq_singularValues_eq_re_trace_adjoint_comp_self (T : E →ₗ[𝕜] F) :
    ∑ i : Fin (finrank 𝕜 E), T.singularValues i.val ^ 2
      = RCLike.re (LinearMap.trace 𝕜 E (adjoint T ∘ₗ T)) := by
  rw [T.isSymmetric_adjoint_comp_self.re_trace_eq_sum_eigenvalues rfl]
  exact Finset.sum_congr rfl fun i _ ↦ T.sq_singularValues_fin rfl i

/-- **Schatten 1–2 comparison: the trace norm is bounded by the rank times the Hilbert–Schmidt
norm** (in squared form). For a linear map `T` between finite-dimensional inner product spaces,

`‖T‖₁² ≤ (finrank 𝕜 (range T)) · re tr(T† ∘ T) = (rank T) · ‖T‖₂²`.

The trace norm `‖T‖₁ = ∑ᵢ σᵢ` is supported on the first `rank T = finrank 𝕜 (range T)` singular
values (`LinearMap.support_singularValues`); Cauchy–Schwarz over those `rank T` terms against the
all-ones vector gives `(∑ᵢ σᵢ)² ≤ (rank T) · ∑ᵢ σᵢ²`, and `∑ᵢ σᵢ² = re tr(T† ∘ T)`
(`sum_sq_singularValues_eq_re_trace_adjoint_comp_self`). The factor is the **rank**, not the ambient
dimension `finrank 𝕜 E`, which is what makes the bound sharp for low-rank operators. -/
theorem traceNorm_sq_le_finrank_range_mul_re_trace_adjoint_comp_self (T : E →ₗ[𝕜] F) :
    T.traceNorm ^ 2
      ≤ (finrank 𝕜 T.range : ℝ) * RCLike.re (LinearMap.trace 𝕜 E (adjoint T ∘ₗ T)) := by
  set r := finrank 𝕜 T.range with hr
  set N := finrank 𝕜 E with hN
  have hrN : r ≤ N := T.finrank_range_le
  have hsub : Finset.range r ⊆ Finset.range N := Finset.range_mono hrN
  -- The trace norm sums the singular values, and only the first `r` of them are nonzero.
  have htr : T.traceNorm = ∑ i ∈ Finset.range r, T.singularValues i := by
    rw [traceNorm_eq, Fin.sum_univ_eq_sum_range (fun k ↦ T.singularValues k) N]
    refine (Finset.sum_subset hsub ?_).symm
    intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    exact T.singularValues_eq_zero_iff_le_finrank_range.mpr hi
  -- The Hilbert–Schmidt norm squared, restricted to the support and then extended.
  have hsq : ∑ i : Fin N, T.singularValues i.val ^ 2
      = ∑ i ∈ Finset.range N, T.singularValues i ^ 2 :=
    Fin.sum_univ_eq_sum_range (fun k ↦ T.singularValues k ^ 2) N
  have hsqle : ∑ i ∈ Finset.range r, T.singularValues i ^ 2
      ≤ RCLike.re (LinearMap.trace 𝕜 E (adjoint T ∘ₗ T)) := by
    rw [← T.sum_sq_singularValues_eq_re_trace_adjoint_comp_self, hsq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ ↦ sq_nonneg _
  -- Cauchy–Schwarz over the `r` nonzero singular values against the all-ones vector.
  have hcs : (∑ i ∈ Finset.range r, T.singularValues i) ^ 2
      ≤ (r : ℝ) * ∑ i ∈ Finset.range r, T.singularValues i ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range r)
      (fun i ↦ T.singularValues i) (fun _ ↦ (1 : ℝ))
    simpa [mul_comm, Finset.card_range] using this
  calc T.traceNorm ^ 2
      = (∑ i ∈ Finset.range r, T.singularValues i) ^ 2 := by rw [htr]
    _ ≤ (r : ℝ) * ∑ i ∈ Finset.range r, T.singularValues i ^ 2 := hcs
    _ ≤ (r : ℝ) * RCLike.re (LinearMap.trace 𝕜 E (adjoint T ∘ₗ T)) := by
        exact mul_le_mul_of_nonneg_left hsqle (by positivity)

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [CompleteSpace F]

/-- **Schatten 1–2 comparison for a continuous linear map** (in squared form). For a continuous
linear map `T` between finite-dimensional inner product spaces,

`‖T‖₁² ≤ (finrank 𝕜 (range T)) · re tr(T† ∘ T) = (rank T) · ‖T‖₂²`.

This is the `ContinuousLinearMap` form of
`LinearMap.traceNorm_sq_le_finrank_range_mul_re_trace_adjoint_comp_self`, obtained by rewriting the
trace norm through `ContinuousLinearMap.traceNorm_toLinearMap` and the adjoint composition through
`ContinuousLinearMap.adjoint_toLinearMap`; the range and rank are read off the underlying map.
It is the operator form consumed by applications where the relevant maps (density operators, their
square roots and products) are continuous. -/
theorem traceNorm_sq_le_finrank_range_mul_re_trace_adjoint_comp_self (T : E →L[𝕜] F) :
    T.traceNorm ^ 2
      ≤ (finrank 𝕜 (LinearMap.range (T : E →ₗ[𝕜] F)) : ℝ)
        * RCLike.re (LinearMap.trace 𝕜 E ((ContinuousLinearMap.adjoint T).comp T : E →ₗ[𝕜] E)) := by
  rw [← T.traceNorm_toLinearMap, ContinuousLinearMap.toLinearMap_comp,
    ← ContinuousLinearMap.adjoint_toLinearMap]
  exact (T : E →ₗ[𝕜] F).traceNorm_sq_le_finrank_range_mul_re_trace_adjoint_comp_self

end ContinuousLinearMap
