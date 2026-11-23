/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochMatrix
import ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM
import ToMathlib.Analysis.InnerProductSpace.Polar
import ToMathlib.Analysis.InnerProductSpace.TraceNorm

/-!
# Concrete: the trace norm of a Pauli-dot operator (Nielsen & Chuang, eq. 9.19–9.20)

The single-qubit trace-distance computation N&C carry out in §9.2.1 (the paragraph
after Exercise 9.6, eqs. 9.18–9.20) rests on one purely algebraic fact: the Hermitian
operator `(t⃗·σ)` on `ℂ²` has eigenvalues `±‖t⃗‖`, so its **trace norm** (the sum of the
absolute eigenvalues) is `2‖t⃗‖`. This file proves that fact, together
with the elementary identity that a *difference* of Bloch matrices is a Pauli-dot matrix.

The statement for states (N&C 9.20, the qubit trace
distance as half the Euclidean Bloch distance) is `AxQM.blochState_traceDistance`,
in `AxQM/NC/Ch9/Exercise9_6.lean`.

## Main results

* `traceNorm_toEuclideanCLM_pauliDot` — `‖t⃗·σ‖₁ = 2‖t⃗‖`, i.e.
  `(Matrix.toEuclideanCLM (pauliDot t)).traceNorm = 2 · √(t₀² + t₁² + t₂²)`.
* `blochMatrix_sub` — `blochMatrix r - blochMatrix s = pauliDot (½ (r - s))`, since the two
  identity halves cancel and `½(r·σ) - ½(s·σ) = ½((r - s)·σ)`.
* `blochMatrix_convex` — affine-linearity of `blochMatrix`: for `p + q = 1`,
  `p·blochMatrix a + q·blochMatrix b = blochMatrix (p a + q b)`. The reusable form of the fact
  that a two-point mixture of Bloch states is the Bloch state of the averaged Bloch vector.

## Proof of the trace-norm identity

Write `A = t⃗·σ` (as an operator via `Matrix.toEuclideanCLM`). It is self-adjoint
(`pauliDot` is Hermitian), and `A† A = A² = ‖t⃗‖² • 1` (from `pauliDot_mul_self`). Hence the
absolute value `|A| = √(A†A) = √(‖t⃗‖² • 1) = ‖t⃗‖ • 1` — computed through the continuous
functional calculus, where `cfc √ (c • 1) = √c • 1` for the scalar operator `c • 1`
(`cfc_algebraMap`). Finally `‖A‖₁ = ‖|A|‖₁ = ‖(‖t⃗‖ : ℂ)‖ · ‖1‖₁ = ‖t⃗‖ · re(tr 1) = ‖t⃗‖ · 2`,
using that `1` is positive so `‖1‖₁ = re(tr 1) = finrank = 2`.
-/

open Matrix ContinuousLinearMap
open scoped ComplexOrder

noncomputable section

namespace AxQM.Concrete

/-- **`‖t⃗·σ‖₁ = 2‖t⃗‖` (Nielsen & Chuang, eq. 9.19).** The trace norm of the Pauli-dot operator
`t⃗·σ = t₀X + t₁Y + t₂Z` on the qubit equals twice the Euclidean length of `t⃗`, because `t⃗·σ`
is self-adjoint with `(t⃗·σ)² = ‖t⃗‖² • I`, so its absolute value is `‖t⃗‖ • I` and its trace
norm is `‖t⃗‖ · dim = 2‖t⃗‖`. -/
theorem traceNorm_toEuclideanCLM_pauliDot (t : Fin 3 → ℝ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (pauliDot t)).traceNorm
      = 2 * Real.sqrt (t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2) := by
  set c := t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set A := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (pauliDot t) with hA
  -- `A` is self-adjoint (`pauliDot t` is Hermitian).
  have hsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, hA, ← map_star]
    congr 1
    rw [Matrix.star_eq_conjTranspose, pauliDot_conjTranspose]
  have hadj : ContinuousLinearMap.adjoint A = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hsa
  -- `A† A = ‖t⃗‖² • 1`.
  have hAA : (ContinuousLinearMap.adjoint A).comp A = (c : ℂ) • 1 := by
    rw [hadj, hA, ← ContinuousLinearMap.mul_def, ← map_mul, pauliDot_mul_self, map_smul, map_one]
  -- `|A| = ‖t⃗‖ • 1`, via the functional calculus `cfc √ (c • 1) = √c • 1`.
  have habs : A.absoluteValue = (Real.sqrt c : ℂ) • 1 := by
    rw [ContinuousLinearMap.absoluteValue_eq_cfc_sqrt, hAA,
      show ((c : ℂ) • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
          = algebraMap ℝ _ c from by simp [Algebra.algebraMap_eq_smul_one],
      cfc_algebraMap]
    simp [Algebra.algebraMap_eq_smul_one]
  -- `‖A‖₁ = ‖|A|‖₁ = √c · re(tr 1) = √c · 2`.
  rw [← ContinuousLinearMap.traceNorm_absoluteValue, habs, ContinuousLinearMap.traceNorm_smul,
    ContinuousLinearMap.traceNorm_eq_re_trace_of_isPositive ContinuousLinearMap.isPositive_one,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg c)]
  simp only [ContinuousLinearMap.toLinearMap_one]
  rw [LinearMap.trace_one, finrank_euclideanSpace_fin]
  norm_num
  ring

/-- **`blochMatrix r - blochMatrix s = (r - s)·σ / 2`.** The identity halves in
`blochMatrix r = ½(I + r·σ)` cancel, leaving `½(r·σ - s·σ) = ½((r - s)·σ) = (½(r - s))·σ`. -/
theorem blochMatrix_sub (r s : Fin 3 → ℝ) :
    blochMatrix r - blochMatrix s = pauliDot ((2⁻¹ : ℝ) • (r - s)) := by
  rw [pauliDot_smul, pauliDot_sub]
  push_cast
  simp only [blochMatrix]
  module

/-- **Affine-linearity of the Bloch matrix.** For weights with `p + q = 1`,
`p·blochMatrix a + q·blochMatrix b = blochMatrix (p a + q b)`: the identity halves recombine
(`p·½I + q·½I = ½I` using `p + q = 1`) and `pauliDot` is `ℝ`-linear, so a convex combination
of Bloch matrices is the Bloch matrix of the convex combination of the vectors. This is the
reusable form of "a two-point mixture of Bloch states is the Bloch state of the averaged
Bloch vector", used in the qubit trace-distance statements. -/
theorem blochMatrix_convex (a b : Fin 3 → ℝ) {p q : ℝ} (h : p + q = 1) :
    (p : ℂ) • blochMatrix a + (q : ℂ) • blochMatrix b = blochMatrix (p • a + q • b) := by
  have hq : q = 1 - p := by linarith
  subst hq
  simp only [blochMatrix, pauliDot_add, pauliDot_smul]
  push_cast
  module

end AxQM.Concrete
