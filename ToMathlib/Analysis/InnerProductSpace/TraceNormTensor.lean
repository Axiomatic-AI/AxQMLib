/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
public import ToMathlib.Analysis.InnerProductSpace.Polar
public import ToMathlib.Analysis.InnerProductSpace.TraceNorm
public import ToMathlib.Analysis.InnerProductSpace.CFCTensor
public import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The trace norm is multiplicative under tensor products

For operators `A : E →L[ℂ] E` and `B : F →L[ℂ] F` on finite-dimensional complex inner product
spaces, the Schatten-1 (trace) norm factorises over the tensor product:
`‖A ⊗ B‖₁ = ‖A‖₁ · ‖B‖₁` (`ContinuousLinearMap.traceNorm_mapL`).

The mechanism is that the *absolute value* factorises, `|A ⊗ B| = |A| ⊗ |B|`
(`ContinuousLinearMap.absoluteValue_mapL`): both are the positive square root of
`(A ⊗ B)† (A ⊗ B) = (A†A) ⊗ (B†B)` (`TensorProduct.mapL_adjoint_comp_self`), and the operator
square root distributes over the tensor product on nonnegative operators (`TensorProduct.sqrt_mapL`,
here in its `cfc Real.sqrt` form `ContinuousLinearMap.cfc_real_sqrt_mapL`). The trace norm is then
the trace of the absolute value (`LinearMap.ofReal_traceNorm_eq_trace_absoluteValue`), and the trace
of a tensor-product operator is the product of the traces (`ContinuousLinearMap.trace_mapL`).

## Main statements

* `ContinuousLinearMap.cfc_real_sqrt_mapL` — `√(A ⊗ B) = √A ⊗ √B` (`cfc Real.sqrt` form).
* `ContinuousLinearMap.absoluteValue_mapL` — `|A ⊗ B| = |A| ⊗ |B|`.
* `ContinuousLinearMap.traceNorm_mapL` — `‖A ⊗ B‖₁ = ‖A‖₁ · ‖B‖₁`.
-/

@[expose] public section

open scoped ComplexOrder

namespace ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

/-- **`cfc Real.sqrt` distributes over the tensor product** on nonnegative operators:
`√(A ⊗ B) = √A ⊗ √B` for `0 ≤ A`, `0 ≤ B`. The `cfc Real.sqrt`-facing restatement of
`TensorProduct.sqrt_mapL` (which is phrased with `CFC.sqrt`), bridged through
`CFC.sqrt_eq_real_sqrt`. -/
theorem cfc_real_sqrt_mapL {A : E →L[ℂ] E} {B : F →L[ℂ] F} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    cfc Real.sqrt (TensorProduct.mapL A B)
      = TensorProduct.mapL (cfc Real.sqrt A) (cfc Real.sqrt B) := by
  have hAB : (0 : TensorProduct ℂ E F →L[ℂ] TensorProduct ℂ E F) ≤ TensorProduct.mapL A B :=
    TensorProduct.mapL_nonneg hA hB
  have e1 : CFC.sqrt (TensorProduct.mapL A B) = cfc Real.sqrt (TensorProduct.mapL A B) := by
    rw [CFC.sqrt_eq_real_sqrt (TensorProduct.mapL A B), cfcₙ_eq_cfc]
  have e2 : CFC.sqrt A = cfc Real.sqrt A := by rw [CFC.sqrt_eq_real_sqrt A, cfcₙ_eq_cfc]
  have e3 : CFC.sqrt B = cfc Real.sqrt B := by rw [CFC.sqrt_eq_real_sqrt B, cfcₙ_eq_cfc]
  rw [← e1, TensorProduct.sqrt_mapL hA hB, e2, e3]

/-- **The absolute value of a tensor-product operator factorises:** `|A ⊗ B| = |A| ⊗ |B|`.
Both sides are the positive square root of `(A ⊗ B)† (A ⊗ B) = (A†A) ⊗ (B†B)`
(`TensorProduct.mapL_adjoint_comp_self`), and `√` distributes over `mapL` on the nonnegative
operators `A†A`, `B†B` (`cfc_real_sqrt_mapL`). -/
theorem absoluteValue_mapL (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    (TensorProduct.mapL A B).absoluteValue
      = TensorProduct.mapL A.absoluteValue B.absoluteValue := by
  have hA : (0 : E →L[ℂ] E) ≤ A.adjoint ∘L A := by
    have h := star_mul_self_nonneg A
    rwa [star_eq_adjoint, mul_def] at h
  have hB : (0 : F →L[ℂ] F) ≤ B.adjoint ∘L B := by
    have h := star_mul_self_nonneg B
    rwa [star_eq_adjoint, mul_def] at h
  rw [absoluteValue_eq_cfc_sqrt, TensorProduct.mapL_adjoint_comp_self, cfc_real_sqrt_mapL hA hB,
    absoluteValue_eq_cfc_sqrt, absoluteValue_eq_cfc_sqrt]

/-- **The trace norm is multiplicative under the tensor product:** `‖A ⊗ B‖₁ = ‖A‖₁ · ‖B‖₁`.
Evaluate each trace norm as the trace of the absolute value
(`LinearMap.ofReal_traceNorm_eq_trace_absoluteValue`); the absolute value factorises
(`absoluteValue_mapL`) and the trace of a tensor-product operator is the product of the traces
(`trace_mapL`). -/
theorem traceNorm_mapL (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    (TensorProduct.mapL A B).traceNorm = A.traceNorm * B.traceNorm := by
  have key : LinearMap.trace ℂ (TensorProduct ℂ E F)
        (TensorProduct.mapL A B).toLinearMap.absoluteValue
      = LinearMap.trace ℂ E A.toLinearMap.absoluteValue
        * LinearMap.trace ℂ F B.toLinearMap.absoluteValue := by
    rw [← toLinearMap_absoluteValue, absoluteValue_mapL, trace_mapL,
      toLinearMap_absoluteValue, toLinearMap_absoluteValue]
  have e := LinearMap.ofReal_traceNorm_eq_trace_absoluteValue (TensorProduct.mapL A B)
  rw [key, ← LinearMap.ofReal_traceNorm_eq_trace_absoluteValue A,
    ← LinearMap.ofReal_traceNorm_eq_trace_absoluteValue B] at e
  simp only [traceNorm_toLinearMap] at e
  exact_mod_cast e

end ContinuousLinearMap
