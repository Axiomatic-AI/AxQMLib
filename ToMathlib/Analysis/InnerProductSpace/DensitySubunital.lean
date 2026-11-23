/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Density
public import ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# A density operator is subunital, and its overlaps are trace-bounded

For a density operator `ρ` on a finite-dimensional complex Hilbert space, this file records two
elementary order/trace facts about the neighbouring density-operator API:

* `ContinuousLinearMap.IsDensityOp.le_one` — `ρ ≤ 1` in the Loewner order: a density operator is
  **subunital**. Obtained from `‖ρ‖ ≤ ‖ρ‖₁ = 1` and the C*-algebra bound
  `a ≤ ‖a‖ • 1` for a self-adjoint `a`.
* `ContinuousLinearMap.IsDensityOp.re_trace_comp_le` — for any positive operator `A`,
  `re tr(A ρ) ≤ re tr A`: an expectation-style overlap never exceeds the total weight `tr A`. The
  gap is `re tr(A (1 − ρ)) ≥ 0`, positive because `1 − ρ ≥ 0` (subunitality) and `A ≥ 0`
  (`re_trace_mul_nonneg_of_nonneg`).

## Generality

Both are stated over `ℂ`, matching the ℂ generality of the neighbouring density-operator trace API
(`ContinuousLinearMap.IsDensityOp.re_trace_mul_self_le_one`,
`ContinuousLinearMap.IsDensityOp.re_trace_depolarize_pow_le`). The `ℂ` is genuinely forced:
`le_one` uses `IsSelfAdjoint.le_algebraMap_norm_self`, whose `CStarAlgebra` hypothesis is a
`ℂ`-algebra structure, and `re_trace_comp_le` additionally uses the `ℂ`-only
`ContinuousLinearMap.re_trace_mul_nonneg_of_nonneg`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace ContinuousLinearMap.IsDensityOp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-- **A density operator is subunital**: `ρ ≤ 1` in the Loewner order. Its operator norm is bounded
by its trace norm `‖ρ‖ ≤ ‖ρ‖₁`, which equals `re tr ρ = 1` for a density operator; then the
C*-algebra bound `ρ ≤ ‖ρ‖ • 1` (`IsSelfAdjoint.le_algebraMap_norm_self`) combined with `‖ρ‖ ≤ 1`
gives `ρ ≤ 1`. -/
theorem le_one {ρ : E →L[ℂ] E} (hρ : ρ.IsDensityOp) : ρ ≤ 1 := by
  have hnorm : ‖ρ‖ ≤ 1 := by
    calc ‖ρ‖ ≤ ρ.traceNorm := ContinuousLinearMap.opNorm_le_traceNorm ρ
      _ = RCLike.re (LinearMap.trace ℂ E (ρ : E →ₗ[ℂ] E)) :=
          ContinuousLinearMap.traceNorm_eq_re_trace_of_isPositive hρ.isPositive
      _ = 1 := by rw [hρ.trace_eq_one]; simp
  calc ρ ≤ algebraMap ℝ (E →L[ℂ] E) ‖ρ‖ := hρ.isPositive.isSelfAdjoint.le_algebraMap_norm_self
    _ = ‖ρ‖ • (1 : E →L[ℂ] E) := Algebra.algebraMap_eq_smul_one _
    _ ≤ (1 : ℝ) • (1 : E →L[ℂ] E) := smul_le_smul_of_nonneg_right hnorm zero_le_one
    _ = 1 := one_smul ℝ 1

/-- **A positive operator's overlap with a density operator is trace-bounded**:
`re tr(A ρ) ≤ re tr A` for a positive operator `A` and a density operator `ρ`. The difference is
`re tr(A (1 − ρ)) ≥ 0`, which is nonnegative because `1 − ρ ≥ 0` (a density operator is subunital,
`le_one`) and `A ≥ 0`, via `re_trace_mul_nonneg_of_nonneg`. (Applied with `A` a POVM effect, this is
the per-outcome bound `bornProb ρ i ≤ tr(Eᵢ)`.) -/
theorem re_trace_comp_le {A ρ : E →L[ℂ] E} (hA : 0 ≤ A) (hρ : ρ.IsDensityOp) :
    RCLike.re (LinearMap.trace ℂ E (A.comp ρ : E →ₗ[ℂ] E)) ≤
      RCLike.re (LinearMap.trace ℂ E (A : E →ₗ[ℂ] E)) := by
  have hpos : (0 : E →L[ℂ] E) ≤ 1 - ρ := sub_nonneg.mpr hρ.le_one
  have key : 0 ≤ RCLike.re (LinearMap.trace ℂ E (↑(A * (1 - ρ)) : E →ₗ[ℂ] E)) :=
    ContinuousLinearMap.re_trace_mul_nonneg_of_nonneg hA hpos
  have hsplit : RCLike.re (LinearMap.trace ℂ E (↑(A * (1 - ρ)) : E →ₗ[ℂ] E))
      = RCLike.re (LinearMap.trace ℂ E (A : E →ₗ[ℂ] E))
        - RCLike.re (LinearMap.trace ℂ E (A.comp ρ : E →ₗ[ℂ] E)) := by
    have hcomp : A * (1 - ρ) = A - A.comp ρ := by
      rw [mul_sub, mul_one, ContinuousLinearMap.mul_def]
    rw [hcomp]; simp only [ContinuousLinearMap.toLinearMap_sub, map_sub]
  rw [hsplit] at key; linarith

end ContinuousLinearMap.IsDensityOp
