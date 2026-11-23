/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Fidelity
import AxQM.Postulates.API.TraceDistance
import AxQM.Concrete.TraceDistancePOVM
import ToMathlib.Analysis.InnerProductSpace.POVM

/-!
# AxQM — pure-state fidelity and the trace distance (N&C §9.2.3)

When one of the two states is **pure**, the fidelity and the trace distance
acquire especially concrete forms. Nielsen & Chuang, *Quantum Computation and
Quantum Information*, §9.2.2–9.2.3, record that for a pure state `|ψ⟩` and any
state `σ`
```
F(|ψ⟩, σ) = √⟨ψ| σ |ψ⟩                                              (9.60)
```
and it is this identity that lets the general trace-distance/fidelity bounds be
sharpened for the pure-vs-mixed case (Exercise 9.21). This file contains the two
facts used for that exercise:

* `State.fidelity_toState_sq` — the squared form of `(9.60)`,
  `F(|ψ⟩, σ)² = ⟨ψ| σ |ψ⟩ = re ⟪ψ, σ.op ψ⟫`.
* `State.one_sub_re_inner_le_traceDistance` — the key bound behind Exercise 9.21,
  `1 − ⟨ψ| σ |ψ⟩ ≤ D(|ψ⟩, σ)`.

The statement that combines them (`PureState.one_sub_fidelity_sq_le_traceDistance`, N&C
Exercise 9.21) is in `AxQM/NC/Ch9/Exercise9_21.lean`.

## Proof design

*The squared fidelity.* Through the trace-norm bridge `State.fidelity_eq_traceNorm`
(`F(ρ, σ) = ‖√ρ √σ‖₁`) with `ρ = |ψ⟩⟨ψ|`: the rank-one projector is its own CFC
square root (`cfc_real_sqrt_mul_self_eq_self_of_nonneg` on the idempotent `|ψ⟩⟨ψ|`),
so `√ρ √σ = |ψ⟩⟨√σ ψ|`, whose trace norm is `‖ψ‖·‖√σ ψ‖ = ‖√σ ψ‖`. Squaring,
`F² = ‖√σ ψ‖² = ⟪√σ ψ, √σ ψ⟫ = ⟪ψ, σ ψ⟫` (self-adjointness of `√σ` and
`√σ √σ = σ`).

*The trace-distance bound.* We instantiate the measurement-monotonicity core of
Theorem 9.1 (`AxQM.Concrete.classicalTraceDist_toPMF_le`) at the
two-outcome projective POVM `{|ψ⟩⟨ψ|, 1 − |ψ⟩⟨ψ|}`. Its outcome distributions are
`(1, 0)` on `|ψ⟩⟨ψ|` and `(⟨ψ|σ|ψ⟩, 1 − ⟨ψ|σ|ψ⟩)` on `σ`, so their classical trace
distance is `|1 − ⟨ψ|σ|ψ⟩| ≥ 1 − ⟨ψ|σ|ψ⟩`, and Theorem 9.1 bounds this by
`D(|ψ⟩, σ)`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace AxQM.Concrete

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang `(9.60)`, squared form.** For a pure state `|ψ⟩` and any
state `σ`, the fidelity satisfies `F(|ψ⟩, σ)² = ⟨ψ| σ |ψ⟩`, i.e.
`(ψ.toState.fidelity σ)² = re ⟪ψ, σ.op ψ⟫`.

Proof through the trace-norm bridge `State.fidelity_eq_traceNorm`: the density
operator of `|ψ⟩` is the rank-one projector `|ψ⟩⟨ψ|`, which is its own CFC square
root (it is a positive idempotent, so
`cfc √ (|ψ⟩⟨ψ| · |ψ⟩⟨ψ|) = |ψ⟩⟨ψ|`). Hence `√ρ √σ = |ψ⟩⟨ψ| √σ = |ψ⟩⟨√σ ψ|`, whose
trace norm is `‖ψ‖ · ‖√σ ψ‖ = ‖√σ ψ‖`. Squaring the resulting `F = ‖√σ ψ‖` gives
`‖√σ ψ‖² = ⟪√σ ψ, √σ ψ⟫ = ⟪ψ, √σ √σ ψ⟫ = ⟪ψ, σ ψ⟫` using self-adjointness of the
CFC square root and `√σ √σ = σ`. -/
theorem State.fidelity_toState_sq (ψ : PureState S) (σ : State S) :
    (ψ.toState.fidelity σ) ^ 2 = RCLike.re (inner ℂ ψ.vec (σ.op ψ.vec)) := by
  have hcomplete : CompleteSpace S.space := FiniteDimensional.completeSpace ℂ S.space
  -- The rank-one projector `|ψ⟩⟨ψ|` is its own CFC square root.
  have hsqrtP : cfc Real.sqrt ψ.toState.op = ψ.toState.op := by
    have hidem : ψ.toState.op * ψ.toState.op = ψ.toState.op := by
      rw [ψ.toState_op]
      exact (isStarProjection_rankOne_self ψ.normalized).isIdempotentElem
    conv_lhs => rw [← hidem]
    exact cfc_real_sqrt_mul_self_eq_self_of_nonneg ψ.toState.isDensity.nonneg
  -- The fidelity of a pure state reduces to `‖√σ |ψ⟩‖`.
  have hF : ψ.toState.fidelity σ = ‖cfc Real.sqrt σ.op ψ.vec‖ := by
    rw [State.fidelity_eq_traceNorm, hsqrtP, ψ.toState_op]
    have hcomp : (rankOne ℂ ψ.vec ψ.vec) * cfc Real.sqrt σ.op
        = rankOne ℂ ψ.vec (cfc Real.sqrt σ.op ψ.vec) := by
      rw [show (rankOne ℂ ψ.vec ψ.vec) * cfc Real.sqrt σ.op
            = (rankOne ℂ ψ.vec ψ.vec).comp (cfc Real.sqrt σ.op) from rfl,
          rankOne_comp, State.adjoint_cfc_sqrt_op]
    rw [hcomp, ContinuousLinearMap.traceNorm_rankOne, ψ.normalized, one_mul]
  -- `⟪√σ ψ, √σ ψ⟫ = ⟪ψ, σ ψ⟫`.
  have hinner : inner ℂ (cfc Real.sqrt σ.op ψ.vec) (cfc Real.sqrt σ.op ψ.vec)
      = inner ℂ ψ.vec (σ.op ψ.vec) := by
    calc inner ℂ (cfc Real.sqrt σ.op ψ.vec) (cfc Real.sqrt σ.op ψ.vec)
        = inner ℂ ψ.vec (adjoint (cfc Real.sqrt σ.op) (cfc Real.sqrt σ.op ψ.vec)) :=
          (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
      _ = inner ℂ ψ.vec ((cfc Real.sqrt σ.op * cfc Real.sqrt σ.op) ψ.vec) := by
          rw [State.adjoint_cfc_sqrt_op, ← mul_apply_eq_comp]
      _ = inner ℂ ψ.vec (σ.op ψ.vec) := by
          rw [cfc_real_sqrt_mul_self_of_nonneg σ.isDensity.nonneg]
  rw [hF, ← inner_self_eq_norm_sq (𝕜 := ℂ), hinner]

/-- **The key bound behind Nielsen & Chuang Exercise 9.21.** For a pure state
`|ψ⟩` and any state `σ`,
`1 − ⟨ψ| σ |ψ⟩ ≤ D(|ψ⟩, σ)`, i.e. `1 − re ⟪ψ, σ.op ψ⟫ ≤ ψ.toState.traceDistance σ`.

This is measurement monotonicity (N&C Theorem 9.1,
`AxQM.Concrete.classicalTraceDist_toPMF_le`) applied to the two-outcome
projective POVM `{|ψ⟩⟨ψ|, 1 − |ψ⟩⟨ψ|}`. Its Born distributions are `(1, 0)` on
`|ψ⟩⟨ψ|` (the projector fixes `|ψ⟩`, giving probability one) and
`(⟨ψ|σ|ψ⟩, 1 − ⟨ψ|σ|ψ⟩)` on `σ` (using `tr σ = 1`), so their classical trace
distance is `|1 − ⟨ψ|σ|ψ⟩|`; the theorem bounds it by `D(|ψ⟩, σ)`, and
`1 − ⟨ψ|σ|ψ⟩ ≤ |1 − ⟨ψ|σ|ψ⟩|`. -/
theorem State.one_sub_re_inner_le_traceDistance (ψ : PureState S) (σ : State S) :
    1 - RCLike.re (inner ℂ ψ.vec (σ.op ψ.vec)) ≤ ψ.toState.traceDistance σ := by
  have hcomplete : CompleteSpace S.space := FiniteDimensional.completeSpace ℂ S.space
  set c := RCLike.re (inner ℂ ψ.vec (σ.op ψ.vec)) with hc
  set P : S.space →L[ℂ] S.space := (rankOne ℂ) ψ.vec ψ.vec with hP
  have hproj : IsStarProjection P := isStarProjection_rankOne_self ψ.normalized
  have hψψ : (inner ℂ ψ.vec ψ.vec : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, ψ.normalized]; norm_num
  have hPψ : P ψ.vec = ψ.vec := by rw [hP, rankOne_apply, hψψ, one_smul]
  -- The two-outcome projective POVM `{|ψ⟩⟨ψ|, 1 − |ψ⟩⟨ψ|}`.
  let M : POVM (Fin 2) ℂ S.space :=
    { elements := ![P, 1 - P]
      isPositive := by
        intro i; fin_cases i
        · exact ContinuousLinearMap.IsPositive.of_isStarProjection hproj
        · exact ContinuousLinearMap.IsPositive.of_isStarProjection
            (isStarProjection_one_sub_iff.mpr hproj)
      sum_eq_one := by rw [Fin.sum_univ_two]; simp }
  have h1comp : (1 : S.space →L[ℂ] S.space) ∘L σ.op = σ.op := by ext x; simp
  -- Born distribution of `|ψ⟩⟨ψ|`: `(1, 0)`.
  have hp0 : M.toPMF ψ.toState.op 0 = 1 := by
    rw [ψ.toState_op, POVM.toPMF_rankOne_self]
    change P.reApplyInnerSelf ψ.vec = 1
    rw [reApplyInnerSelf_apply, hPψ, hψψ]; simp
  have hp1 : M.toPMF ψ.toState.op 1 = 0 := by
    rw [ψ.toState_op, POVM.toPMF_rankOne_self]
    change (1 - P).reApplyInnerSelf ψ.vec = 0
    rw [reApplyInnerSelf_apply, sub_apply,
        one_apply_eq_self, hPψ, sub_self]; simp
  -- Born distribution of `σ`: `(⟨ψ|σ|ψ⟩, 1 − ⟨ψ|σ|ψ⟩)`.
  have hq0 : M.toPMF σ.op 0 = c := by
    rw [POVM.toPMF_eq]
    change RCLike.re (LinearMap.trace ℂ S.space
      ((P ∘L σ.op : S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space)) = c
    rw [hP, rankOne_comp, σ.isPositive_op.isSelfAdjoint.adjoint_eq,
        InnerProductSpace.trace_rankOne, hc, ← inner_conj_symm ψ.vec (σ.op ψ.vec), RCLike.conj_re]
  have hq1 : M.toPMF σ.op 1 = 1 - c := by
    rw [POVM.toPMF_eq]
    change RCLike.re (LinearMap.trace ℂ S.space
      (((1 - P) ∘L σ.op : S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space)) = 1 - c
    rw [ContinuousLinearMap.sub_comp, h1comp, ContinuousLinearMap.toLinearMap_sub, map_sub, map_sub,
        σ.trace_op_eq_one, RCLike.one_re, hP, rankOne_comp,
        σ.isPositive_op.isSelfAdjoint.adjoint_eq, InnerProductSpace.trace_rankOne,
        hc, ← inner_conj_symm ψ.vec (σ.op ψ.vec), RCLike.conj_re]
  -- Measurement monotonicity (Theorem 9.1) at this POVM.
  have hle := classicalTraceDist_toPMF_le M ψ.toState.op σ.op
  rw [← State.traceDistance_eq] at hle
  have hcd : classicalTraceDist (M.toPMF ψ.toState.op) (M.toPMF σ.op) = |1 - c| := by
    rw [classicalTraceDist, Fin.sum_univ_two, hp0, hp1, hq0, hq1, zero_sub, abs_neg]; ring
  calc 1 - c ≤ |1 - c| := le_abs_self _
    _ = classicalTraceDist (M.toPMF ψ.toState.op) (M.toPMF σ.op) := hcd.symm
    _ ≤ ψ.toState.traceDistance σ := hle

/-- **The fidelity of two pure states is the magnitude of their overlap** (Nielsen & Chuang
`(9.60)` for the pure-vs-pure case): `F(|ψ⟩, |φ⟩) = ‖⟨ψ | φ⟩‖`. This
lets the non-orthogonality condition `0 < F(ψ, φ) < 1` (used in the no-cloning theorem,
N&C Problem 12.2) be traded for the overlap bounds `0 < ‖⟨ψ|φ⟩‖ < 1`.

Squaring reduces to `State.fidelity_toState_sq`: `F² = ⟨ψ| |φ⟩⟨φ| |ψ⟩ = ⟨φ, ψ⟩ · ⟨ψ, φ⟩ =
conj⟨ψ, φ⟩ · ⟨ψ, φ⟩ = ‖⟨ψ, φ⟩‖²` (`PureState.toState_op`, `rankOne_apply`, `inner_conj_symm`,
`Complex.mul_conj`). Both `F` and `‖⟨ψ, φ⟩‖` are nonnegative (`State.fidelity_nonneg`,
`norm_nonneg`), so the square roots agree. -/
theorem State.fidelity_toState_toState (ψ φ : PureState S) :
    ψ.toState.fidelity φ.toState = ‖inner ℂ ψ.vec φ.vec‖ := by
  have hF := ψ.toState.fidelity_nonneg φ.toState
  have hz := norm_nonneg (inner ℂ ψ.vec φ.vec)
  have hconj : (inner ℂ φ.vec ψ.vec : ℂ) = (starRingEnd ℂ) (inner ℂ ψ.vec φ.vec) :=
    (inner_conj_symm φ.vec ψ.vec).symm
  have hsq : (ψ.toState.fidelity φ.toState) ^ 2 = ‖inner ℂ ψ.vec φ.vec‖ ^ 2 := by
    rw [State.fidelity_toState_sq ψ φ.toState, φ.toState_op, rankOne_apply, inner_smul_right,
      hconj, mul_comm, Complex.mul_conj]
    simp [Complex.sq_norm]
  calc ψ.toState.fidelity φ.toState
      = Real.sqrt ((ψ.toState.fidelity φ.toState) ^ 2) := (Real.sqrt_sq hF).symm
    _ = Real.sqrt (‖inner ℂ ψ.vec φ.vec‖ ^ 2) := by rw [hsq]
    _ = ‖inner ℂ ψ.vec φ.vec‖ := Real.sqrt_sq hz

end AxQM
