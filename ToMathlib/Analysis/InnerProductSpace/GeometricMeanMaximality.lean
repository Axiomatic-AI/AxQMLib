/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.GeometricMean
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import ToMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import ToMathlib.Analysis.InnerProductSpace.Positive
public import ToMathlib.Analysis.InnerProductSpace.SchurComplement
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import ToMathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import ToMathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Maximality and joint concavity of the operator geometric mean

For strictly positive operators `A, B` on a finite-dimensional complex inner product space,
the operator geometric mean `M₀(A, B) := A^{1/2} (A^{-1/2} B A^{-1/2})^{1/2} A^{1/2}` is the
**largest** self-adjoint operator `X` satisfying the block-PSD condition `[[A, X], [X, B]] ≥ 0`.
This file proves the two halves of maximality, and derives joint concavity of `M₀` as a
consequence.

## Main results

* `CFC.geometricMean_block_quadForm_nonneg` — `M₀(A, B)` is in the witness set: the block
  quadratic form `⟨x, Ax⟩ + ⟨x, M₀ y⟩ + ⟨y, M₀ x⟩ + ⟨y, By⟩ ≥ 0` for all `x, y`.
* `CFC.le_geometricMean_of_block_quadForm_nonneg` — every `X` in the witness set is bounded
  above by `M₀(A, B)`.
* `CFC.geometricMean_concave` — `(A, B) ↦ M₀(A, B)` is jointly operator-concave on strictly
  positive × nonneg operators (consequence of maximality + convexity of the witness set).
-/

namespace CFC

open Ring RCLike

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

@[expose] public section Maximality

/-- **Membership**: for strictly positive `A` and nonnegative `B`, the geometric mean
`M₀(A, B)` is in the witness set, i.e., the block `[[A, M₀], [M₀, B]]` is positive semidefinite
as a quadratic form on `E × E`. Carlen Theorem 3.7 first half. -/
theorem geometricMean_block_quadForm_nonneg
    {A B : E →L[ℂ] E} (hA : IsStrictlyPositive A) (hB : 0 ≤ B) (x y : E) :
    0 ≤ re (inner ℂ x (A x) + inner ℂ x ((geometricMean A B) y) +
            inner ℂ y ((geometricMean A B) x) + inner ℂ y (B y)) := by
  -- Block quadratic form equals `⟨v, v⟩` for `v := √A x + √(conjSqrt A⁻¹ B) (√A y)`,
  -- after pushing self-adjoints across via `IsSymmetric.apply_clm` and using
  -- `√A · conjSqrt A⁻¹ B · √A = B` (the `conjSqrt` round-trip).
  have hZ : 0 ≤ conjSqrt (Ring.inverse A) B := conjSqrt_nonneg _ hB
  have hAA (u : E) : sqrt A (sqrt A u) = A u :=
    DFunLike.congr_fun (sqrt_mul_sqrt_self A hA.nonneg) u
  have hBB (u : E) : sqrt A (sqrt (conjSqrt (Ring.inverse A) B)
      (sqrt (conjSqrt (Ring.inverse A) B) (sqrt A u))) = B u :=
    DFunLike.congr_fun
      ((sqrt_mul_sqrt_self _ hZ).symm ▸ conjSqrt_conjSqrt_ringInverse A B hA) u
  suffices h : inner ℂ x (A x) + inner ℂ x ((geometricMean A B) y) +
      inner ℂ y ((geometricMean A B) x) + inner ℂ y (B y) =
      inner ℂ (sqrt A x + sqrt (conjSqrt (Ring.inverse A) B) (sqrt A y))
          (sqrt A x + sqrt (conjSqrt (Ring.inverse A) B) (sqrt A y)) by
    rw [h]; exact inner_self_nonneg
  simp only [inner_add_left, inner_add_right,
    (sqrt_nonneg A).isSelfAdjoint.isSymmetric.apply_clm,
    (sqrt_nonneg (conjSqrt (Ring.inverse A) B)).isSelfAdjoint.isSymmetric.apply_clm,
    geometricMean_eq_mul, mul_apply_eq_comp, hAA, hBB]
  ring

variable [FiniteDimensional ℂ E]

/-- **Le-direction (maximality)**: every `X` in the block-PSD witness set is bounded above by
`M₀(A, B)`. Together with `geometricMean_block_quadForm_nonneg`, this is Carlen Theorem 3.7.

The argument: rewrite `X = conjSqrt A (conjSqrt A⁻¹ X)` (`conjSqrt` round-trip), then apply
`conjSqrt`-monotonicity twice — once with the abs-detour `Y ≤ √(Y²)`, once with the conjugated
Schur bound `(conjSqrt A⁻¹ X)² = conjSqrt A⁻¹ (X · A⁻¹ · X) ≤ conjSqrt A⁻¹ B`. -/
theorem le_geometricMean_of_block_quadForm_nonneg
    {A B X : E →L[ℂ] E} (hA : IsStrictlyPositive A) (hB : 0 ≤ B) (hX : IsSelfAdjoint X)
    (h_block : ∀ x y : E,
        0 ≤ re (inner ℂ x (A x) + inner ℂ x (X y) + inner ℂ y (X x) + inner ℂ y (B y))) :
    X ≤ geometricMean A B :=
  calc X
      = conjSqrt A (conjSqrt (Ring.inverse A) X) := (conjSqrt_conjSqrt_ringInverse A X hA).symm
    _ ≤ conjSqrt A (sqrt (conjSqrt (Ring.inverse A) B)) := by
        refine conjSqrt_monotone (CFC.le_sqrt_of_mul_self_le
          (hX.conjugate_self (sqrt_nonneg _).isSelfAdjoint) ?_)
        rw [CFC.conjSqrt_mul_self (Ring.inverse A) X hA.ringInverse.nonneg]
        exact conjSqrt_monotone (sub_nonneg.mp
          (ContinuousLinearMap.schurComplement_nonneg_of_block_quadForm_nonneg
            hA.isUnit hA.isSelfAdjoint hX hB.isSelfAdjoint h_block))
    _ = geometricMean A B := (geometricMean_def A B).symm

/-- **Joint operator concavity** of the geometric mean. For strictly positive `A₁, A₂` and
nonneg `B₁, B₂`, and `t, s : ℝ` with `0 ≤ t`, `0 ≤ s`, `t + s = 1`:
`t • M₀(A₁, B₁) + s • M₀(A₂, B₂) ≤ M₀(t • A₁ + s • A₂, t • B₁ + s • B₂)`.

Proof via maximality: `t • M₀(A₁, B₁) + s • M₀(A₂, B₂)` is in the block-PSD witness set for
the convex-combined `(t • A₁ + s • A₂, t • B₁ + s • B₂)` (linear combination of nonneg block
quadratic forms is nonneg); the le-direction `le_geometricMean_of_block_quadForm_nonneg`
discharges. -/
theorem geometricMean_concave
    {A₁ A₂ B₁ B₂ : E →L[ℂ] E} (hA₁ : IsStrictlyPositive A₁) (hA₂ : IsStrictlyPositive A₂)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    t • geometricMean A₁ B₁ + s • geometricMean A₂ B₂ ≤
      geometricMean (t • A₁ + s • A₂) (t • B₁ + s • B₂) := by
  refine le_geometricMean_of_block_quadForm_nonneg ?_ ?_ ?_ fun x y ↦ ?_
  · -- `t • A₁ + s • A₂` strictly positive: convex combination of strictly positives.
    exact convex_isStrictlyPositive hA₁ hA₂ ht hs hts
  · -- `t • B₁ + s • B₂` nonneg: nonneg + nonneg scaled by nonneg.
    exact add_nonneg (smul_nonneg ht hB₁) (smul_nonneg hs hB₂)
  · -- `t • M₀(A₁, B₁) + s • M₀(A₂, B₂)` self-adjoint: real-smul + sum of self-adjoints.
    exact ((IsSelfAdjoint.all t).smul (geometricMean_nonneg A₁ B₁).isSelfAdjoint).add
      ((IsSelfAdjoint.all s).smul (geometricMean_nonneg A₂ B₂).isSelfAdjoint)
  -- Block-quadratic form: linear combination of the two β.2 membership hypotheses.
  have h₁ := geometricMean_block_quadForm_nonneg hA₁ hB₁ x y
  have h₂ := geometricMean_block_quadForm_nonneg hA₂ hB₂ x y
  -- `T ↦ re ⟨z, T w⟩` is ℝ-linear in T (used 4× below).
  have key : ∀ (T₁ T₂ : E →L[ℂ] E) (z w : E),
      re (inner ℂ z ((t • T₁ + s • T₂) w)) =
        t * re (inner ℂ z (T₁ w)) + s * re (inner ℂ z (T₂ w)) := fun T₁ T₂ z w ↦ by
    change re (inner ℂ z ((t : ℂ) • T₁ w + (s : ℂ) • T₂ w)) = _
    rw [inner_add_right, map_add, inner_smul_right, inner_smul_right, mul_re, mul_re]
    simp
  rw [map_add, map_add, map_add] at h₁ h₂
  rw [map_add, map_add, map_add, key, key, key, key]
  nlinarith [mul_nonneg ht h₁, mul_nonneg hs h₂]

/-- **Monotonicity of the operator geometric mean**. For strictly positive `A ≤ A'` and
nonneg `B ≤ B'`, `M₀(A, B) ≤ M₀(A', B')`. Proof via maximality: `M₀(A, B)` is in the block-PSD
witness set for `(A, B)` (by `geometricMean_block_quadForm_nonneg`), and adding the nonneg
differences `re ⟨x, (A'-A)x⟩` and `re ⟨y, (B'-B)y⟩` keeps the block form nonneg at `(A', B')`;
`le_geometricMean_of_block_quadForm_nonneg` discharges. -/
theorem geometricMean_mono
    {A A' B B' : E →L[ℂ] E} (hA : IsStrictlyPositive A) (hA' : IsStrictlyPositive A')
    (hB : 0 ≤ B) (hB' : 0 ≤ B') (hAA' : A ≤ A') (hBB' : B ≤ B') :
    geometricMean A B ≤ geometricMean A' B' := by
  refine le_geometricMean_of_block_quadForm_nonneg hA' hB'
    (geometricMean_nonneg A B).isSelfAdjoint fun x y ↦ ?_
  have hAdiff : (A' - A).IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hAA')
  have hBdiff : (B' - B).IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hBB')
  have hA_eq : A' = A + (A' - A) := (add_sub_cancel A A').symm
  have hB_eq : B' = B + (B' - B) := (add_sub_cancel B B').symm
  have h_base := geometricMean_block_quadForm_nonneg hA hB x y
  rw [map_add, map_add, map_add] at h_base
  conv_rhs =>
    rw [hA_eq, hB_eq, add_apply, add_apply,
      inner_add_right, inner_add_right, map_add, map_add, map_add, map_add, map_add]
  linarith [hAdiff.re_inner_nonneg_right x, hBdiff.re_inner_nonneg_right y]

end Maximality

end CFC
