/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Positive
public import ToMathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Schur complement at the linear-map level

For an invertible self-adjoint operator `A` on an inner product space, and self-adjoint operators
`X, B`, the Schur complement of the hermitian block `[[A, X], [X, B]]` is `B - X · A⁻¹ · X`.
This file proves the forward direction of the Schur complement positivity criterion: if the block
quadratic form is nonneg, then the Schur complement is positive semidefinite (`IsPositive`).

This is the LinearMap-level analog of `Matrix.PosDef.fromBlocks₁₁` (which requires a CommRing of
matrix entries); the present lemma works on any inner product space.

## Main results

* `LinearMap.IsSymmetric.ringInverse` — the ring inverse of a self-adjoint invertible operator is
  self-adjoint.
* `LinearMap.schurComplement_isPositive_of_block_quadForm_nonneg` — Carlen Lemma 3.2 (forward
  direction): block PSD ⇒ Schur complement PSD.
* `ContinuousLinearMap.schurComplement_nonneg_of_block_quadForm_nonneg` — CLM-level lift via the
  CLM↔LM ring iso in finite dimensions.
-/

namespace LinearMap

open RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

@[expose] public section SchurComplement

/-- For an invertible operator `A`, `A (Ring.inverse A z) = z`. -/
private lemma apply_ringInverse {A : E →ₗ[𝕜] E} (hAu : IsUnit A) (z : E) :
    A (Ring.inverse A z) = z :=
  (LinearMap.congr_fun (Ring.mul_inverse_cancel A hAu) z).trans (one_apply_eq_self _)

/-- The ring inverse of an invertible self-adjoint operator is self-adjoint. -/
lemma IsSymmetric.ringInverse {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hAu : IsUnit A) :
    (Ring.inverse A).IsSymmetric := fun x y ↦ by
  conv_lhs => rw [← apply_ringInverse hAu y]
  rw [← hA, apply_ringInverse hAu]

/-- **Schur complement, forward direction**: if the hermitian block operator `[[A, X], [X, B]]`
(with `A` invertible self-adjoint, `X` self-adjoint, `B` self-adjoint) is positive semidefinite
as a quadratic form on `E × E`, then the Schur complement `B - X · A⁻¹ · X` is positive
semidefinite.

Forward direction of Carlen Lemma 3.2 at the linear-map level on an inner product space; the
substitution `(x, y) ↦ (-(A⁻¹ X y), y)` reduces the block quadratic form to the Schur
complement's quadratic form. -/
lemma schurComplement_isPositive_of_block_quadForm_nonneg
    {A : E →ₗ[𝕜] E} (hAu : IsUnit A) (hA : A.IsSymmetric)
    {X B : E →ₗ[𝕜] E} (hX : X.IsSymmetric) (hB : B.IsSymmetric)
    (h_block : ∀ x y : E,
        0 ≤ re (inner 𝕜 x (A x) + inner 𝕜 x (X y) + inner 𝕜 y (X x) + inner 𝕜 y (B y))) :
    (B - X ∘ₗ Ring.inverse A ∘ₗ X).IsPositive := by
  have hA_inv : (Ring.inverse A).IsSymmetric := hA.ringInverse hAu
  refine ⟨fun u v ↦ ?_, fun y ↦ ?_⟩
  · -- Symmetry of `B - X · A⁻¹ · X`.
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_left, inner_sub_right]
    rw [hB, hX, hA_inv, hX]
  · -- Nonnegativity: substitute `(x, y) ↦ (-(A⁻¹ X y), y)`; cross terms cancel.
    have key := h_block (-(Ring.inverse A) (X y)) y
    simp only [map_neg, inner_neg_left, inner_neg_right, apply_ringInverse hAu, neg_neg,
      LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_left, map_sub, map_add] at key ⊢
    rw [inner_re_symm (B y) y, inner_re_symm (X (Ring.inverse A (X y))) y]
    linarith [key]

end SchurComplement

end LinearMap

namespace ContinuousLinearMap

open RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [FiniteDimensional 𝕜 E]

@[expose] public section SchurComplement

/-- **CLM-level forward Schur complement**: thin lift of the LM-level
`LinearMap.schurComplement_isPositive_of_block_quadForm_nonneg` to the CLM C⋆-order. In finite
dimensions the ring homomorphism `(· : E →L[𝕜] E) → (E →ₗ[𝕜] E)` is a ring isomorphism, so
`IsUnit`, `Ring.inverse`, and `IsPositive` transport across it faithfully. -/
theorem schurComplement_nonneg_of_block_quadForm_nonneg
    {A : E →L[𝕜] E} (hAu : IsUnit A) (hA : IsSelfAdjoint A)
    {X B : E →L[𝕜] E} (hX : IsSelfAdjoint X) (hB : IsSelfAdjoint B)
    (h_block : ∀ x y : E,
        0 ≤ re (inner 𝕜 x (A x) + inner 𝕜 x (X y) + inner 𝕜 y (X x) + inner 𝕜 y (B y))) :
    0 ≤ B - X * Ring.inverse A * X := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive,
    ← ContinuousLinearMap.isPositive_toLinearMap_iff]
  simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_mul,
    ContinuousLinearMap.coe_ringInverse]
  exact LinearMap.schurComplement_isPositive_of_block_quadForm_nonneg
    (hAu.map ContinuousLinearMap.toLinearMapRingHom)
    hA.isSymmetric hX.isSymmetric hB.isSymmetric h_block

end SchurComplement

end ContinuousLinearMap
