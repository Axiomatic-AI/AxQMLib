/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Composite
import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM.Postulates.API — the product eigenbasis of a tensor-product state

A single reusable fact: if orthonormal bases `b₁`, `b₂` diagonalize the density
operators `ρ.op`, `σ.op` with real eigenvalues `p`, `q`, then their tensor product diagonalizes the
composite operator `(ρ ⊗ σ).op = ρ.op ⊗ σ.op` with the *product* eigenvalues `(i, j) ↦ p i · q j`.

This is the basic step in every "spectrum of a tensor-product state" computation (the
tensor of the reduced-state eigenvalues).
-/

namespace AxQM

variable {S T : QSystem}

/-- **The tensor of two eigenbases diagonalizes the tensor-product state.** If `b₁` diagonalizes
`ρ.op` with real eigenvalues `p` (`ρ.op (b₁ i) = p i • b₁ i`) and `b₂` diagonalizes `σ.op` with real
eigenvalues `q`, then `b₁.tensorProduct b₂` is an eigenbasis of `(ρ ⊗ σ).op` with eigenvalue
`(i, j) ↦ p i · q j` on the basis vector `b₁ i ⊗ b₂ j`.

Since `(ρ ⊗ σ).op` is definitionally `TensorProduct.mapL ρ.op σ.op` (`State.tmul_op`), the goal is
re-presented at the native `TensorProduct ℂ S.space T.space` type, where `TensorProduct.mapL_tmul`
factors the action across the tensor and the two eigenvalue equations combine via
`TensorProduct.smul_tmul_smul`. -/
theorem State.tmul_op_tensorProduct_apply_self {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ρ : State S) (σ : State T) (b₁ : OrthonormalBasis ι ℂ S.space)
    (b₂ : OrthonormalBasis κ ℂ T.space) {p : ι → ℝ} {q : κ → ℝ}
    (hp : ∀ i, ρ.op (b₁ i) = (p i : ℂ) • b₁ i) (hq : ∀ j, σ.op (b₂ j) = (q j : ℂ) • b₂ j)
    (ij : ι × κ) :
    (ρ.tmul σ).op ((b₁.tensorProduct b₂) ij)
      = ((p ij.1 * q ij.2 : ℝ) : ℂ) • (b₁.tensorProduct b₂) ij := by
  change (TensorProduct.mapL ρ.op σ.op) ((b₁.tensorProduct b₂) ij)
      = ((p ij.1 * q ij.2 : ℝ) : ℂ) • (b₁.tensorProduct b₂) ij
  rw [OrthonormalBasis.tensorProduct_apply', TensorProduct.mapL_tmul, hp, hq,
    TensorProduct.smul_tmul_smul, ← Complex.ofReal_mul]

end AxQM
