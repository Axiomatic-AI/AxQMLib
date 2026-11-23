/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# AxQM.Concrete — scalar pull-through for threefold tensors

Six elementary module-algebra facts that pull the scalars off individual factors of a threefold
tensor `x ⊗ (y ⊗ z)` out to the front, the threefold companions of `TensorProduct.smul_tmul_smul`.
They are pure `TensorProduct` scalar algebra over an arbitrary commutative
ring. Position-explicit names spell out which slots carry a
scalar (`smul`) versus which are plain (`tmul`):

* `smul_tmul_smul_tmul_left` / `tmul_smul_tmul_smul_right` — scalars on the first two / last two
  factors, used to evaluate `Z ⊗ Z ⊗ I` / `I ⊗ Z ⊗ Z` on a three-qubit computational-basis ket;
* `smul_tmul_tmul` / `tmul_smul_tmul` / `tmul_tmul_smul` — a scalar on the first / middle / last
  factor only, used to evaluate a single Pauli `Z` placed as `Z ⊗ I ⊗ I` / `I ⊗ Z ⊗ I` /
  `I ⊗ I ⊗ Z`;
* `smul_tmul_smul_tmul_smul` — scalars on all three factors, used to evaluate `Z ⊗ Z ⊗ Z`.
-/

open scoped TensorProduct

namespace AxQM.Concrete

variable {R E F G : Type*} [CommRing R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [AddCommGroup G] [Module R G]

/-- Scalar extraction for a threefold tensor with scalars on the **first two** factors:
`(c₁ • x) ⊗ (c₂ • y) ⊗ z = (c₁ c₂) • (x ⊗ y ⊗ z)`. -/
theorem smul_tmul_smul_tmul_left (c1 c2 : R) (x : E) (y : F) (z : G) :
    (c1 • x) ⊗ₜ[R] ((c2 • y) ⊗ₜ[R] z) = (c1 * c2) • (x ⊗ₜ[R] (y ⊗ₜ[R] z)) := by
  rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]

/-- Scalar extraction for a threefold tensor with scalars on the **last two** factors:
`x ⊗ (c₂ • y) ⊗ (c₃ • z) = (c₂ c₃) • (x ⊗ y ⊗ z)`. -/
theorem tmul_smul_tmul_smul_right (c2 c3 : R) (x : E) (y : F) (z : G) :
    x ⊗ₜ[R] ((c2 • y) ⊗ₜ[R] (c3 • z)) = (c2 * c3) • (x ⊗ₜ[R] (y ⊗ₜ[R] z)) := by
  rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.tmul_smul,
    TensorProduct.tmul_smul, smul_smul]

/-- Scalar extraction for a threefold tensor with a scalar on the **first** factor only:
`(c • x) ⊗ (y ⊗ z) = c • (x ⊗ y ⊗ z)`. Named position-explicitly (`smul` in the first slot,
`tmul` in the other two), matching the structure-mirroring convention of the two-scalar siblings. -/
theorem smul_tmul_tmul (c : R) (x : E) (y : F) (z : G) :
    (c • x) ⊗ₜ[R] (y ⊗ₜ[R] z) = c • (x ⊗ₜ[R] (y ⊗ₜ[R] z)) :=
  (TensorProduct.smul_tmul' c x _).symm

/-- Scalar extraction for a threefold tensor with a scalar on the **middle** factor only:
`x ⊗ (c • y) ⊗ z = c • (x ⊗ y ⊗ z)`. Named position-explicitly (`smul` in the middle slot). -/
theorem tmul_smul_tmul (c : R) (x : E) (y : F) (z : G) :
    x ⊗ₜ[R] ((c • y) ⊗ₜ[R] z) = c • (x ⊗ₜ[R] (y ⊗ₜ[R] z)) := by
  rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul]

/-- Scalar extraction for a threefold tensor with a scalar on the **last** factor only:
`x ⊗ (y ⊗ (c • z)) = c • (x ⊗ y ⊗ z)`. Named position-explicitly (`smul` in the last slot). -/
theorem tmul_tmul_smul (c : R) (x : E) (y : F) (z : G) :
    x ⊗ₜ[R] (y ⊗ₜ[R] (c • z)) = c • (x ⊗ₜ[R] (y ⊗ₜ[R] z)) := by
  rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul]

/-- Scalar extraction for a threefold tensor with a scalar on **all three** factors:
`(c₁ • x) ⊗ (c₂ • y) ⊗ (c₃ • z) = (c₁ c₂ c₃) • (x ⊗ y ⊗ z)`. -/
theorem smul_tmul_smul_tmul_smul (c1 c2 c3 : R) (x : E) (y : F) (z : G) :
    (c1 • x) ⊗ₜ[R] ((c2 • y) ⊗ₜ[R] (c3 • z)) = (c1 * c2 * c3) • (x ⊗ₜ[R] (y ⊗ₜ[R] z)) := by
  rw [TensorProduct.smul_tmul_smul, TensorProduct.smul_tmul_smul, mul_assoc]

end AxQM.Concrete
