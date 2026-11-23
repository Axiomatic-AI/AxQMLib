/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliEigenvectors
import ToMathlib.Analysis.InnerProductSpace.TensorProduct
import ToMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Concrete: the Bell vector `(|00⟩ + |11⟩)/√2` is not a simple tensor

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 2.68 (p. 96)
concerns the two-qubit state `|ψ⟩ = (|00⟩ + |11⟩)/√2` (equation 2.132) and asks to show
it is **not** a product `|a⟩|b⟩` of single-qubit states — the archetypal *entangled* state.

This file supplies the pure linear-algebra core over
`ℂ² ⊗ ℂ² = EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)`:

* `bellVector` — the vector `(1/√2)·(|0⟩⊗|0⟩ + |1⟩⊗|1⟩)` in the abstract tensor product.
* `bellVector_ne_tmul` — it is **not a simple tensor**: `bellVector ≠ a ⊗ₜ b` for *every*
  pair of vectors `a, b : ℂ²` (not merely unit vectors). This is the concrete content of the
  exercise. For the normalised `PureState` `bellPhiPlus`, `bellPhiPlus.vec` is
  definitionally `bellVector` (both are `(√2)⁻¹ • (|00⟩ + |11⟩)`), so
  `AxQM/NC/Ch2/Exercise2_68.lean` reduces the physics claim to this lemma.

## Design notes

The Bell vector is built in the **abstract** tensor product `⊗[ℂ]` (via `⊗ₜ`), not the raw
index-vector Kronecker form used elsewhere in `Concrete/`, matching
`bellPhiPlus.vec = (√2)⁻¹ • bellVec`. Working over the *raw* underlying type (rather than the
composite `(qubit ⊗ qubit).space`) lets the inner-product expansion lemmas fire directly, with
no head-mismatch `change` needed.

Non-factorizability is proved by the standard coefficient argument. Pairing the vector against
the four product basis kets `|i⟩⊗|j⟩` with the inner product reads off its coefficients: for a
simple tensor `a ⊗ₜ b` the `(i,j)` coefficient is `aᵢ·bⱼ` (`TensorProduct.inner_tmul`), while for
`bellVector` it is `1/√2` on the diagonal and `0` off it. Equality would force
`a₀b₁ = 0` (so `b₁ = 0`, since `a₀b₀ = 1/√2 ≠ 0`) yet `a₁b₁ = 1/√2 ≠ 0` — a contradiction.
-/

namespace AxQM.Concrete

open scoped TensorProduct

/-- The **Bell vector** `(|00⟩ + |11⟩)/√2` (Nielsen & Chuang eq. 2.132), as a vector of the
abstract tensor product `ℂ² ⊗ ℂ²`. Here `|i⟩ = EuclideanSpace.single i 1` is the `i`-th
computational basis ket, so `|0⟩⊗|0⟩` and `|1⟩⊗|1⟩` are the diagonal product basis kets. This is
definitionally the state vector `bellPhiPlus.vec` of the Bell state. -/
noncomputable def bellVector :
    EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) :=
  invSqrt2 • (EuclideanSpace.single 0 (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single 0 (1 : ℂ)
    + EuclideanSpace.single 1 (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single 1 (1 : ℂ))

/-- **Exercise 2.68 (concrete core): the Bell vector is not a simple tensor.** For *every* pair
`a, b : ℂ²`, `bellVector ≠ a ⊗ₜ b`. Hence `(|00⟩ + |11⟩)/√2` is not a product `|a⟩|b⟩` — it is
entangled. -/
theorem bellVector_ne_tmul (a b : EuclideanSpace ℂ (Fin 2)) :
    bellVector ≠ a ⊗ₜ[ℂ] b := by
  intro h
  -- The `(i,j)` coefficient of `a ⊗ₜ b`, read by pairing with `|i⟩⊗|j⟩`, is `aᵢ·bⱼ`.
  have key : ∀ i j : Fin 2,
      inner ℂ (EuclideanSpace.single i (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single j (1 : ℂ)) bellVector
        = a i * b j := by
    intro i j
    rw [h, TensorProduct.inner_tmul, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_left]
    simp
  -- The same coefficient of `bellVector` is `1/√2` on the diagonal, `0` off it.
  have coeff : ∀ i j : Fin 2,
      inner ℂ (EuclideanSpace.single i (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single j (1 : ℂ)) bellVector
        = invSqrt2 * ((if i = 0 then (1 : ℂ) else 0) * (if j = 0 then 1 else 0)
            + (if i = 1 then 1 else 0) * (if j = 1 then 1 else 0)) := by
    intro i j
    rw [bellVector, inner_smul_right, inner_add_right, TensorProduct.inner_tmul,
      TensorProduct.inner_tmul, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_left, PiLp.single_apply, PiLp.single_apply,
      PiLp.single_apply, PiLp.single_apply]
    simp
  -- The three coefficient equations we need: `aᵢ·bⱼ = bell coefficient`.
  have e00 : a 0 * b 0 = invSqrt2 := by simpa using (key 0 0).symm.trans (coeff 0 0)
  have e01 : a 0 * b 1 = 0 := by simpa using (key 0 1).symm.trans (coeff 0 1)
  have e11 : a 1 * b 1 = invSqrt2 := by simpa using (key 1 1).symm.trans (coeff 1 1)
  -- `a₀b₀ = 1/√2 ≠ 0`, so `a₀ ≠ 0`; then `a₀b₁ = 0` forces `b₁ = 0`, so `a₁b₁ = 0 ≠ 1/√2`.
  have ha0 : a 0 ≠ 0 := fun h0 => invSqrt2_ne_zero (by rw [← e00, h0, zero_mul])
  have hb1 : b 1 = 0 := (mul_eq_zero.mp e01).resolve_left ha0
  exact invSqrt2_ne_zero (by rw [← e11, hb1, mul_zero])

end AxQM.Concrete
