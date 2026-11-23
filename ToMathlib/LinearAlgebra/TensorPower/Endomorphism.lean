/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Tensor power of an endomorphism

For an endomorphism `A : M →ₗ[R] M`, this file defines its `n`-fold tensor power
`LinearMap.tensorPow A n : ⨂[R]^n M →ₗ[R] ⨂[R]^n M`, acting on `⨂[R]^n M` by
applying `A` in each factor. We provide the notation `A ^⊗ n` for it.

This is the special case of `PiTensorProduct.map` for the constant family `fun _ ↦ A`.

## Main definitions

* `LinearMap.tensorPow A n`: the `n`-fold tensor power of `A`, with notation `A ^⊗ n`.

## Main results

* `LinearMap.tensorPow_eq_map`: the rfl-form `A ^⊗ n = PiTensorProduct.map (fun _ ↦ A)`,
  exposed as `@[simp]` so proofs can reach through `tensorPow` automatically.
* `LinearMap.tensorPow_apply_tprod`: `(A ^⊗ n) (tprod R v) = tprod R (fun i ↦ A (v i))`.
* `LinearMap.tensorPow_zero`, `LinearMap.tensorPow_id`: `A ^⊗ 0 = id` and `id ^⊗ n = id`.
* `LinearMap.tensorPow_comp`: `(A ∘ₗ B) ^⊗ n = A ^⊗ n ∘ₗ B ^⊗ n`.

## Implementation notes

The operator-equality forms involving canonical isomorphisms (`tensorPow_one` via the
`PiTensorProduct.subsingletonEquiv` for `Fin 1`, `tensorPow_succ` via
`TensorPower.mulEquiv`) are not formalised here; the `tprod`-applied form
`tensorPow_apply_tprod` covers the common uses.
-/

@[expose] public section

open scoped TensorProduct

namespace LinearMap

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The `n`-fold tensor power of an endomorphism `A : M →ₗ[R] M`, acting on
`⨂[R]^n M` by applying `A` in each factor. -/
noncomputable def tensorPow (A : M →ₗ[R] M) (n : ℕ) :
    (⨂[R]^n) M →ₗ[R] (⨂[R]^n) M :=
  PiTensorProduct.map (fun (_ : Fin n) ↦ A)

@[inherit_doc] notation:max A " ^⊗ " n:arg => LinearMap.tensorPow A n

@[simp] theorem tensorPow_eq_map (A : M →ₗ[R] M) (n : ℕ) :
    A ^⊗ n = PiTensorProduct.map (fun (_ : Fin n) ↦ A) := rfl

@[simp] theorem tensorPow_apply_tprod (A : M →ₗ[R] M) {n : ℕ} (v : Fin n → M) :
    (A ^⊗ n) (PiTensorProduct.tprod R v) = PiTensorProduct.tprod R (fun i ↦ A (v i)) := by
  simp

@[simp] theorem tensorPow_zero (A : M →ₗ[R] M) :
    A ^⊗ 0 = LinearMap.id := by
  rw [tensorPow_eq_map, Subsingleton.elim (fun (_ : Fin 0) ↦ A) (fun _ ↦ LinearMap.id)]
  exact PiTensorProduct.map_id

@[simp] theorem tensorPow_id (n : ℕ) :
    (LinearMap.id : M →ₗ[R] M) ^⊗ n = LinearMap.id := by
  rw [tensorPow_eq_map]
  exact PiTensorProduct.map_id

theorem tensorPow_comp (A B : M →ₗ[R] M) (n : ℕ) :
    (A ∘ₗ B) ^⊗ n = A ^⊗ n ∘ₗ B ^⊗ n := by
  rw [tensorPow_eq_map, tensorPow_eq_map, tensorPow_eq_map]
  exact PiTensorProduct.map_comp _ _

end LinearMap
