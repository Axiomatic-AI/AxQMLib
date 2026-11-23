/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Extra `TensorProduct.map` lemmas

Extends `Mathlib.LinearAlgebra.TensorProduct.Map` with `TensorProduct.map_sum_left` (`map`
is additive in its first argument over a finite sum) and `LinearEquiv.rTensor_comp_map_comp_symm`
(conjugating a product map by an `rTensor` equivalence rewrites its first factor).
-/

public section

namespace TensorProduct

variable {R R₂ : Type*} [CommSemiring R] [CommSemiring R₂] {σ₁₂ : R →+* R₂}
variable {M N M₂ N₂ : Type*} [AddCommMonoid M] [AddCommMonoid N]
variable [AddCommMonoid M₂] [AddCommMonoid N₂]
variable [Module R M] [Module R N] [Module R₂ M₂] [Module R₂ N₂]

theorem map_sum_left {ι : Type*} (s : Finset ι) (f : ι → (M →ₛₗ[σ₁₂] M₂)) (g : N →ₛₗ[σ₁₂] N₂) :
    map (∑ i ∈ s, f i) g = ∑ i ∈ s, map (f i) g := by
  simpa only [mapBilinear_apply, LinearMap.sum_apply] using
    LinearMap.congr_fun (_root_.map_sum (mapBilinear σ₁₂ M N M₂ N₂) f s) g

end TensorProduct

namespace LinearEquiv

variable {R : Type*} [CommSemiring R]
variable {M N P : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module R N] [Module R P]
variable (f : N ≃ₗ[R] P)

/-- Conjugating a product map `B ⊗ C` by the first-factor equivalence `f.rTensor M = f ⊗ id`
rewrites its first factor: `(f.rTensor M) ∘ (B ⊗ C) ∘ (f.rTensor M)⁻¹ = (f ∘ B ∘ f⁻¹) ⊗ C`. The
second factor `C` is left untouched. -/
theorem rTensor_comp_map_comp_symm (B : N →ₗ[R] N) (C : M →ₗ[R] M) :
    (f.rTensor M).toLinearMap ∘ₗ TensorProduct.map B C ∘ₗ (f.rTensor M).symm.toLinearMap
      = TensorProduct.map ((f : N →ₗ[R] P) ∘ₗ B ∘ₗ (f.symm : P →ₗ[R] N)) C := by
  refine TensorProduct.ext' fun p c => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_rTensor,
      TensorProduct.map_tmul,
    rTensor_tmul]

end LinearEquiv
