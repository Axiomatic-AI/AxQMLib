/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Additional API for inner product space tensor products

* `LinearMap.IsSymmetric.tensorMap`: the tensor product of symmetric linear maps is symmetric.
* `IsSelfAdjoint.tensorMap`: the tensor product of self-adjoint linear maps is self-adjoint.
* `TensorProduct.mapL`: the continuous linear map version of `TensorProduct.map` for finite-dim
  inner product spaces, together with its algebraic API (linearity, composition, adjoint,
  unitarity, Lie-bracket compatibility, joint continuity, etc).
* `TensorProduct.instCompleteSpace`: the tensor product of two finite-dimensional inner product
  spaces is complete.
* `TensorProduct.contractFst`: the partial inner product on the first tensor factor.
-/

@[expose] public section

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

open scoped TensorProduct

namespace TensorProduct

/-- The tensor product of two finite-dimensional inner product spaces is itself a complete
inner product space. Cannot be derived via `FiniteDimensional.completeSpace` as a global instance
because the latter has an ambiguous `𝕜` parameter; the type `E ⊗[𝕜] F` recovers `𝕜`
unambiguously for this specialization. -/
instance instCompleteSpace [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] :
    CompleteSpace (E ⊗[𝕜] F) := FiniteDimensional.completeSpace 𝕜 _

section isometry

@[simp] lemma congrIsometry_tmul (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) (a : E) (b : F) :
    congrIsometry f g (a ⊗ₜ[𝕜] b) = f a ⊗ₜ[𝕜] g b := rfl

end isometry

open LinearMap

/-- The tensor product of two symmetric linear maps is symmetric. -/
theorem _root_.LinearMap.IsSymmetric.tensorMap [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {B : F →ₗ[𝕜] F} (hB : B.IsSymmetric) :
    (TensorProduct.map A B).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint] at hA hB ⊢
  rw [LinearMap.isSelfAdjoint_iff'] at hA hB ⊢
  rw [TensorProduct.adjoint_map, hA, hB]

/-- The tensor product of two self-adjoint linear maps is self-adjoint. -/
theorem _root_.IsSelfAdjoint.tensorMap [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {A : E →ₗ[𝕜] E} (hA : IsSelfAdjoint A) {B : F →ₗ[𝕜] F} (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (TensorProduct.map A B) := by
  rw [LinearMap.isSelfAdjoint_iff'] at hA hB ⊢
  rw [TensorProduct.adjoint_map, hA, hB]

-- `TensorProduct.mapL`, `TensorProduct.mapL_apply`, and `TensorProduct.mapL_tmul` now exist
-- upstream in `Mathlib.Analysis.InnerProductSpace.TensorProduct` (more general: they do not
-- require `FiniteDimensional` hypotheses, only continuity of `f`/`g`). Use the upstream
-- declarations directly.

/-- The rank-one operator of two pure tensors factorizes through `mapL`:
`|a₁ ⊗ₜ b₁⟩⟨a₂ ⊗ₜ b₂| = mapL |a₁⟩⟨a₂| |b₁⟩⟨b₂|`. Checked on generators `x ⊗ₜ y` via `rankOne_apply`
and `inner_tmul`. The non-self generalization of `InnerProductSpace.rankOne_tmul_self`. -/
theorem _root_.InnerProductSpace.rankOne_tmul_tmul [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (a₁ a₂ : E) (b₁ b₂ : F) :
    (InnerProductSpace.rankOne 𝕜 (a₁ ⊗ₜ[𝕜] b₁) (a₂ ⊗ₜ[𝕜] b₂) : (E ⊗[𝕜] F) →L[𝕜] (E ⊗[𝕜] F))
      = mapL (InnerProductSpace.rankOne 𝕜 a₁ a₂) (InnerProductSpace.rankOne 𝕜 b₁ b₂) := by
  apply ContinuousLinearMap.coe_injective
  apply TensorProduct.ext'
  intro x y
  simp only [ContinuousLinearMap.coe_coe, mapL_apply, InnerProductSpace.rankOne_apply,
    inner_tmul, TensorProduct.map_tmul, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    mul_smul]
  rw [smul_comm]

/-- The rank-one operator of a pure tensor factorizes through `mapL`:
`|u ⊗ₜ v⟩⟨u ⊗ₜ v| = mapL |u⟩⟨u| |v⟩⟨v|`. The self case of
`InnerProductSpace.rankOne_tmul_tmul`. -/
theorem _root_.InnerProductSpace.rankOne_tmul_self [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (u : E) (v : F) :
    (InnerProductSpace.rankOne 𝕜 (u ⊗ₜ[𝕜] v) (u ⊗ₜ[𝕜] v) : (E ⊗[𝕜] F) →L[𝕜] (E ⊗[𝕜] F))
      = mapL (InnerProductSpace.rankOne 𝕜 u u) (InnerProductSpace.rankOne 𝕜 v v) :=
  InnerProductSpace.rankOne_tmul_tmul u u v v

/-- **Partial inner product on the first tensor factor.** For `v : E`, the linear map
`E ⊗[𝕜] F →ₗ[𝕜] F` sending `x ⊗ₜ y ↦ ⟪v, x⟫ • y` — contract the left factor of a tensor against
`v`. Built as `TensorProduct.lid ∘ (innerSL 𝕜 v).rTensor`; `contractFst_tmul` gives its action on
a pure tensor. -/
noncomputable def contractFst (v : E) : E ⊗[𝕜] F →ₗ[𝕜] F :=
  (TensorProduct.lid 𝕜 F).toLinearMap ∘ₗ LinearMap.rTensor F (innerSL 𝕜 v).toLinearMap

@[simp]
theorem contractFst_tmul (v x : E) (y : F) :
    contractFst v (x ⊗ₜ[𝕜] y) = (inner 𝕜 v x : 𝕜) • y := by
  simp [contractFst, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

-- `TensorProduct.mapL_mul` and `TensorProduct.mapL_comp` now exist upstream in
-- `Mathlib.Analysis.InnerProductSpace.TensorProduct` (more general: no `FiniteDimensional`
-- hypotheses needed). Use the upstream declarations directly.

/-- `mapL` of identity operators is the identity. CLM-level lift of `TensorProduct.map_one`. -/
@[simp]
theorem mapL_one [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] :
    mapL (1 : E →L[𝕜] E) (1 : F →L[𝕜] F) = 1 := by
  ext x
  simp [TensorProduct.map_one]

/-- `mapL · 1` is multiplicative: `mapL (f₁ * f₂) 1 = mapL f₁ 1 * mapL f₂ 1`, i.e. the left
embedding `f ↦ f ⊗ 1` is a monoid homomorphism. Specialisation of `mapL_mul` at `g₁ = g₂ = 1`. -/
theorem mapL_mul_one [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (f₁ f₂ : E →L[𝕜] E) :
    mapL (f₁ * f₂) (1 : F →L[𝕜] F) = mapL f₁ 1 * mapL f₂ 1 := by
  simpa using mapL_mul f₁ f₂ (1 : F →L[𝕜] F) 1

-- `TensorProduct.mapL_adjoint` now exists upstream as `TensorProduct.adjoint_mapL` (more general:
-- no `FiniteDimensional` hypotheses needed). Use the upstream declaration directly.

/-- The tensor product of two unitary operators is unitary: if `f` and `g` are unitary,
so is `mapL f g`. CLM-level lift combining `adjoint_mapL`, `mapL_mul`, and `mapL_one`. -/
theorem mapL_mem_unitary [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [CompleteSpace E] [CompleteSpace F]
    {f : E →L[𝕜] E} {g : F →L[𝕜] F}
    (hf : f ∈ unitary (E →L[𝕜] E)) (hg : g ∈ unitary (F →L[𝕜] F)) :
    mapL f g ∈ unitary (E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F) := by
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hf hg ⊢
  rw [adjoint_mapL]
  refine ⟨?_, ?_⟩
  · rw [← mapL_mul, hf.1, hg.1, mapL_one]
  · rw [← mapL_mul, hf.2, hg.2, mapL_one]

/-- The conjugate-square of a tensor-product map factors over the slots:
`(mapL f g)† ∘ mapL f g = mapL (f† ∘ f) (g† ∘ g)`. CLM-level lift combining `adjoint_mapL` and
`mapL_comp`; the building block for completeness of a tensor product of Kraus families. -/
theorem mapL_adjoint_comp_self [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H] [CompleteSpace E] [CompleteSpace F]
    [CompleteSpace G] [CompleteSpace H] (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    (mapL f g).adjoint ∘L mapL f g = mapL (f.adjoint ∘L f) (g.adjoint ∘L g) := by
  rw [adjoint_mapL, mapL_comp]

/-- Conjugating a tensor-product map by `mapL f g` factors over the slots:
`mapL f g ∘ mapL ρ σ ∘ (mapL f g)† = mapL (f ∘ ρ ∘ f†) (g ∘ σ ∘ g†)`. CLM-level lift combining
`adjoint_mapL` and `mapL_comp`; the Kraus action of a tensor-product operator on a product map. -/
theorem mapL_comp_self [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] [CompleteSpace H]
    (f : E →L[𝕜] F) (g : G →L[𝕜] H) (ρ : E →L[𝕜] E) (σ : G →L[𝕜] G) :
    mapL f g ∘L mapL ρ σ ∘L (mapL f g).adjoint
      = mapL (f ∘L ρ ∘L f.adjoint) (g ∘L σ ∘L g.adjoint) := by
  rw [adjoint_mapL, mapL_comp, mapL_comp]

-- `TensorProduct.mapL_add_left`, `mapL_zero_left`, `mapL_zero_right`, `mapL_add_right`,
-- `mapL_smul_left`, `mapL_smul_right` now exist upstream in
-- `Mathlib.Analysis.InnerProductSpace.TensorProduct` (more general: no `FiniteDimensional`
-- hypotheses needed). Use the upstream declarations directly.

/-- `mapL` negates in the first argument: `mapL (-f) g = -mapL f g`. -/
theorem mapL_neg_left [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL (-f) g = -mapL f g := by
  rw [← neg_one_smul 𝕜 f, mapL_smul_left, neg_one_smul]

/-- `mapL` negates in the second argument: `mapL f (-g) = -mapL f g`. -/
theorem mapL_neg_right [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL f (-g) = -mapL f g := by
  rw [← neg_one_smul 𝕜 g, mapL_smul_right, neg_one_smul]

/-- `mapL` is additive-subtractive in the first argument:
`mapL (f₁ - f₂) g = mapL f₁ g - mapL f₂ g`. -/
theorem mapL_sub_left [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f₁ f₂ : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL (f₁ - f₂) g = mapL f₁ g - mapL f₂ g := by
  rw [sub_eq_add_neg, mapL_add_left, mapL_neg_left, ← sub_eq_add_neg]

/-- `mapL` is additive-subtractive in the second argument:
`mapL f (g₁ - g₂) = mapL f g₁ - mapL f g₂`. -/
theorem mapL_sub_right [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f : E →L[𝕜] F) (g₁ g₂ : G →L[𝕜] H) :
    mapL f (g₁ - g₂) = mapL f g₁ - mapL f g₂ := by
  rw [sub_eq_add_neg, mapL_add_right, mapL_neg_right, ← sub_eq_add_neg]

/-- **The tensor square of a nonzero operator is nonzero**: for a finite-dimensional inner product
space `E` and `x : E →L[𝕜] E` with `x ≠ 0`, the tensor-product map `mapL x x ≠ 0`. Pick a witness
`v` with `x v ≠ 0`; then `mapL x x (v ⊗ₜ v) = x v ⊗ₜ x v` has norm `‖x v‖ * ‖x v‖ ≠ 0`, so the map
is nonzero. The finite-dimensional analogue over an inner product space of the "tensor of nonzero is
nonzero" fact for operators. -/
theorem mapL_self_ne_zero [FiniteDimensional 𝕜 E] {x : E →L[𝕜] E} (hx : x ≠ 0) :
    mapL x x ≠ 0 := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hx
  rw [_root_.zero_apply] at hv
  intro hzero
  refine hv (norm_eq_zero.mp (mul_self_eq_zero.mp ?_))
  rw [← norm_tmul (𝕜 := 𝕜), ← mapL_tmul, hzero, _root_.zero_apply, norm_zero]

/-- The factor-swap `commIsometry` on `E ⊗[𝕜] E` is an involution as a continuous linear map:
`commIsometry ∘ commIsometry = id`. -/
theorem commIsometry_comp_self :
    (commIsometry 𝕜 E E : E ⊗[𝕜] E →L[𝕜] E ⊗[𝕜] E).comp
        (commIsometry 𝕜 E E : E ⊗[𝕜] E →L[𝕜] E ⊗[𝕜] E) = 1 := by
  apply ContinuousLinearMap.coe_injective
  apply TensorProduct.ext'
  intro x y
  simp [commIsometry_apply, comm_tmul]

/-- Conjugating a tensor-product operator by the factor-swap `commIsometry` interchanges the two
factor operators: `commIsometry ∘ (A ⊗ B) ∘ commIsometry = B ⊗ A`, as continuous linear maps on
`E ⊗[𝕜] E`. This is the continuous-linear, isometric-swap form of the naturality of
`TensorProduct.comm` (`TensorProduct.map_comp_comm_eq`). -/
theorem commIsometry_conj_mapL [FiniteDimensional 𝕜 E] (A B : E →L[𝕜] E) :
    (commIsometry 𝕜 E E : E ⊗[𝕜] E →L[𝕜] E ⊗[𝕜] E).comp
        ((mapL A B).comp (commIsometry 𝕜 E E : E ⊗[𝕜] E →L[𝕜] E ⊗[𝕜] E))
      = mapL B A := by
  apply ContinuousLinearMap.coe_injective
  apply TensorProduct.ext'
  intro x y
  simp [commIsometry_apply, comm_tmul]

/-- Conjugating a tensor-product operator by the factor-swap `commIsometry` (as the `⋆`-algebra
equivalence `conjStarAlgEquiv`) interchanges the two factor operators:
`commIsometry.conjStarAlgEquiv (A ⊗ B) = B ⊗ A`, as continuous linear maps on `F ⊗[𝕜] E`. The
`conjStarAlgEquiv`, distinct-input-space companion of `commIsometry_conj_mapL`. -/
theorem commIsometry_conjStarAlgEquiv_mapL [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (A : E →L[𝕜] E) (B : F →L[𝕜] F) :
    (commIsometry 𝕜 E F).conjStarAlgEquiv (mapL A B) = mapL B A := by
  apply ContinuousLinearMap.coe_injective
  apply TensorProduct.ext'
  intro y x
  simp [commIsometry_apply, comm_tmul, commIsometry_symm]

/-- The Lie bracket of two left-embedded operators factors through `mapL`:
`⁅mapL f₁ 1, mapL f₂ 1⁆ = mapL ⁅f₁, f₂⁆ 1`. The left embedding `f ↦ f ⊗ 1` is a ring
homomorphism (`mapL_mul_one` + additivity), so it preserves the ring commutator. -/
theorem mapL_lie_left [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (f₁ f₂ : E →L[𝕜] E) :
    ⁅mapL f₁ (1 : F →L[𝕜] F), mapL f₂ (1 : F →L[𝕜] F)⁆ = mapL ⁅f₁, f₂⁆ 1 := by
  rw [Ring.lie_def, Ring.lie_def, ← mapL_mul_one, ← mapL_mul_one, ← mapL_sub_left]

/-- The Lie bracket of two right-embedded operators factors through `mapL`:
`⁅mapL 1 g₁, mapL 1 g₂⁆ = mapL 1 ⁅g₁, g₂⁆`. The right embedding `g ↦ 1 ⊗ g` is a ring
homomorphism (`mapL_mul` + additivity), so it preserves the ring commutator. -/
theorem mapL_lie_right [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (g₁ g₂ : F →L[𝕜] F) :
    ⁅mapL (1 : E →L[𝕜] E) g₁, mapL (1 : E →L[𝕜] E) g₂⁆ = mapL 1 ⁅g₁, g₂⁆ := by
  rw [Ring.lie_def, Ring.lie_def, ← mapL_mul, ← mapL_mul, ← mapL_sub_right, one_mul]

/-- `mapL` factors via two "tensor-by-identity" maps composed: `mapL f g = mapL f 1 ∘ mapL 1 g`.
CLM-level lift of `TensorProduct.map_comp` applied at the identity in opposite slots. -/
theorem mapL_factor [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL f g = (mapL f (1 : H →L[𝕜] H)).comp (mapL (1 : E →L[𝕜] E) g) := by
  refine ContinuousLinearMap.coe_injective (TensorProduct.ext' fun a b ↦ ?_)
  simp

/-- `mapL · 1` as a `LinearMap`: linear in the first argument (`mapL_add_left` +
`mapL_smul_left`). Scaffolding for `Continuous.mapL` (file-local). -/
private noncomputable def mapL_one_right_LM [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 H] :
    (E →L[𝕜] F) →ₗ[𝕜] (E ⊗[𝕜] H →L[𝕜] F ⊗[𝕜] H) where
  toFun f := mapL f (1 : H →L[𝕜] H)
  map_add' f₁ f₂ := mapL_add_left f₁ f₂ 1
  map_smul' c f := mapL_smul_left c f 1

/-- `mapL 1 ·` as a `LinearMap`: linear in the second argument. Scaffolding for
`Continuous.mapL` (file-local). -/
private noncomputable def mapL_one_left_LM [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] :
    (G →L[𝕜] H) →ₗ[𝕜] (E ⊗[𝕜] G →L[𝕜] E ⊗[𝕜] H) where
  toFun g := mapL (1 : E →L[𝕜] E) g
  map_add' g₁ g₂ := mapL_add_right 1 g₁ g₂
  map_smul' c g := mapL_smul_right c 1 g

/-- `mapL 1 ·` distributes over finite sums in the second argument:
`mapL 1 (∑ k, g k) = ∑ k, mapL 1 (g k)`. -/
theorem mapL_one_sum_right [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H]
    {n : Type*} [Fintype n] (g : n → (G →L[𝕜] H)) :
    mapL (1 : E →L[𝕜] E) (∑ k, g k) = ∑ k, mapL (1 : E →L[𝕜] E) (g k) :=
  map_sum (mapL_one_left_LM (E := E)) g Finset.univ

/-- `mapL · g` as a `LinearMap`: linear in the first argument (`mapL_add_left` +
`mapL_smul_left`). Scaffolding for `mapL_sum_left` (file-local). -/
private noncomputable def mapL_rightArg_LM [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H] (g : G →L[𝕜] H) :
    (E →L[𝕜] F) →ₗ[𝕜] (E ⊗[𝕜] G →L[𝕜] F ⊗[𝕜] H) where
  toFun f := mapL f g
  map_add' f₁ f₂ := mapL_add_left f₁ f₂ g
  map_smul' c f := mapL_smul_left c f g

/-- `mapL f ·` as a `LinearMap`: linear in the second argument (`mapL_add_right` +
`mapL_smul_right`). Scaffolding for `mapL_sum_right` (file-local). -/
private noncomputable def mapL_leftArg_LM [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H] (f : E →L[𝕜] F) :
    (G →L[𝕜] H) →ₗ[𝕜] (E ⊗[𝕜] G →L[𝕜] F ⊗[𝕜] H) where
  toFun g := mapL f g
  map_add' g₁ g₂ := mapL_add_right f g₁ g₂
  map_smul' c g := mapL_smul_right c f g

/-- `mapL` distributes over finite sums in the first argument:
`mapL (∑ k, A k) g = ∑ k, mapL (A k) g`. -/
theorem mapL_sum_left [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] {n : Type*} [Fintype n] (A : n → (E →L[𝕜] F)) (g : G →L[𝕜] H) :
    mapL (∑ k, A k) g = ∑ k, mapL (A k) g :=
  map_sum (mapL_rightArg_LM g) A Finset.univ

/-- `mapL` distributes over finite sums in the second argument:
`mapL f (∑ k, B k) = ∑ k, mapL f (B k)`. -/
theorem mapL_sum_right [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] {n : Type*} [Fintype n] (f : E →L[𝕜] F) (B : n → (G →L[𝕜] H)) :
    mapL f (∑ k, B k) = ∑ k, mapL f (B k) :=
  map_sum (mapL_leftArg_LM f) B Finset.univ

/-- **Joint continuity of `mapL`**: for continuous `f : β → E →L[𝕜] F` and `g : β → G →L[𝕜] H`
(`β` topological, all spaces finite-dim), `b ↦ mapL (f b) (g b)` is continuous. Proof via the
factorization `mapL f g = mapL f 1 ∘ mapL 1 g`: the two factors are linear-in-one-arg, hence
continuous in finite-dim; their composition is jointly continuous bilinear via
`isBoundedBilinearMap_comp`. -/
theorem _root_.Continuous.mapL [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H]
    {β : Type*} [TopologicalSpace β]
    {f : β → E →L[𝕜] F} {g : β → G →L[𝕜] H}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun b ↦ TensorProduct.mapL (f b) (g b)) :=
  (isBoundedBilinearMap_comp.continuous.comp (Continuous.prodMk
    ((TensorProduct.mapL_one_right_LM (E := E) (F := F) (H := H)
      (𝕜 := 𝕜)).continuous_of_finiteDimensional.comp hf)
    ((TensorProduct.mapL_one_left_LM (E := E) (G := G) (H := H)
      (𝕜 := 𝕜)).continuous_of_finiteDimensional.comp hg))).congr
    fun b ↦ (TensorProduct.mapL_factor (f b) (g b)).symm

end TensorProduct
