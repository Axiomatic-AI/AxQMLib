/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.PiTensorProduct
public import ToMathlib.Analysis.InnerProductSpace.Trace

/-!
# The n-ary tensor map on inner product spaces and its adjoint

For a finite family of continuous linear maps `f i : E i →L[𝕜] E' i` between finite-dimensional
inner product spaces, `PiTensorProduct.mapCLM f : (⨂ᵢ Eᵢ) →L[𝕜] ⨂ᵢ E'ᵢ` is the induced
continuous linear map, `⨂ aᵢ ↦ ⨂ (f i) aᵢ`.

This is the **inner-product-native** companion of `PiTensorProduct.mapL` (which lives on the
projective-seminorm normed structure): built as the finite-dimensional `.toContinuousLinearMap`
of the algebraic `PiTensorProduct.map`, it lands on the inner-product `NormedAddCommGroup`
instance, so it is compatible with `ContinuousLinearMap.adjoint` / the tensor inner product —
avoiding the norm-instance diamond between the two structures.

## Main results

* `PiTensorProduct.mapCLM` — the induced continuous linear map.
* `PiTensorProduct.mapCLM_adjoint` — `(mapCLM f)† = mapCLM (fun i ↦ (f i)†)`.
* `PiTensorProduct.mapCLM_trace` — `Tr (mapCLM f) = ∏ᵢ Tr (f i)`.
* `PiTensorProduct.reindexₗᵢ_mapCLM` — naturality of `mapCLM` under reindexing.
-/

@[expose] public section

namespace PiTensorProduct

open scoped TensorProduct InnerProductSpace

variable {ι : Type*} [Finite ι] {𝕜 : Type*} [RCLike 𝕜]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
    [∀ i, FiniteDimensional 𝕜 (E i)]

instance instFiniteDimensionalPiTensor : FiniteDimensional 𝕜 (⨂[𝕜] i, E i) :=
  Module.Basis.finiteDimensional_of_finite (Basis.piTensorProduct fun i ↦ Module.finBasis 𝕜 (E i))

instance instCompleteSpacePiTensor : CompleteSpace (⨂[𝕜] i, E i) :=
  FiniteDimensional.completeSpace 𝕜 _

variable {E' : ι → Type*} [∀ i, NormedAddCommGroup (E' i)] [∀ i, InnerProductSpace 𝕜 (E' i)]
  [∀ i, FiniteDimensional 𝕜 (E' i)]

/-- **The n-ary tensor map** `⨂ aᵢ ↦ ⨂ (f i) aᵢ` as a continuous linear map on the
inner-product tensor products. The finite-dimensional `.toContinuousLinearMap` of the algebraic
`PiTensorProduct.map`; lives on the inner-product normed structure (unlike `PiTensorProduct.mapL`,
which uses the projective seminorm). -/
noncomputable def mapCLM (f : ∀ i, E i →L[𝕜] E' i) : (⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i :=
  LinearMap.toContinuousLinearMap (PiTensorProduct.map fun i ↦ (f i : E i →ₗ[𝕜] E' i))

omit [∀ i, FiniteDimensional 𝕜 (E' i)] in
@[simp]
theorem mapCLM_tprod (f : ∀ i, E i →L[𝕜] E' i) (x : ∀ i, E i) :
    mapCLM f (⨂ₜ[𝕜] i, x i) = ⨂ₜ[𝕜] i, f i (x i) := by
  simp [mapCLM, PiTensorProduct.map_tprod]

@[simp]
theorem mapCLM_id :
    mapCLM (fun i ↦ ContinuousLinearMap.id 𝕜 (E i)) = ContinuousLinearMap.id 𝕜 (⨂[𝕜] i, E i) := by
  ext x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a => simp
  | add x y hx hy => simp [hx, hy]

/-- **The adjoint of the n-ary tensor map is the n-ary tensor map of the adjoints:**
`(mapCLM f)† = mapCLM (fun i ↦ (f i)†)`. Verified on elementary tensors via the multiplicativity
of the tensor inner product (`inner_tprod_tprod`) and the defining property of each factor's
adjoint. -/
theorem mapCLM_adjoint [∀ i, CompleteSpace (E i)] [∀ i, CompleteSpace (E' i)]
    (f : ∀ i, E i →L[𝕜] E' i) :
    ContinuousLinearMap.adjoint (mapCLM f) =
      mapCLM (fun i ↦ ContinuousLinearMap.adjoint (f i)) := by
  have := Fintype.ofFinite ι
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y ↦ ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      simp only [map_smul, inner_smul_left, inner_smul_right, mapCLM_tprod, inner_tprod_tprod]
      congr 2
      exact Finset.prod_congr rfl fun i _ ↦
        ContinuousLinearMap.adjoint_inner_left (f i) (b i) (a i)
    | add y₁ y₂ hy₁ hy₂ => simp only [map_add, inner_add_right, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, inner_add_left, hx₁, hx₂]

/-- **The trace of the n-ary tensor map is the product of the factor traces:**
`Tr (mapCLM f) = ∏ᵢ Tr (f i)`. Computed in the tensor-product orthonormal basis
(`OrthonormalBasis.piTensorProduct`) via `inner_tprod_tprod` and the product-of-sums expansion
`Finset.prod_univ_sum`. -/
-- `[Fintype ι]` (rather than the file's `[Finite ι]` + `Fintype.ofFinite ι`): the `∏ i` in the
-- statement needs it at elaboration time, and the `Fintype.ofFinite` route yields a noncomputable
-- `Fintype` that blocks synthesis of `DecidableEq ι` / `Fintype (∀ i, Fin _)` in the proof.
theorem mapCLM_trace [Fintype ι] (f : ∀ i, E i →L[𝕜] E i) :
    LinearMap.trace 𝕜 (⨂[𝕜] i, E i) (mapCLM f).toLinearMap =
      ∏ i, LinearMap.trace 𝕜 (E i) (f i).toLinearMap := by
  classical
  rw [LinearMap.trace_eq_sum_inner _
    (OrthonormalBasis.piTensorProduct fun i ↦ stdOrthonormalBasis 𝕜 (E i))]
  simp_rw [fun i ↦ LinearMap.trace_eq_sum_inner (f i).toLinearMap (stdOrthonormalBasis 𝕜 (E i))]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr Fintype.piFinset_univ.symm fun p _ ↦ ?_
  rw [OrthonormalBasis.piTensorProduct_apply, ContinuousLinearMap.coe_coe, mapCLM_tprod,
    inner_tprod_tprod]
  simp only [ContinuousLinearMap.coe_coe]

omit [∀ i, FiniteDimensional 𝕜 (E' i)] in
/-- **Naturality of `mapCLM` under reindexing**: reindexing the tensor factors intertwines the
tensor maps, `reindexₗᵢ e (mapCLM f x) = mapCLM (fun j ↦ f (e.symm j)) (reindexₗᵢ e x)`. The
inner-product-native (`mapCLM`/`reindexₗᵢ`) analogue of the algebraic
`PiTensorProduct.map_comp_reindex_eq`. -/
theorem reindexₗᵢ_mapCLM {κ : Type*} [Finite κ] (e : ι ≃ κ) (f : ∀ i, E i →L[𝕜] E' i)
    (x : ⨂[𝕜] i, E i) :
    reindexₗᵢ 𝕜 E' e (mapCLM f x) = mapCLM (fun j ↦ f (e.symm j)) (reindexₗᵢ 𝕜 E e x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    simp only [map_smul, PiTensorProduct.reindexₗᵢ_tprod, mapCLM_tprod]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {E'' : ι → Type*} [∀ i, NormedAddCommGroup (E'' i)] [∀ i, InnerProductSpace 𝕜 (E'' i)]
  [∀ i, FiniteDimensional 𝕜 (E'' i)]

omit [∀ i, FiniteDimensional 𝕜 (E'' i)] in
theorem mapCLM_comp (g : ∀ i, E' i →L[𝕜] E'' i) (f : ∀ i, E i →L[𝕜] E' i) :
    mapCLM (fun i ↦ (g i).comp (f i)) = (mapCLM g).comp (mapCLM f) := by
  ext x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a => simp
  | add x y hx hy => simp [hx, hy]

end PiTensorProduct

namespace ContinuousLinearMap

open scoped TensorProduct InnerProductSpace

variable {ι : Type*} [Finite ι] {𝕜 : Type*} [RCLike 𝕜]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
    [∀ i, FiniteDimensional 𝕜 (E i)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

omit [∀ i, FiniteDimensional 𝕜 (E i)] in
/-- **Extensionality via elementary tensors for continuous linear maps out of a pi-tensor product.**
Two continuous linear maps `f g : (⨂[𝕜] i, E i) →L[𝕜] F` out of a finite tensor product of inner
product spaces are equal as soon as they agree on every elementary tensor `⨂ₜ[𝕜] i, x i`. The
elementary tensors span the tensor product and a continuous linear map is determined by its
underlying linear map (`ContinuousLinearMap.coe_injective`, `PiTensorProduct.ext`). -/
theorem ext_tprod {f g : (⨂[𝕜] i, E i) →L[𝕜] F}
    (h : ∀ x : ∀ i, E i, f (⨂ₜ[𝕜] i, x i) = g (⨂ₜ[𝕜] i, x i)) : f = g := by
  apply ContinuousLinearMap.coe_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply]
  exact h x

end ContinuousLinearMap
