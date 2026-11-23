/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSumChoi
public import ToMathlib.Analysis.InnerProductSpace.PiL2
public import ToMathlib.LinearAlgebra.TensorProduct.Map
-- `TensorProduct` is re-imported LAST on purpose (mirroring `OperatorSumChoi`/`OperatorSumCP`): it
-- re-asserts the inner-product-space normed structure on `E ⊗[𝕜] F` as the resolution-priority
-- module instance over the bare algebraic one, so operators built with `TensorProduct.map` unify
-- with the normed module that `LinearMap.IsPositive`/`rankOne`/`rTensor` require.
public import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Positivity of the Choi operator (reverse direction of Theorem 8.1)

Building on `ToMathlib.Analysis.InnerProductSpace.OperatorSumChoi`, the **Choi operator**
`σ = choiOp b Φ` of a **completely positive** superoperator `Φ` is a *positive* operator, `σ ≥ 0`
(Nielsen–Chuang, *Quantum Computation and Quantum Information*, §8.2.4, Eq. (8.60)). This is the
input to the spectral (PSD) decomposition `σ = Σᵢ |sᵢ⟩⟨sᵢ|` from which the operation elements of the
reverse direction of Theorem 8.1 are read off.

## The universe obstacle, and how it is resolved

Complete positivity (`ContinuousLinearMap.IsCompletelyPositive`) quantifies its reference system
`R` over `Type` (universe `0`) — this is not a weakening, since complete positivity depends only on
the reference's *dimension* and every finite dimension is realised in `Type 0`. But the Choi
operator `σ = (id_H ⊗ Φ)(|α⟩⟨α|)` is built with the reference taken to be the input space `H`
itself (via `choiOp`), which lives in an arbitrary universe. Concluding `σ ≥ 0` directly from
`IsCompletelyPositive Φ` therefore needs a **universe transport**: transfer positivity of the
ampliation with reference `H` to positivity of the ampliation with reference
`R₀ = EuclideanSpace ℂ (Fin (dim H))` (a `Type 0` space isometric to `H`), where complete positivity
applies.

The transport rests on the **naturality of the ampliation in its reference**: for a linear isometry
`e : H ≃ₗᵢ R`, conjugating `superopAmpliationₗ H Φ` by the reference-factor isometry
`rTensor _ e = e ⊗ id` equals `superopAmpliationₗ R Φ` of the conjugated argument. On product
operators `B ⊗ C` this is immediate from `superopAmpliationₗ_map` (the reference factor `B` is
carried through untouched by `Φ`, so conjugating it by `e` on both sides agrees — the underlying
purely-algebraic fact `LinearEquiv.rTensor_comp_map_comp_symm`); the general case follows by
linearity.

## Main results

* `ContinuousLinearMap.superopAmpliationₗ_conj_rTensor` — **naturality of the ampliation in its
  reference**: `superopAmpliationₗ R Φ (rTensor H e · rTensor H e⁻¹) =
  rTensor G e · (superopAmpliationₗ H Φ ·) · rTensor G e⁻¹`.
* `ContinuousLinearMap.IsCompletelyPositive.superopAmpliationₗ_isPositive` — the **universe
  transport**: a completely positive `Φ` has *every* ampliation
  `superopAmpliationₗ H (toLMSuperop Φ)` (reference `H` of arbitrary universe)
  positivity-preserving, not merely the `Type 0` references of `IsCompletelyPositive`.
* `ContinuousLinearMap.choiOp_isPositive` — **the Choi operator of a completely positive map is
  positive** (N&C Eq. (8.60)): `σ = choiOp b Φ ≥ 0`, since `σ` is the ampliation of the positive
  operator `|α⟩⟨α|` (`isPositive_rankOne_self`).

Everything here is general finite-dimensional complex Hilbert-space operator mathematics.
-/

open scoped TensorProduct InnerProductSpace
open ContinuousLinearMap

noncomputable section

@[expose] public section

namespace ContinuousLinearMap

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]

omit [CompleteSpace H] [CompleteSpace G] in
/-- **Naturality of the ampliation in its reference system.** For a linear isometry
`e : H ≃ₗᵢ R` between (finite-dimensional) reference spaces, conjugating the ampliation
`superopAmpliationₗ H Φ` by the reference-factor isometry `rTensor _ e` equals the ampliation
`superopAmpliationₗ R Φ` of the conjugated argument:
`superopAmpliationₗ R Φ (rTensor H e ∘ A ∘ (rTensor H e)⁻¹)
  = rTensor G e ∘ superopAmpliationₗ H Φ A ∘ (rTensor G e)⁻¹`.
Reducing `A` to product operators `B ⊗ C` (via `homTensorHomEquiv` surjectivity), each side becomes
`(e B e⁻¹) ⊗ Φ C` by `superopAmpliationₗ_map` and the general algebraic conjugation lemma
`LinearEquiv.rTensor_comp_map_comp_symm` (after normalising the isometry `rTensor` to the underlying
`LinearEquiv.rTensor` via `LinearIsometryEquiv.toLinearEquiv_rTensor`). -/
theorem superopAmpliationₗ_conj_rTensor {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R]
    [FiniteDimensional ℂ R] (e : H ≃ₗᵢ[ℂ] R) (Φ : (H →ₗ[ℂ] H) →ₗ[ℂ] (G →ₗ[ℂ] G))
    (A : H ⊗[ℂ] H →ₗ[ℂ] H ⊗[ℂ] H) :
    superopAmpliationₗ R Φ
        ((↑(LinearIsometryEquiv.rTensor H e).toLinearEquiv : H ⊗[ℂ] H →ₗ[ℂ] R ⊗[ℂ] H) ∘ₗ A ∘ₗ
          (↑(LinearIsometryEquiv.rTensor H e).symm.toLinearEquiv : R ⊗[ℂ] H →ₗ[ℂ] H ⊗[ℂ] H))
      = (↑(LinearIsometryEquiv.rTensor G e).toLinearEquiv : H ⊗[ℂ] G →ₗ[ℂ] R ⊗[ℂ] G) ∘ₗ
          superopAmpliationₗ H Φ A ∘ₗ
          (↑(LinearIsometryEquiv.rTensor G e).symm.toLinearEquiv : R ⊗[ℂ] G →ₗ[ℂ] H ⊗[ℂ] G) := by
  obtain ⟨X, rfl⟩ := (homTensorHomEquiv ℂ H H H H).surjective A
  induction X using TensorProduct.inductionOn with
  | tmul B C =>
      -- Normalise the isometry reference factor `rTensor _ e` to the underlying
      -- `LinearEquiv.rTensor` of `e.toLinearEquiv`, so the general algebraic
      -- `LinearEquiv.rTensor_comp_map_comp_symm` applies.
      rw [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]
      simp only [LinearIsometryEquiv.toLinearEquiv_symm, LinearIsometryEquiv.toLinearEquiv_rTensor]
      rw [LinearEquiv.rTensor_comp_map_comp_symm, superopAmpliationₗ_map, superopAmpliationₗ_map,
        LinearEquiv.rTensor_comp_map_comp_symm]
  | add X Y ihX ihY =>
      simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, ihX, ihY]

omit [CompleteSpace H] [CompleteSpace G] in
/-- **Universe transport of complete positivity to an arbitrary-universe reference.** A completely
positive superoperator `Φ` has *every* reference ampliation `superopAmpliationₗ H (toLMSuperop Φ)`
positivity-preserving — including the reference `H` itself, which need not live in `Type 0`. The
`IsCompletelyPositive` predicate only asserts this for references `R : Type 0`; we transport along
the linear isometry `e : H ≃ₗᵢ EuclideanSpace ℂ (Fin (dim H))` to a `Type 0` reference, using the
reference naturality `superopAmpliationₗ_conj_rTensor` and invariance of positivity under isometric
conjugation (`isPositive_linearIsometryEquiv_conj_iff`). -/
theorem IsCompletelyPositive.superopAmpliationₗ_isPositive
    {Φ : (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)} (hΦ : IsCompletelyPositive Φ)
    {A : H ⊗[ℂ] H →ₗ[ℂ] H ⊗[ℂ] H} (hA : A.IsPositive) :
    (superopAmpliationₗ H (toLMSuperop Φ) A).IsPositive := by
  set e : H ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ H)) := (stdOrthonormalBasis ℂ H).repr
    with he
  -- Transport `A ≥ 0` to a positive operator on the `Type 0` reference `R₀ ⊗ H`.
  have hA' : ((↑(LinearIsometryEquiv.rTensor H e).toLinearEquiv :
        H ⊗[ℂ] H →ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ H)) ⊗[ℂ] H) ∘ₗ A ∘ₗ
        (↑(LinearIsometryEquiv.rTensor H e).symm.toLinearEquiv :
          EuclideanSpace ℂ (Fin (Module.finrank ℂ H)) ⊗[ℂ] H →ₗ[ℂ] H ⊗[ℂ] H)).IsPositive :=
    (LinearMap.isPositive_linearIsometryEquiv_conj_iff (LinearIsometryEquiv.rTensor H e)).mpr hA
  -- Complete positivity applies at the `Type 0` reference `R₀ = EuclideanSpace ℂ (Fin (dim H))`.
  have hCP := hΦ (EuclideanSpace ℂ (Fin (Module.finrank ℂ H))) _ hA'
  rw [superopAmpliationₗ_conj_rTensor] at hCP
  exact (LinearMap.isPositive_linearIsometryEquiv_conj_iff (LinearIsometryEquiv.rTensor G e)).mp hCP

omit [CompleteSpace H] [CompleteSpace G] in
/-- **The Choi operator of a completely positive map is positive** (Nielsen–Chuang Eq. (8.60)). For
a completely positive superoperator `Φ`, the Choi operator `σ = choiOp b Φ = (id_H ⊗ Φ)(|α⟩⟨α|)` is
a positive operator on `H ⊗ G`. Indeed `σ` is the ampliation (reference `H`) of the maximally
entangled projector `|α⟩⟨α|`, which is positive (`isPositive_rankOne_self`); positivity of the
ampliation is `IsCompletelyPositive.superopAmpliationₗ_isPositive`. This `σ ≥ 0` is the input to the
PSD decomposition `σ = Σᵢ |sᵢ⟩⟨sᵢ|` of the reverse direction of Theorem 8.1. -/
theorem choiOp_isPositive {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H)
    {Φ : (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)} (hΦ : IsCompletelyPositive Φ) :
    (choiOp b Φ).IsPositive := by
  rw [choiOp]
  refine hΦ.superopAmpliationₗ_isPositive ?_
  rw [ContinuousLinearMap.isPositive_toLinearMap_iff]
  exact InnerProductSpace.isPositive_rankOne_self b.maxEntVec

end ContinuousLinearMap
