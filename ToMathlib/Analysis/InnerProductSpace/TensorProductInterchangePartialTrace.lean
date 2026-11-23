/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.TensorProductInterchange
public import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
public import Mathlib.LinearAlgebra.Contraction

/-!
# Partial trace through the middle-two interchange isometry

For finite-dimensional inner product spaces `E, F, G, H` over `RCLike 𝕜`, the interchange isometry
`tensorTensorTensorCommIsometry : (E ⊗ F) ⊗ (G ⊗ H) ≃ₗᵢ (E ⊗ G) ⊗ (F ⊗ H)` swaps the two middle
factors `F` and `G`.  Conjugating a **product** operator `mapL P Q` (with `P` on `E ⊗ F`, `Q` on
`G ⊗ H`) by it and then tracing out the new right factor `F ⊗ H` computes the `E ⊗ G`-marginal:

`Tr_{F ⊗ H} (interchange (P ⊗ Q) interchange⁻¹) = (Tr_F P) ⊗ (Tr_H Q)`.

Even though `P`, `Q` are entangling within their own blocks, the marginal factorises: `E` sees only
the `F`-trace of `P` and `G` sees only the `H`-trace of `Q`.  This is the operator-level step
behind the "trace out both parties' ancillae" step of Nielsen & Chuang Exercise 12.22 — where the
joint pure state factorises as `|φ⟩⟨φ| ⊗ |χ⟩⟨χ|` and its Alice-side `(A ⊗ CA)`-marginal is read off
as `ρ_φ ⊗ ρ_χ` across the `(A ⊗ B) | (CA ⊗ CB)` ↔ `(A ⊗ CA) | (B ⊗ CB)` interchange.

## Design notes

Both sides are `𝕜`-bilinear in `(P, Q)`, and the operators `TensorProduct.map a b` span
`E ⊗ F →ₗ[𝕜] E ⊗ F` (via `homTensorHomEquiv`), so it suffices to check the identity on **fully
product** operators `P = a ⊗ b`, `Q = c ⊗ d`.  There the interchange conjugation is the four-factor
naturality `tensorTensorTensorComm_conj_map` (`interchange ∘ (a ⊗ b ⊗ c ⊗ d) ∘ interchange⁻¹ =
a ⊗ c ⊗ b ⊗ d`), after which `partialTraceRight_tensorMap` and `trace_tensorProduct'` close it.  The
reduction to product operators is a nested `homTensorHomEquiv`-surjectivity +
`TensorProduct.induction_on` on each of `P`, `Q`, mirroring the reduction in
`sum_conjStarAlgEquiv_congrIsometry_depolarizingUnitary`.

## Main results

* `TensorProduct.tensorTensorTensorCommIsometry_toLinearEquiv` — the isometry's underlying `≃ₗ` is
  `TensorProduct.tensorTensorTensorComm`.
* `TensorProduct.tensorTensorTensorComm_conj_map` — the four-factor naturality: conjugating a fully
  product operator `map (map a b) (map c d)` by the interchange gives `map (map a c) (map b d)`.
* `TensorProduct.partialTraceRight_tensorTensorTensorCommIsometry_conjStarAlgEquiv_mapL` — the
  interchange marginal of a product operator, in `conjStarAlgEquiv` / `mapL` form.
-/

@[expose] public section

open scoped TensorProduct
open LinearMap (partialTraceRight)

namespace TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The underlying linear equivalence of the interchange isometry
`tensorTensorTensorCommIsometry` is the plain `TensorProduct.tensorTensorTensorComm`: both send
`(e ⊗ f) ⊗ (g ⊗ h) ↦ (e ⊗ g) ⊗ (f ⊗ h)`. -/
theorem tensorTensorTensorCommIsometry_toLinearEquiv :
    (tensorTensorTensorCommIsometry 𝕜 E F G H).toLinearEquiv
      = tensorTensorTensorComm 𝕜 E F G H := by
  refine LinearEquiv.toLinearMap_injective (TensorProduct.ext_fourfold' fun e f g h => ?_)
  simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    tensorTensorTensorCommIsometry_tmul, tensorTensorTensorComm_tmul]

/-- **Four-factor naturality of `tensorTensorTensorComm` conjugation.** Conjugating the fully
product operator `map (map a b) (map c d)` by the middle-two interchange reshuffles the four
blocks. The operator/`conj`-level companion of `tensorTensorTensorComm_tmul`. -/
theorem tensorTensorTensorComm_conj_map (a : E →ₗ[𝕜] E) (b : F →ₗ[𝕜] F) (c : G →ₗ[𝕜] G)
    (d : H →ₗ[𝕜] H) :
    (tensorTensorTensorComm 𝕜 E F G H).conj
        (TensorProduct.map (TensorProduct.map a b) (TensorProduct.map c d))
      = TensorProduct.map (TensorProduct.map a c) (TensorProduct.map b d) := by
  refine TensorProduct.ext_fourfold' fun w x y z => ?_
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    tensorTensorTensorComm_symm, tensorTensorTensorComm_tmul, TensorProduct.map_tmul]

section FiniteDimensional
variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
  [FiniteDimensional 𝕜 H]

/-- `(interchange.conjStarAlgEquiv T).toLinearMap` is the `LinearEquiv.conj` of the plain
interchange linear equivalence — the `_toLinearMap` bridge for `tensorTensorTensorCommIsometry`,
mirroring `assocIsometry_conjStarAlgEquiv_toLinearMap`. -/
theorem tensorTensorTensorCommIsometry_conjStarAlgEquiv_toLinearMap
    (T : ((E ⊗[𝕜] F) ⊗[𝕜] (G ⊗[𝕜] H)) →L[𝕜] ((E ⊗[𝕜] F) ⊗[𝕜] (G ⊗[𝕜] H))) :
    ((tensorTensorTensorCommIsometry 𝕜 E F G H).conjStarAlgEquiv T).toLinearMap
      = (tensorTensorTensorComm 𝕜 E F G H).conj T.toLinearMap := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_toLinearMap,
    tensorTensorTensorCommIsometry_toLinearEquiv]

/-- **Four-factor naturality of the interchange isometry conjugation, `conjStarAlgEquiv`/`mapL`
form.** Conjugating the fully product continuous operator `mapL (mapL a b) (mapL c d)` by the
middle-two interchange isometry reshuffles the four blocks:
`interchange.conjStarAlgEquiv (a ⊗ b ⊗ c ⊗ d) = a ⊗ c ⊗ b ⊗ d`. The `ContinuousLinearMap` reading of
`tensorTensorTensorComm_conj_map`, bridging via
`tensorTensorTensorCommIsometry_conjStarAlgEquiv_toLinearMap` and `toLinearMap_mapL`. -/
theorem tensorTensorTensorCommIsometry_conjStarAlgEquiv_mapL_mapL
    (a : E →L[𝕜] E) (b : F →L[𝕜] F) (c : G →L[𝕜] G) (d : H →L[𝕜] H) :
    (tensorTensorTensorCommIsometry 𝕜 E F G H).conjStarAlgEquiv (mapL (mapL a b) (mapL c d))
      = mapL (mapL a c) (mapL b d) := by
  apply ContinuousLinearMap.coe_injective
  rw [tensorTensorTensorCommIsometry_conjStarAlgEquiv_toLinearMap, toLinearMap_mapL,
    toLinearMap_mapL, toLinearMap_mapL, toLinearMap_mapL, toLinearMap_mapL, toLinearMap_mapL,
    tensorTensorTensorComm_conj_map]

variable {ι ιF ιH : Type*} [Fintype ι] [Fintype ιF] [Fintype ιH]

/-- **Interchange marginal of a product operator, `LinearMap` form.** Conjugating the product
operator `map Pl Ql` (`Pl` on `E ⊗ F`, `Ql` on `G ⊗ H`) by the plain interchange linear equivalence
and tracing out the new right factor `F ⊗ H` (over any orthonormal basis `bt` of it) yields
`(Tr_F Pl) ⊗ (Tr_H Ql)`.  Both sides are linear in each of `Pl`, `Ql`; reducing each to product
operators `map _ _` via `homTensorHomEquiv` surjectivity, the four-factor case is
`tensorTensorTensorComm_conj_map` + `partialTraceRight_tensorMap` + `trace_tensorProduct'` (all
basis-free once the trace has been taken). -/
theorem partialTraceRight_tensorTensorTensorComm_conj_map
    (bt : OrthonormalBasis ι 𝕜 (F ⊗[𝕜] H)) (bF : OrthonormalBasis ιF 𝕜 F)
    (bH : OrthonormalBasis ιH 𝕜 H) (Pl : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F)
    (Ql : G ⊗[𝕜] H →ₗ[𝕜] G ⊗[𝕜] H) :
    partialTraceRight bt
        ((tensorTensorTensorComm 𝕜 E F G H).conj (TensorProduct.map Pl Ql))
      = TensorProduct.map (partialTraceRight bF Pl) (partialTraceRight bH Ql) := by
  obtain ⟨X, rfl⟩ := (homTensorHomEquiv 𝕜 E F E F).surjective Pl
  induction X using TensorProduct.inductionOn with
  | add X₁ X₂ h₁ h₂ =>
      simp only [map_add, TensorProduct.map_add_left, ← LinearMap.partialTraceRightLM_apply] at *
      rw [h₁, h₂]
  | tmul a b =>
      obtain ⟨Y, rfl⟩ := (homTensorHomEquiv 𝕜 G H G H).surjective Ql
      induction Y using TensorProduct.inductionOn with
      | add Y₁ Y₂ h₁ h₂ =>
          simp only [map_add, TensorProduct.map_add_right, ← LinearMap.partialTraceRightLM_apply]
            at *
          rw [h₁, h₂]
      | tmul c d =>
          rw [homTensorHomEquiv_apply, homTensorHomEquiv_apply, homTensorHomMap_apply,
            homTensorHomMap_apply, tensorTensorTensorComm_conj_map,
            LinearMap.partialTraceRight_tensorMap, LinearMap.partialTraceRight_tensorMap,
            LinearMap.partialTraceRight_tensorMap, LinearMap.trace_tensorProduct',
            TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul]

/-- **Interchange marginal of a product operator** (`conjStarAlgEquiv` / `mapL` form). Conjugating
the product operator `mapL P Q` (with `P` on `E ⊗ F`, `Q` on `G ⊗ H`) by the interchange isometry
`tensorTensorTensorCommIsometry` and tracing out the new right factor `F ⊗ H` yields the product of
the two block marginals `(Tr_F P) ⊗ (Tr_H Q)`. The `ContinuousLinearMap` reading of
`partialTraceRight_tensorTensorTensorComm_conj_map`, bridging via
`tensorTensorTensorCommIsometry_conjStarAlgEquiv_toLinearMap` and `toLinearMap_mapL`. -/
theorem partialTraceRight_tensorTensorTensorCommIsometry_conjStarAlgEquiv_mapL
    (bt : OrthonormalBasis ι 𝕜 (F ⊗[𝕜] H)) (bF : OrthonormalBasis ιF 𝕜 F)
    (bH : OrthonormalBasis ιH 𝕜 H)
    (P : E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F) (Q : G ⊗[𝕜] H →L[𝕜] G ⊗[𝕜] H) :
    partialTraceRight bt
        ((tensorTensorTensorCommIsometry 𝕜 E F G H).conjStarAlgEquiv (mapL P Q)).toLinearMap
      = TensorProduct.map (partialTraceRight bF P.toLinearMap)
          (partialTraceRight bH Q.toLinearMap) := by
  rw [tensorTensorTensorCommIsometry_conjStarAlgEquiv_toLinearMap, toLinearMap_mapL]
  exact partialTraceRight_tensorTensorTensorComm_conj_map bt bF bH P.toLinearMap Q.toLinearMap

end FiniteDimensional

end TensorProduct
