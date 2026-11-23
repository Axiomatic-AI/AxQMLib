/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Conjugation of a tensor-product operator by a factorwise transport

The factorwise-transport companion of `TensorProduct.commIsometry_conjStarAlgEquiv_mapL` and
`TensorProduct.assocIsometry_conjStarAlgEquiv_mapL_mapL`: conjugating the tensor-product operator
`A ⊗ B` by the factorwise isometry `congrIsometry e f` (as the `⋆`-algebra equivalence
`LinearIsometryEquiv.conjStarAlgEquiv`) conjugates each factor operator by its own transport,

`(e ⊗ f) (A ⊗ B) (e ⊗ f)⁻¹ = (e A e⁻¹) ⊗ (f B f⁻¹)`.

This is the `conjStarAlgEquiv` reading of the naturality of `TensorProduct.map` under
`TensorProduct.congr`, packaged for the density-operator transport machinery
(`LinearIsometryEquiv.conjStarAlgEquiv` is how a state/observable is carried along a unitary
change of basis).
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

variable {𝕜 : Type*} {E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] [CompleteSpace H]
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H]

/-- Conjugating a tensor-product operator by a factorwise transport `congrIsometry e f` (as the
`⋆`-algebra equivalence `conjStarAlgEquiv`) conjugates each factor operator by its own transport:
`(e ⊗ f).conjStarAlgEquiv (A ⊗ B) = (e A e⁻¹) ⊗ (f B f⁻¹)`, as continuous linear maps on
`G ⊗[𝕜] H`. The `conjStarAlgEquiv` reading of the naturality of `map` under `congr`, and the
factorwise sibling of `commIsometry_conjStarAlgEquiv_mapL` /
`assocIsometry_conjStarAlgEquiv_mapL_mapL`. -/
theorem congrIsometry_conjStarAlgEquiv_mapL (e : E ≃ₗᵢ[𝕜] G) (f : F ≃ₗᵢ[𝕜] H)
    (A : E →L[𝕜] E) (B : F →L[𝕜] F) :
    (congrIsometry e f).conjStarAlgEquiv (mapL A B)
      = mapL (e.conjStarAlgEquiv A) (f.conjStarAlgEquiv B) := by
  apply ContinuousLinearMap.coe_injective
  apply TensorProduct.ext'
  intro x y
  simp [congrIsometry_apply, congrIsometry_symm]

end TensorProduct

end
