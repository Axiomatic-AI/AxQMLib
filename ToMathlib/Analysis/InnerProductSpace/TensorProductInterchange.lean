/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The middle-two interchange isometry on a fourfold tensor product

The **linear isometry equivalence version of `TensorProduct.tensorTensorTensorComm`**: for inner
product spaces `E, F, G, H`, the rearrangement
`(E ⊗ F) ⊗ (G ⊗ H) ≃ₗᵢ[𝕜] (E ⊗ G) ⊗ (F ⊗ H)` that swaps the two middle factors, packaged as an
isometry so it transports the inner-product / norm structure.

`TensorProduct.tensorTensorTensorComm` already provides this rearrangement as a plain `≃ₗ`; this
file upgrades it to a `≃ₗᵢ`.  Rather than re-proving inner-product preservation for the composite,
we assemble it directly from the existing isometry equivalences `assocIsometry`, `commIsometry`
and `congrIsometry` (each of which is already known to be an isometry), so the result is
manifestly an isometry.  Its action on pure tensors is `tensorTensorTensorCommIsometry_tmul`,
matching `TensorProduct.tensorTensorTensorComm_tmul`.

## Main definitions

* `TensorProduct.tensorTensorTensorCommIsometry` — the interchange isometry equivalence.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

variable (𝕜 : Type*) [RCLike 𝕜]
variable (E F G H : Type*)
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The **linear isometry equivalence version of `TensorProduct.tensorTensorTensorComm`**: the
inner-product-preserving rearrangement `(E ⊗ F) ⊗ (G ⊗ H) ≃ₗᵢ (E ⊗ G) ⊗ (F ⊗ H)` swapping the two
middle factors `F` and `G`.  Assembled from the isometry equivalences `assocIsometry`,
`commIsometry` and `congrIsometry` (each already an isometry), so it is manifestly an isometry
with no separate inner-product-preservation proof; its action on pure tensors is
`tensorTensorTensorCommIsometry_tmul`. -/
noncomputable def tensorTensorTensorCommIsometry :
    (E ⊗[𝕜] F) ⊗[𝕜] (G ⊗[𝕜] H) ≃ₗᵢ[𝕜] (E ⊗[𝕜] G) ⊗[𝕜] (F ⊗[𝕜] H) :=
  (assocIsometry 𝕜 E F (G ⊗[𝕜] H)).trans
    ((congrIsometry (LinearIsometryEquiv.refl 𝕜 E) (assocIsometry 𝕜 F G H).symm).trans
      ((congrIsometry (LinearIsometryEquiv.refl 𝕜 E)
          (congrIsometry (commIsometry 𝕜 F G) (LinearIsometryEquiv.refl 𝕜 H))).trans
        ((congrIsometry (LinearIsometryEquiv.refl 𝕜 E) (assocIsometry 𝕜 G F H)).trans
          (assocIsometry 𝕜 E G (F ⊗[𝕜] H)).symm)))

@[simp] theorem tensorTensorTensorCommIsometry_tmul (e : E) (f : F) (g : G) (h : H) :
    tensorTensorTensorCommIsometry 𝕜 E F G H ((e ⊗ₜ[𝕜] f) ⊗ₜ[𝕜] (g ⊗ₜ[𝕜] h))
      = (e ⊗ₜ[𝕜] g) ⊗ₜ[𝕜] (f ⊗ₜ[𝕜] h) := by
  simp only [tensorTensorTensorCommIsometry, LinearIsometryEquiv.trans_apply, assocIsometry_apply,
    TensorProduct.assoc_tmul, congrIsometry_tmul, LinearIsometryEquiv.coe_refl, id_eq,
    assocIsometry_symm_apply, TensorProduct.assoc_symm_tmul, commIsometry_apply,
    TensorProduct.comm_tmul]

end TensorProduct
