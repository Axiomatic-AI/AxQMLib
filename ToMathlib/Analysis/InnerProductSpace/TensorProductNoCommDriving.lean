/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.TensorProductMapLSpan
public import ToMathlib.Analysis.InnerProductSpace.TensorProductInterchange

/-!
# The no-communication driving-unitary reshaping identity (general operators)

This file proves the operator identity at the heart of Nielsen & Chuang Exercise 12.22's
sequential-versus-joint driving-unitary *linchpin*, for **arbitrary** operators on the two
tensor factors — the general form of the product-operator core proved elsewhere.

For finite-dimensional inner product spaces `EA, FA, EB, FB` over an `RCLike` field `𝕜`, and
arbitrary operators `UA : EA ⊗ FA →L EA ⊗ FA` (Alice) and `UB : EB ⊗ FB →L EB ⊗ FB` (Bob), the
composite reshape
conjugation produced by collapsing two sequential single-system dilations (the `leftComm`/`assoc`
composite on the left, the `assoc`-symm composite on the right) equals the clean interchange
conjugation of the product operator `UA ⊗ UB`, reordered to the `FB ⊗ FA` ancilla by
`congrIsometry (refl) (commIsometry)`.

## Main result

* `TensorProduct.noComm_driving_raw_eq` — the general driving-unitary reshaping identity.

## Implementation notes

Both sides of the identity are `𝕜`-bilinear in the pair `(UA, UB)` (the left side is an operator
*composition* of a `UA`-linear factor and a `UB`-linear factor; the right side is a linear image of
the bilinear product `mapL UA UB`), and the identity holds *definitionally* on product operators
`mapL a b`, `mapL c d` — every reshape braid acts factorwise on pure tensors
(`TensorProduct.ext_fourfold'`). It therefore reduces to the product case by bilinearity, obtained
here by a **double `span_induction`** over `TensorProduct.span_range_mapL_eq_top` (product operators
span the operator space): the base case is the pure-tensor `rfl`, the additive/homogeneous cases are
the `mapL`/conjugation additivity lemmas.

The proof is stated over *bare* inner product spaces (not a bundled composite system), so the
`mapL`/`conjStarAlgEquiv` additivity lemmas fire cleanly — the corresponding statement over a
bundled composite `QSystem.space` is blocked by the tensor-instance diamond, which is exactly why
the whole reshaping identity is proved here for bare inner product spaces and then transported to
`QSystem.space` through the definitional `.toIsometry` bridges (`AxQM.Evolution.noComm_driving_eq`).
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace

namespace TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜]
variable {EA FA EB FB : Type*}
  [NormedAddCommGroup EA] [InnerProductSpace 𝕜 EA] [FiniteDimensional 𝕜 EA]
  [NormedAddCommGroup FA] [InnerProductSpace 𝕜 FA] [FiniteDimensional 𝕜 FA]
  [NormedAddCommGroup EB] [InnerProductSpace 𝕜 EB] [FiniteDimensional 𝕜 EB]
  [NormedAddCommGroup FB] [InnerProductSpace 𝕜 FB] [FiniteDimensional 𝕜 FB]

set_option maxHeartbeats 4000000 in
-- The generous heartbeat budget reflects the size of the reshaping expressions pushed through the
-- six `span_induction` cases (each threads `mapL`/`conjStarAlgEquiv` additivity through a deeply
-- nested composite of reshape conjugations over four-fold tensor operator spaces).
set_option synthInstance.maxHeartbeats 400000 in
/-- **The no-communication driving-unitary reshaping identity, for arbitrary operators.** For
operators `UA` on `EA ⊗ FA` (Alice) and `UB` on `EB ⊗ FB` (Bob), the `leftComm`/`assoc` composite
reshape conjugation produced by collapsing two sequential single-system dilations equals the
interchange conjugation of the product operator `UA ⊗ UB`, reordered to the `FB ⊗ FA` ancilla.

Both sides are `𝕜`-bilinear in `(UA, UB)` and agree definitionally on product operators
(`mapL a b`, `mapL c d`), where all the reshape braids act factorwise on pure tensors; the general
identity follows by bilinearity, via a double `span_induction` over `span_range_mapL_eq_top`. This
is the operator-level core of the Nielsen & Chuang Exercise 12.22 sequential↔joint driving-unitary
identity; `AxQM.Evolution.noComm_driving_eq` transports it through the
`.toIsometry` bridges. -/
theorem noComm_driving_raw_eq
    (UA : (EA ⊗[𝕜] FA) →L[𝕜] (EA ⊗[𝕜] FA)) (UB : (EB ⊗[𝕜] FB) →L[𝕜] (EB ⊗[𝕜] FB)) :
    ((((assocIsometry 𝕜 FB (EA ⊗[𝕜] EB) FA).symm.trans
              (congrIsometry (commIsometry 𝕜 FB (EA ⊗[𝕜] EB))
                (LinearIsometryEquiv.refl 𝕜 FA))).trans
            (assocIsometry 𝕜 (EA ⊗[𝕜] EB) FB FA)).conjStarAlgEquiv
          (TensorProduct.mapL 1
            ((congrIsometry (commIsometry 𝕜 EB EA)
                (LinearIsometryEquiv.refl 𝕜 FA)).conjStarAlgEquiv
              ((assocIsometry 𝕜 EB EA FA).symm.conjStarAlgEquiv
                (TensorProduct.mapL 1 UA))))).comp
        ((assocIsometry 𝕜 (EA ⊗[𝕜] EB) FB FA).conjStarAlgEquiv
          (TensorProduct.mapL
            ((assocIsometry 𝕜 EA EB FB).symm.conjStarAlgEquiv (TensorProduct.mapL 1 UB))
            1))
      = (congrIsometry (LinearIsometryEquiv.refl 𝕜 (EA ⊗[𝕜] EB))
            (commIsometry 𝕜 FA FB)).conjStarAlgEquiv
          ((tensorTensorTensorCommIsometry 𝕜 EA FA EB FB).conjStarAlgEquiv
            (TensorProduct.mapL UA UB)) := by
  have hUA : UA ∈ (⊤ : Submodule 𝕜 ((EA ⊗[𝕜] FA) →L[𝕜] (EA ⊗[𝕜] FA))) := Submodule.mem_top
  rw [← span_range_mapL_eq_top] at hUA
  induction hUA using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hx
      have hUB : UB ∈ (⊤ : Submodule 𝕜 ((EB ⊗[𝕜] FB) →L[𝕜] (EB ⊗[𝕜] FB))) := Submodule.mem_top
      rw [← span_range_mapL_eq_top] at hUB
      induction hUB using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨⟨c, d⟩, rfl⟩ := hy
          exact ContinuousLinearMap.coe_injective
            (TensorProduct.ext_fourfold' fun wA wB wCB wCA => rfl)
      | zero =>
          simp only [mapL_zero_left, mapL_zero_right, map_zero, ContinuousLinearMap.comp_zero]
      | add y1 y2 _ _ ih1 ih2 =>
          simp only [mapL_add_left, mapL_add_right, map_add, ContinuousLinearMap.comp_add]
          exact congrArg₂ (· + ·) ih1 ih2
      | smul c y _ ih =>
          simp only [mapL_smul_left, mapL_smul_right, map_smul, ContinuousLinearMap.comp_smul]
          exact congrArg (c • ·) ih
  | zero =>
      simp only [mapL_zero_left, mapL_zero_right, map_zero, ContinuousLinearMap.zero_comp]
  | add x1 x2 _ _ ih1 ih2 =>
      simp only [mapL_add_left, mapL_add_right, map_add, ContinuousLinearMap.add_comp]
      exact congrArg₂ (· + ·) ih1 ih2
  | smul c x _ ih =>
      simp only [mapL_smul_left, mapL_smul_right, map_smul, ContinuousLinearMap.smul_comp]
      exact congrArg (c • ·) ih

end TensorProduct
