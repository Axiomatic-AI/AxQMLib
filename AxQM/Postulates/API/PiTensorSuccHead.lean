/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TensorPowSplit

/-!
# Head-peel conjugation for the indexed product operator

The head-peel isometry `QSystem.tensorPowSuccHead S n : S ^⊗ₛ (n+1) ≃ₛ S ⊗ S ^⊗ₛ n`
(`AxQM/Postulates/API/TensorPowSplit.lean`) acts on the state vectors.  This file records how it
conjugates the elementary *product operator* `PiTensorProduct.mapCLM` — the operator-level fact
behind the `State`-level product-state recursion `State.tmul_piTensor_congr_tensorPowSuccHead_symm`
(`AxQM/Core/PiTensorSuccHead.lean`), which lifts it to the product state `State.piTensor`.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

/-- **Operator-level head-peel conjugation.**  The head-peel isometry
`tensorPowSuccHeadIsometry S n` conjugates the elementary product operator
`(g 0) ⊗ (⨂ⱼ g j.succ)` on `S.space ⊗ (⨂ⱼ S.space)` back to the `(n+1)`-fold product operator
`⨂ᵢ g i` on `⨂ᵢ S.space`:

`(tensorPowSuccHeadIsometry S n).symm.conj (mapL (g 0) (⨂ⱼ g j.succ))  =  ⨂ᵢ g i`.

The operator engine behind the `State`-level recursion
`State.tmul_piTensor_congr_tensorPowSuccHead_symm`.  Stated on the raw `PiTensorProduct` space
`⨂[ℂ] _ : Fin (n+1), S.space` — whose module/inner instances are the canonical `PiTensorProduct`
ones — so the tensor extensionality `ContinuousLinearMap.ext_tprod` applies without meeting the
re-bundled instances of the `QSystem.piTensor` space.  Proved by evaluating both sides on an
elementary tensor `⨂ᵢ vᵢ`: the head-peel maps it to `v 0 ⊗ (⨂ⱼ v j.succ)`, `mapL`/`mapCLM` act
factorwise, and the inverse head-peel reassembles the `cons` (`Fin.cons_self_tail`). -/
theorem QSystem.tensorPowSuccHeadIsometry_symm_conj (S : QSystem) (n : ℕ)
    (g : Fin (n + 1) → S.space →L[ℂ] S.space) :
    (QSystem.tensorPowSuccHeadIsometry S n).symm.conjStarAlgEquiv
        (TensorProduct.mapL (g 0) (PiTensorProduct.mapCLM fun j => g j.succ))
      = PiTensorProduct.mapCLM g := by
  apply ContinuousLinearMap.ext_tprod
  intro v
  erw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_symm,
    QSystem.tensorPowSuccHead_toIsometry_tprod, TensorProduct.mapL_tmul,
    PiTensorProduct.mapCLM_tprod, PiTensorProduct.mapCLM_tprod,
    QSystem.tensorPowSuccHead_symm_toIsometry_tmul_tprod]
  exact congrArg (PiTensorProduct.tprod ℂ) (Fin.cons_self_tail fun i => g i (v i))

end AxQM
