/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PiTensorSuccHead
import AxQM.Postulates.API.Qubit

/-!
# Head-peel recursion for the indexed product state `State.piTensor`

Lifting the head-peel conjugation
`QSystem.tensorPowSuccHeadIsometry_symm_conj` (`Postulates/API/PiTensorSuccHead`) to the level of
**product states**, this file gives the missing `succ`-recursion for the indexed product (mixed)
state `State.piTensor`:

`⨂ₚ i, f i  =  (f 0) ⊗ (⨂ₚ j, f j.succ)`   (transported along the head-peel).

It is the `State` companion of the pure-state head-peel action lemmas, and the structural step
behind any induction over the number of tensor factors of a mixed product state — in particular the
`n`-fold subadditivity of the Holevo χ quantity underlying the HSW converse single-letterisation
(N&C Theorem 12.8).

The proof uses `QSystem.tensorPowSuccHeadIsometry_symm_conj` from
`AxQM/Postulates/API/PiTensorSuccHead.lean`.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Head-peel recursion for `State.piTensor`** (the `cons` direction).  Transporting the product
state `(f 0) ⊗ (⨂ⱼ f j.succ)` on `S ⊗ S ^⊗ₛ n` *backwards* along the head-peel isomorphism
`QSystem.tensorPowSuccHead S n` reconstructs the full `(n+1)`-fold product state `⨂ᵢ f i` on
`S ^⊗ₛ (n+1)`:

`((f 0) ⊗ (⨂ⱼ f j.succ)).congr (QSystem.tensorPowSuccHead S n).symm  =  ⨂ᵢ f i`.

The `State`-level analogue of `QSystem.tensorPowSuccHead_symm_toIsometry_tmul_tprod`; the structural
`succ` step for an induction over the tensor factors of a mixed product state.  Reduces, via
`State.congr_op`/`State.tmul_op`/`State.piTensor_op`, to
`QSystem.tensorPowSuccHeadIsometry_symm_conj`. -/
theorem State.tmul_piTensor_congr_tensorPowSuccHead_symm {n : ℕ} (f : Fin (n + 1) → State S) :
    ((f 0).tmul (State.piTensor fun j : Fin n => f j.succ)).congr
        (QSystem.tensorPowSuccHead S n).symm
      = State.piTensor f := by
  apply State.ext
  erw [State.congr_op, State.tmul_op, State.piTensor_op, State.piTensor_op,
    QSystem.Iso.symm_toIsometry]
  exact QSystem.tensorPowSuccHeadIsometry_symm_conj S n fun i => (f i).op

/-- **`PureState` head-peel of the tensor-power head split.** `⨂ₚ ᵢ ψ i ↦ ψ 0 ⊗ (⨂ₚ ⱼ ψ j.succ)`:
transporting a product state along `QSystem.tensorPowSuccHead qubit m` peels the head factor off the
front. The pure-state companion of `State.tmul_piTensor_congr_tensorPowSuccHead_symm` (forward
direction); reduces, via `PureState.congr_vec`/`piTensor_vec`/`tmul_vec`, to the isometry action
`QSystem.tensorPowSuccHead_toIsometry_tprod`. -/
theorem tensorPowSuccHead_congr_piTensor (m : ℕ) (ψ : Fin (m + 1) → PureState qubit) :
    PureState.congr (QSystem.tensorPowSuccHead qubit m) (PureState.piTensor ψ)
      = (ψ 0).tmul (PureState.piTensor fun j => ψ j.succ) := by
  apply PureState.ext
  erw [PureState.congr_vec, PureState.piTensor_vec, PureState.tmul_vec, PureState.piTensor_vec]
  rw [QSystem.tensorPowSuccHead_toIsometry_tprod]
  rfl

/-- **`PureState` `cons` of the inverse tensor-power head split.**
`a ⊗ (⨂ₚ ⱼ φ j) ↦ ⨂ₚ ᵢ (Fin.cons a φ) i`: transporting along `(tensorPowSuccHead qubit m).symm`
prepends a head factor `a` to the tail product `⨂ₚ φ`. The pure-state `cons` companion of
`State.tmul_piTensor_congr_tensorPowSuccHead_symm`; reduces to the isometry action
`QSystem.tensorPowSuccHead_symm_toIsometry_tmul_tprod`. -/
theorem tensorPowSuccHead_symm_congr_tmul_piTensor (m : ℕ) (a : PureState qubit)
    (φ : Fin m → PureState qubit) :
    PureState.congr (QSystem.tensorPowSuccHead qubit m).symm (a.tmul (PureState.piTensor φ))
      = PureState.piTensor (Fin.cons a φ) := by
  apply PureState.ext
  erw [PureState.congr_vec, PureState.tmul_vec, PureState.piTensor_vec, PureState.piTensor_vec,
    QSystem.Iso.symm_toIsometry, QSystem.tensorPowSuccHead_symm_toIsometry_tmul_tprod]
  congr 1
  exact (Fin.comp_cons PureState.vec a φ).symm

end AxQM
