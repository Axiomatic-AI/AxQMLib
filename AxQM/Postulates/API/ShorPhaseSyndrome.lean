/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorCodeBlock

/-!
# AxQM.Postulates.API — the Shor-code phase-flip syndrome observables

Infrastructure for the phase-flip part of the nine-qubit Shor code (Nielsen &
Chuang §10.2, Exercise 10.5). The Shor code is a *concatenation*: three "phase-flip qubits" `|±⟩`,
each encoded by the three-qubit bit-flip code into a **block** — the cat state
`catBlockState σ = (|000⟩ + (−1)^σ |111⟩)/√2` (developed in `ShorCodeBlock.lean`, where `X⊗X⊗X`
reads a block's `±` sign). Detecting a phase flip means *comparing the signs of adjacent blocks*,
just as the bare phase-flip code compares the signs of adjacent qubits by measuring `X₁X₂`, `X₂X₃`.
This file assembles the nine-qubit register and the two block-sign-comparison observables.

* `shorReg = bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)` — the nine-qubit register, three blocks
  `(q₁q₂q₃)(q₄q₅q₆)(q₇q₈q₉)`.
* `shorPhaseSyndromeX123456` (`X₁X₂X₃X₄X₅X₆ = X⊗X⊗X on blocks 1,2, I on block 3`) and
  `shorPhaseSyndromeX456789` (`X₄X₅X₆X₇X₈X₉ = I on block 1, X⊗X⊗X on blocks 2,3`), the two
  phase-flip syndrome observables of Exercise 10.5. They share the block-2 factor `X₄X₅X₆`, exactly
  as the bit-flip syndrome observables `Z₁Z₂`, `Z₂Z₃` share `Z₂`. Each is a self-adjoint involution
  (`shorPhaseSyndromeX123456_op_mul_self`, `shorPhaseSyndromeX456789_op_mul_self`), so it defines a
  two-outcome `±1` measurement.
* `shorCatProduct σ₁ σ₂ σ₃` — the three-block product `catBlockState σ₁ ⊗ (catBlockState σ₂ ⊗
  catBlockState σ₃)`. The logical codewords are the equal-sign products (`|0_L⟩` at `0,0,0`,
  `|1_L⟩` at `1,1,1`); a phase flip on block `b` flips `σ_b`, so this family is exactly the set of
  states the phase-flip syndrome discriminates.
* `shorPhaseSyndromeX123456_op_shorCatProduct_vec` / `..X456789..` — the **joint sign-readout law**:
  on a three-block cat product, `X₁X₂X₃X₄X₅X₆` acts by the scalar `(−1)^{σ₁+σ₂}` and
  `X₄X₅X₆X₇X₈X₉` by `(−1)^{σ₂+σ₃}` — the product of the signs of the two blocks each observable
  spans. Its `+1`/`−1` value is `+1` iff those two blocks agree in sign (no phase flip between them)
  and `−1` iff they differ. This is the elementary computation behind Exercise 10.5; the
  `HasEigenstate` statements it supports are in `AxQM/NC/Ch10/Exercise10_5.lean`.

The general helper `Observable.tmul_op_mul_self` (a tensor of involutive observables is involutive,
in `Postulates/API/Observable`) is reused for both syndrome observables.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-! ### The nine-qubit Shor register and the two phase-flip syndrome observables -/

/-- **The nine-qubit Shor register** `bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)`: three copies of the
three-qubit bit-flip register, one per "phase-flip qubit" of the concatenated Shor code (N&C §10.2).
Its physical qubits are grouped into three blocks `(q₁q₂q₃)(q₄q₅q₆)(q₇q₈q₉)`. -/
abbrev shorReg : QSystem := bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)

/-- **`X₁X₂X₃X₄X₅X₆`**, the first Shor phase-flip syndrome observable: `X⊗X⊗X` on block 1, `X⊗X⊗X`
on block 2, identity on block 3. Its `±1` outcome compares the signs of the first two cat blocks
(N&C §10.2, Exercise 10.5). -/
def shorPhaseSyndromeX123456 : Observable shorReg :=
  blockXObservable ⊗ (blockXObservable ⊗ Observable.id bitFlipReg)

/-- **`X₄X₅X₆X₇X₈X₉`**, the second Shor phase-flip syndrome observable: identity on block 1,
`X⊗X⊗X` on block 2, `X⊗X⊗X` on block 3. Its `±1` outcome compares the signs of the last two cat
blocks. The two observables share the block-2 factor `X₄X₅X₆`, exactly as `Z₁Z₂` and `Z₂Z₃` share
`Z₂` in the bit-flip syndrome. -/
def shorPhaseSyndromeX456789 : Observable shorReg :=
  Observable.id bitFlipReg ⊗ (blockXObservable ⊗ blockXObservable)

/-- **`X₁X₂X₃X₄X₅X₆` is a self-adjoint involution** — a valid `±1` observable whose two-outcome sign
measurement is the first stage of the phase-flip syndrome. Both nontrivial block factors are
involutions (`blockXObservable_op_mul_self`) and the identity factor trivially so, combined through
`Observable.tmul_op_mul_self`. -/
theorem shorPhaseSyndromeX123456_op_mul_self :
    shorPhaseSyndromeX123456.op * shorPhaseSyndromeX123456.op = 1 :=
  Observable.tmul_op_mul_self blockXObservable_op_mul_self
    (Observable.tmul_op_mul_self blockXObservable_op_mul_self (by simp [Observable.id_op]))

/-- **`X₄X₅X₆X₇X₈X₉` is a self-adjoint involution** — a valid `±1` observable whose two-outcome sign
measurement is the second stage of the phase-flip syndrome. -/
theorem shorPhaseSyndromeX456789_op_mul_self :
    shorPhaseSyndromeX456789.op * shorPhaseSyndromeX456789.op = 1 :=
  Observable.tmul_op_mul_self (by simp [Observable.id_op])
    (Observable.tmul_op_mul_self blockXObservable_op_mul_self blockXObservable_op_mul_self)

/-! ### The three-block cat products and the joint sign-readout law -/

/-- **A three-block product of sign-definite cat states** `catBlockState σ₁ ⊗ (catBlockState σ₂ ⊗
catBlockState σ₃)` on the nine-qubit register. The Shor logical codewords are the equal-sign
products `σ₁ = σ₂ = σ₃` (`|0_L⟩` at `0,0,0`, `|1_L⟩` at `1,1,1`); a phase flip on block `b` flips
`σ_b`, so the general product is exactly the family of states the phase-flip syndrome discriminates.
-/
def shorCatProduct (σ₁ σ₂ σ₃ : Fin 2) : PureState shorReg :=
  catBlockState σ₁ ⊗ (catBlockState σ₂ ⊗ catBlockState σ₃)

/-- **`X₁X₂X₃X₄X₅X₆` reads the product of the first two block signs.** On the three-block cat
product it acts by the scalar `(−1)^{σ₁+σ₂}`: `X⊗X⊗X` reads `(−1)^{σᵢ}` on block `i`
(`blockXObservable_hasEigenstate_catBlockState`), the identity leaves block 3 untouched, and the two
sign factors combine (`Concrete.smul_tmul_smul_tmul_left`). Equivalently, the `±1` outcome is `+1`
iff blocks 1 and 2 agree in sign and `−1` iff they differ. -/
theorem shorPhaseSyndromeX123456_op_shorCatProduct_vec (σ₁ σ₂ σ₃ : Fin 2) :
    shorPhaseSyndromeX123456.op (shorCatProduct σ₁ σ₂ σ₃).vec
      = (-1 : ℂ) ^ ((σ₁ : ℕ) + (σ₂ : ℕ)) • (shorCatProduct σ₁ σ₂ σ₃).vec := by
  have hb₁ : blockXObservable.op (catBlockState σ₁).vec = _ • (catBlockState σ₁).vec :=
    blockXObservable_hasEigenstate_catBlockState σ₁
  have hb₂ : blockXObservable.op (catBlockState σ₂).vec = _ • (catBlockState σ₂).vec :=
    blockXObservable_hasEigenstate_catBlockState σ₂
  simp only [shorCatProduct, PureState.tmul_vec, shorPhaseSyndromeX123456]
  erw [Observable.tmul_op_tmul, Observable.tmul_op_tmul]
  simp only [Observable.id_op, one_apply_eq_self, hb₁, hb₂]
  refine (Concrete.smul_tmul_smul_tmul_left _ _ _ _ _).trans ?_
  congr 1
  push_cast
  ring

/-- **`X₄X₅X₆X₇X₈X₉` reads the product of the last two block signs.** On the three-block cat product
it acts by the scalar `(−1)^{σ₂+σ₃}`: the identity leaves block 1 untouched, `X⊗X⊗X` reads
`(−1)^{σᵢ}` on blocks 2 and 3, and the two sign factors combine
(`Concrete.tmul_smul_tmul_smul_right`). Equivalently, the `±1` outcome is `+1` iff blocks 2 and 3
agree in sign and `−1` iff they differ. -/
theorem shorPhaseSyndromeX456789_op_shorCatProduct_vec (σ₁ σ₂ σ₃ : Fin 2) :
    shorPhaseSyndromeX456789.op (shorCatProduct σ₁ σ₂ σ₃).vec
      = (-1 : ℂ) ^ ((σ₂ : ℕ) + (σ₃ : ℕ)) • (shorCatProduct σ₁ σ₂ σ₃).vec := by
  have hb₂ : blockXObservable.op (catBlockState σ₂).vec = _ • (catBlockState σ₂).vec :=
    blockXObservable_hasEigenstate_catBlockState σ₂
  have hb₃ : blockXObservable.op (catBlockState σ₃).vec = _ • (catBlockState σ₃).vec :=
    blockXObservable_hasEigenstate_catBlockState σ₃
  simp only [shorCatProduct, PureState.tmul_vec, shorPhaseSyndromeX456789]
  erw [Observable.tmul_op_tmul, Observable.tmul_op_tmul]
  simp only [Observable.id_op, one_apply_eq_self, hb₂, hb₃]
  refine (Concrete.tmul_smul_tmul_smul_right _ _ _ _ _).trans ?_
  congr 1
  push_cast
  ring

end AxQM
