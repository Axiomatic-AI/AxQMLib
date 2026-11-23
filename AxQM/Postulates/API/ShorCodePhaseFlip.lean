/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorCodeBlock
import AxQM.Postulates.API.CnotPauliPropagation

/-!
# AxQM.Postulates.API — block-level phase-flip gates and their sign-flip action

Gates for the phase-flip errors and the recovery operator of one Shor-code
block (Nielsen & Chuang §10.2, Exercises 10.5–10.6). A block is the three-qubit register
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)` carrying a cat state `catBlockVec σ = |000⟩ + (−1)^σ |111⟩`
(from `AxQM/Postulates/API/ShorCodeBlock.lean`). Here we treat the Pauli `Z`s as **unitary gates**
(`Evolution`s), the operational form a phase-flip *error* and its *recovery* both take.

* `blockPhaseFlip i` (`i : Fin 3`) — the phase-flip gate `Z` on the `i`-th physical qubit of a block
  (`Z ⊗ I ⊗ I`, `I ⊗ Z ⊗ I`, `I ⊗ I ⊗ Z`): a phase-flip error on one of the block's three qubits.
* `blockZGate` — the gate `Z ⊗ Z ⊗ Z = Z₁Z₂Z₃` on a block: N&C's phase-flip **recovery** operator
  (Exercise 10.6), the `Z`-analogue of the sign-readout observable `blockXObservable`.

The two structural facts, both proved on the block's cat vectors:

* `blockPhaseFlip_op_catBlockVec` — **a phase flip on any of the three qubits flips the block's
  sign**: `Zᵢ (|000⟩ + (−1)^σ |111⟩) = |000⟩ + (−1)^{σ+1} |111⟩` for every `i`. On a cat vector only
  the all-`0` and all-`1` kets appear, and `Z` fixes `|0⟩`, negates `|1⟩` — so whichever qubit `Zᵢ`
  hits, it negates the `|111⟩` term, changing `|000⟩+|111⟩ ↔ |000⟩−|111⟩` (N&C's description).
* `blockZGate_op_catBlockVec` — `Z₁Z₂Z₃` flips the block's sign the same way: `(−1)³ = −1` on
  `|111⟩`, `+1` on `|000⟩`.

Both reduce to the diagonal-ket laws `blockPhaseFlip_op_qubitThreeBasis_diag` /
`blockZGate_op_qubitThreeBasis_diag`: on `|bbb⟩` a single-qubit `Z` (resp. `Z⊗Z⊗Z`) acts by `(−1)^b`
regardless of which qubit(s) it hits, since all three qubits carry the same bit `b`. The general
Evolution↔PureState bridge `Evolution.evolvePure_normalize_of_op_eq`
(`AxQM/Postulates/API/Evolution.lean`) lifts these operator identities to the normalised
`PureState` level (`catBlockState`) for `AxQM/NC/Ch10/Exercise10_6.lean`.

The scalar-pull-through steps use `AxQM/Concrete/TensorScalar.lean`; the tensor-gate action uses
`Evolution.tmul_op_tmul`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-! ### The phase-flip gates and the recovery gate on a block -/

/-- **The phase-flip gate `Z` on the `i`-th qubit of a block** (`i : Fin 3`), on
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`: `Z ⊗ I ⊗ I`, `I ⊗ Z ⊗ I`, `I ⊗ I ⊗ Z` for `i = 0, 1, 2`.
It models a phase-flip error on one of the block's three physical qubits. -/
def blockPhaseFlip : Fin 3 → Evolution bitFlipReg
  | 0 => pauliZGate ⊗ ((Evolution.id : Evolution qubit) ⊗ (Evolution.id : Evolution qubit))
  | 1 => (Evolution.id : Evolution qubit) ⊗ (pauliZGate ⊗ (Evolution.id : Evolution qubit))
  | 2 => (Evolution.id : Evolution qubit) ⊗ ((Evolution.id : Evolution qubit) ⊗ pauliZGate)

/-- **The recovery gate `Z ⊗ Z ⊗ Z = Z₁Z₂Z₃`** on a block: N&C's phase-flip recovery operator
(Exercise 10.6), the `Z`-analogue of the sign-readout observable `blockXObservable`. -/
def blockZGate : Evolution bitFlipReg :=
  pauliZGate ⊗ (pauliZGate ⊗ pauliZGate)

/-! ### The sign-flip action on the block's cat vectors -/

/-- **A single-qubit `Z` acts by `(−1)^b` on a diagonal ket `|bbb⟩`, regardless of which qubit it
hits.** Since all three qubits of `|bbb⟩` carry the same bit `b`, `Zᵢ |bbb⟩ = (−1)^b |bbb⟩` for
`i = 0, 1, 2` (`Z|0⟩ = |0⟩`, `Z|1⟩ = −|1⟩`). The uniform ingredient behind both sign-flip laws. -/
theorem blockPhaseFlip_op_qubitThreeBasis_diag (i : Fin 3) (b : Fin 2) :
    (blockPhaseFlip i).op (qubitThreeBasis (b, b, b)).vec
      = (-1 : ℂ) ^ (b : ℕ) • (qubitThreeBasis (b, b, b)).vec := by
  fin_cases i
  · change (pauliZGate ⊗ ((Evolution.id : Evolution qubit) ⊗ (Evolution.id : Evolution qubit))).op
        ((qubitBasis b).vec ⊗ₜ[ℂ] ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis b).vec))
      = (-1 : ℂ) ^ (b : ℕ) •
          ((qubitBasis b).vec ⊗ₜ[ℂ] ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis b).vec))
    have h1 := Evolution.tmul_op_tmul pauliZGate
      ((Evolution.id : Evolution qubit) ⊗ (Evolution.id : Evolution qubit)) (qubitBasis b).vec
      ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
    rw [h1, pauliZGate_op_apply_qubitBasis]
    have h2 := Evolution.tmul_op_tmul (Evolution.id : Evolution qubit)
      (Evolution.id : Evolution qubit) (qubitBasis b).vec (qubitBasis b).vec
    rw [h2, Evolution.id_op, one_apply_eq_self]
    exact Concrete.smul_tmul_tmul ((-1 : ℂ) ^ (b : ℕ)) (qubitBasis b).vec (qubitBasis b).vec
      (qubitBasis b).vec
  · change ((Evolution.id : Evolution qubit) ⊗ (pauliZGate ⊗ (Evolution.id : Evolution qubit))).op
        ((qubitBasis b).vec ⊗ₜ[ℂ] ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis b).vec))
      = (-1 : ℂ) ^ (b : ℕ) •
          ((qubitBasis b).vec ⊗ₜ[ℂ] ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis b).vec))
    have h1 := Evolution.tmul_op_tmul (Evolution.id : Evolution qubit)
      (pauliZGate ⊗ (Evolution.id : Evolution qubit)) (qubitBasis b).vec
      ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
    rw [h1, Evolution.id_op, one_apply_eq_self]
    have h2 := Evolution.tmul_op_tmul pauliZGate (Evolution.id : Evolution qubit)
      (qubitBasis b).vec (qubitBasis b).vec
    rw [h2, Evolution.id_op, one_apply_eq_self, pauliZGate_op_apply_qubitBasis]
    exact Concrete.tmul_smul_tmul _ _ _ _
  · change ((Evolution.id : Evolution qubit) ⊗ ((Evolution.id : Evolution qubit) ⊗ pauliZGate)).op
        ((qubitBasis b).vec ⊗ₜ[ℂ] ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis b).vec))
      = (-1 : ℂ) ^ (b : ℕ) •
          ((qubitBasis b).vec ⊗ₜ[ℂ] ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis b).vec))
    have h1 := Evolution.tmul_op_tmul (Evolution.id : Evolution qubit)
      ((Evolution.id : Evolution qubit) ⊗ pauliZGate) (qubitBasis b).vec
      ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
    rw [h1, Evolution.id_op, one_apply_eq_self]
    have h2 := Evolution.tmul_op_tmul (Evolution.id : Evolution qubit) pauliZGate
      (qubitBasis b).vec (qubitBasis b).vec
    rw [h2, Evolution.id_op, one_apply_eq_self, pauliZGate_op_apply_qubitBasis]
    exact Concrete.tmul_tmul_smul _ _ _ _

/-- **A block gate that acts by `(−1)^b` on every diagonal ket `|bbb⟩` flips the cat vector's
sign:** `U (|000⟩ + (−1)^σ |111⟩) = |000⟩ + (−1)^{σ+1} |111⟩`. Only the all-`0` and all-`1` kets
appear in `catBlockVec σ`, and on each the diagonal action `h` contributes `(−1)^0 = 1` /
`(−1)^1 = −1`, so the sign of the `|111⟩` term flips. The shared reason both a `blockPhaseFlip i`
error and the `blockZGate` recovery flip a block's sign. -/
theorem op_catBlockVec_of_op_qubitThreeBasis_diag (U : Evolution bitFlipReg)
    (h : ∀ b : Fin 2, U.op (qubitThreeBasis (b, b, b)).vec
          = (-1 : ℂ) ^ (b : ℕ) • (qubitThreeBasis (b, b, b)).vec) (σ : Fin 2) :
    U.op (catBlockVec σ) = catBlockVec (σ + 1) := by
  rw [catBlockVec, map_add, map_smul, h, h, catBlockVec]
  fin_cases σ <;> simp

/-- **A phase flip on any of the block's three qubits flips its sign.** `Zᵢ (|000⟩ + (−1)^σ |111⟩)
= |000⟩ + (−1)^{σ+1} |111⟩`, i.e. `Zᵢ` swaps `|000⟩+|111⟩ ↔ |000⟩−|111⟩` for every `i` (N&C §10.2:
"a phase flip on any of the first three qubits ... changes `|000⟩+|111⟩` to `|000⟩−|111⟩`, and vice
versa"). Immediate from the diagonal action `blockPhaseFlip_op_qubitThreeBasis_diag` via
`op_catBlockVec_of_op_qubitThreeBasis_diag`. -/
theorem blockPhaseFlip_op_catBlockVec (i : Fin 3) (σ : Fin 2) :
    (blockPhaseFlip i).op (catBlockVec σ) = catBlockVec (σ + 1) :=
  op_catBlockVec_of_op_qubitThreeBasis_diag _ (blockPhaseFlip_op_qubitThreeBasis_diag i) σ

/-- **`Z ⊗ Z ⊗ Z` acts by `(−1)^b` on a diagonal ket `|bbb⟩`.** The three `Z`s each contribute
`(−1)^b`, and their product `(−1)^{3b}` equals `(−1)^b` (same parity). The `Z₁Z₂Z₃` companion of
`blockPhaseFlip_op_qubitThreeBasis_diag`. -/
theorem blockZGate_op_qubitThreeBasis_diag (b : Fin 2) :
    blockZGate.op (qubitThreeBasis (b, b, b)).vec
      = (-1 : ℂ) ^ (b : ℕ) • (qubitThreeBasis (b, b, b)).vec := by
  change (pauliZGate ⊗ (pauliZGate ⊗ pauliZGate)).op
      ((qubitBasis b).vec ⊗ₜ[ℂ] ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis b).vec))
    = (-1 : ℂ) ^ (b : ℕ) • ((qubitBasis b).vec ⊗ₜ[ℂ] ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis b).vec))
  have h1 := Evolution.tmul_op_tmul pauliZGate (pauliZGate ⊗ pauliZGate) (qubitBasis b).vec
    ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
  rw [h1, pauliZGate_op_apply_qubitBasis]
  have h2 := Evolution.tmul_op_tmul pauliZGate pauliZGate (qubitBasis b).vec (qubitBasis b).vec
  rw [h2, pauliZGate_op_apply_qubitBasis]
  refine (Concrete.smul_tmul_smul_tmul_smul _ _ _ _ _ _).trans ?_
  congr 1
  fin_cases b <;> norm_num

/-- **The recovery gate `Z₁Z₂Z₃` flips the block's sign too.** `(Z⊗Z⊗Z)(|000⟩ + (−1)^σ |111⟩)
= |000⟩ + (−1)^{σ+1} |111⟩`: on `|111⟩` the three `Z`s contribute `(−1)³ = −1`, on `|000⟩` they
contribute `+1`. This is why applying `Z₁Z₂Z₃` *after* a phase flip restores the block. -/
theorem blockZGate_op_catBlockVec (σ : Fin 2) :
    blockZGate.op (catBlockVec σ) = catBlockVec (σ + 1) :=
  op_catBlockVec_of_op_qubitThreeBasis_diag _ blockZGate_op_qubitThreeBasis_diag σ

end AxQM
