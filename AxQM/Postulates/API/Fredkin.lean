/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.Swap

/-!
# AxQM.Postulates.API — the Fredkin (controlled-`SWAP`) gate and its construction gates

Infrastructure for Nielsen & Chuang **Exercise 4.25** (Fredkin gate construction):
the controlled-`SWAP` gate `fredkinGate` together with the two auxiliary gates its three-Toffoli
construction is built from — a reversed `CNOT` and the "middle" Toffoli (controls on qubits 1 and
3, target qubit 2). It sits above `ControlledControlledUnitary` (supplying `ccontrolledUnitary`,
`toffoliGate`, and the three-qubit extensionality bridge) and `Swap`.

## What is formalised

* `fredkinGate` — the **Fredkin gate** `C(SWAP)` on `qubit ⊗ (qubit ⊗ qubit)`: the single-qubit
  controlled gate `controlledUnitary` applied to the two-qubit `SWAP`, i.e. it swaps qubits 2 and 3
  exactly when the control qubit 1 is `|1⟩`. This is precisely the transform of N&C eq. (4.30).
* `fredkinGate_evolvePure_ketZero_left` / `fredkinGate_evolvePure_ketOne_left` — the **defining
  action** (the two diagonal blocks of the matrix 4.30): control `|0⟩` leaves the pair untouched,
  `C(SWAP)(|0⟩ ⊗ ψ) = |0⟩ ⊗ ψ`; control `|1⟩` swaps the pair, `C(SWAP)(|1⟩ ⊗ |a⟩ ⊗ |b⟩) =
  |1⟩ ⊗ |b⟩ ⊗ |a⟩`.
* `reversedCnotGate` — `CNOT` with the roles of the two qubits interchanged (control on the second
  qubit, target on the first), realised as the swap-conjugate `SWAP · CNOT · SWAP`; its truth table
  is `|a, b⟩ ↦ |a ⊕ b, b⟩` (`reversedCnotGate_evolvePure_qubitBasis`).
* `middleToffoliGate` — the doubly-controlled `X` with controls on qubits 1 and 3 and target
  qubit 2, `C(reversedCNOT)`; its truth table is `|c, a, b⟩ ↦ |c, a ⊕ c·b, b⟩`
  (`middleToffoliGate_evolvePure_qubitBasis`). This is the middle gate of the swap construction — a
  Toffoli whose target is qubit 2 rather than qubit 3.

## Design notes

* **`fredkinGate = C(SWAP)` (N&C fidelity).** The Fredkin gate is the *controlled-swap*: conditioned
  on the control qubit, it applies the two-qubit `SWAP` to the target pair. On the right-associated
  three-qubit system `qubit ⊗ (qubit ⊗ qubit)` (control ⊗ (target₁ ⊗ target₂)) this is literally
  `controlledUnitary (Evolution.swap)`, with no associator bookkeeping, and its two control branches
  are exactly the identity/permutation blocks of the matrix (4.30). A value of
  `Evolution (qubit ⊗ (qubit ⊗ qubit))` cannot be formed without the underlying unitarity,
  inherited here from `controlledUnitary` and `Evolution.swap`.
* **Why a reversed `CNOT` and a permuted Toffoli.** The standard swap identity
  `SWAP = CNOT · reversedCNOT · CNOT` (N&C §1.3.4) has its middle `CNOT` running the *opposite*
  direction; controlling the whole identity on qubit 1 therefore produces two ordinary Toffolis
  (`toffoliGate`, target qubit 3) around one Toffoli whose control/target roles on qubits 2, 3 are
  interchanged (`middleToffoliGate`, target qubit 2). Both auxiliary gates are defined by
  conjugation/controlling of gates already in the library, so they are automatically unitary
  `Evolution`s, and their truth tables follow from the `controlledUnitary`/`SWAP`/`CNOT` action
  lemmas one tensor factor at a time.
* **Related declarations.** The statements here use only `controlledUnitary`, `Evolution.swap`,
  `cnotGate`, `evolvePure`, `⊗` and `qubitBasis`. The gates are built directly on the
  controlled-gate API, alongside `cnotGate`, `toffoliGate`, and `Evolution.swap`. Exercise 4.25's
  construction theorems (which are pure `Evolution` equalities) are in
  `AxQM/NC/Ch4/Exercise4_25.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The Fredkin (controlled-`SWAP`) gate -/

/-- **The Fredkin gate** `C(SWAP)` (Nielsen & Chuang §1.3.4, eq. 4.30): the `Evolution` on the
three-qubit system `qubit ⊗ (qubit ⊗ qubit)` that swaps the last two (target) qubits exactly when
the first (control) qubit is `|1⟩`. It is the single-qubit-controlled gate `controlledUnitary`
applied to the two-qubit `SWAP`, so it is a genuine unitary `Evolution` with no new obligation. -/
def fredkinGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  controlledUnitary (Evolution.swap (S := qubit))

/-- **Fredkin, control `|0⟩`** (upper-left identity block of matrix 4.30): the target pair is
untouched, `C(SWAP)(|0⟩ ⊗ ψ) = |0⟩ ⊗ ψ`. -/
theorem fredkinGate_evolvePure_ketZero_left (ψ : PureState (qubit ⊗ qubit)) :
    fredkinGate.evolvePure ((qubitBasis 0) ⊗ ψ) = (qubitBasis 0) ⊗ ψ :=
  controlledUnitary_evolvePure_ketZero (Evolution.swap (S := qubit)) ψ

/-- **Fredkin, control `|1⟩`** (lower-right swap block of matrix 4.30): the target pair is swapped,
`C(SWAP)(|1⟩ ⊗ |a⟩ ⊗ |b⟩) = |1⟩ ⊗ |b⟩ ⊗ |a⟩`. -/
theorem fredkinGate_evolvePure_ketOne_left (a b : Fin 2) :
    fredkinGate.evolvePure ((qubitBasis 1) ⊗ ((qubitBasis a) ⊗ (qubitBasis b)))
      = (qubitBasis 1) ⊗ ((qubitBasis b) ⊗ (qubitBasis a)) := by
  rw [fredkinGate, controlledUnitary_evolvePure_ketOne, Evolution.swap_evolvePure_tmul]

/-! ### The reversed `CNOT` and the middle Toffoli of the swap construction -/

/-- **The reversed `CNOT`**: the controlled-`NOT` with control on the *second* qubit and target on
the *first*, obtained by conjugating `cnotGate` with the factor swap, `reversedCNOT = SWAP · CNOT ·
SWAP`. Its truth table is `|a, b⟩ ↦ |a ⊕ b, b⟩` (`reversedCnotGate_evolvePure_qubitBasis`). -/
def reversedCnotGate : Evolution (qubit ⊗ qubit) :=
  (Evolution.swap (S := qubit)).comp (cnotGate.comp (Evolution.swap (S := qubit)))

/-- **The reversed-`CNOT` truth table:** `reversedCNOT|a, b⟩ = |a ⊕ b, b⟩` (`a + b` in `Fin 2`) —
the second qubit is the control (unchanged) and the first qubit is the target. Computed from
`SWAP · CNOT · SWAP` factor by factor. -/
theorem reversedCnotGate_evolvePure_qubitBasis (a b : Fin 2) :
    reversedCnotGate.evolvePure ((qubitBasis a) ⊗ (qubitBasis b))
      = (qubitBasis (a + b)) ⊗ (qubitBasis b) := by
  rw [reversedCnotGate, Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    Evolution.swap_evolvePure_tmul, cnotGate_evolvePure_qubitBasis, Evolution.swap_evolvePure_tmul]

/-- **The middle Toffoli** of the Fredkin swap construction: the doubly-controlled `X` with controls
on qubits 1 and 3 and target qubit 2, realised as `C(reversedCNOT)`. It is the middle of the three
Toffoli gates, differing from `toffoliGate` only in that its target is qubit 2 rather than qubit 3.
Its truth table is `|c, a, b⟩ ↦ |c, a ⊕ c·b, b⟩` (`middleToffoliGate_evolvePure_qubitBasis`). -/
def middleToffoliGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  controlledUnitary reversedCnotGate

/-- **The middle-Toffoli truth table:** `middleToffoli|c, a, b⟩ = |c, a ⊕ c·b, b⟩` — controls on
qubits 1 (`c`) and 3 (`b`), target qubit 2 (`a`), which is flipped exactly when both controls are
`1`. -/
theorem middleToffoliGate_evolvePure_qubitBasis (c a b : Fin 2) :
    middleToffoliGate.evolvePure ((qubitBasis c) ⊗ ((qubitBasis a) ⊗ (qubitBasis b)))
      = (qubitBasis c) ⊗ ((qubitBasis (a + c * b)) ⊗ (qubitBasis b)) := by
  rw [middleToffoliGate]
  fin_cases c <;>
    simp only [Fin.mk_zero, Fin.mk_one, controlledUnitary_evolvePure_ketZero,
      controlledUnitary_evolvePure_ketOne, reversedCnotGate_evolvePure_qubitBasis, zero_mul,
      one_mul, add_zero]

end AxQM
