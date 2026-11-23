/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Fredkin
import AxQM.Postulates.API.Associator
import AxQM.Postulates.API.SystemIsoComm

/-!
# AxQM.Postulates.API — CNOT / reversed-CNOT on the *left pair* of three qubits

The two `CNOT` placements that act on qubits **1 and 2** of the right-associated three-qubit
system `qubit ⊗ (qubit ⊗ qubit)`, leaving qubit 3 untouched. The existing gate
vocabulary (`cnotGate.onRight`, `reversedCnotGate.onRight`, `toffoliGate`,
`middleToffoliGate`) only reaches qubits 2 and 3, or uses qubit 1 as a *control*; nothing flips
qubit 1. These two gates fill that gap and are reused by any circuit that must act on the first
qubit as a target (e.g. N&C Exercise 4.27's partial cyclic permutation).

## What is formalised

* `Evolution.congr_evolvePure_congr` — the **transport law for gate action** through a system
  isomorphism: `(U.congr e)` acts on the transported state `ψ.congr e` exactly as the transport of
  `U`'s action, `(U.congr e).evolvePure (ψ.congr e) = (U.evolvePure ψ).congr e`. This is the general
  lemma that lets a gate defined on one bracketing of a composite be evaluated on the other.
* `cnotLeftGate` — the `CNOT` with control qubit 1 and target qubit 2 (`|q₁,q₂,q₃⟩ ↦
  |q₁, q₂⊕q₁, q₃⟩`), realised as `C(X ⊗ 1)` (a single-qubit-controlled gate, so no re-bracketing is
  needed). Truth table `cnotLeftGate_evolvePure_qubitBasis`.
* `reversedCnotLeftGate` — the `CNOT` with control qubit 2 and target qubit 1 (`|q₁,q₂,q₃⟩ ↦
  |q₁⊕q₂, q₂, q₃⟩`). Its target is qubit 1, unreachable by the controlled-gate constructors, so it
  is the two-qubit `reversedCnotGate` placed on the left pair `(qubit ⊗ qubit) ⊗ qubit` via
  `onLeft` and transported to the right-associated system by the associator. Truth table
  `reversedCnotLeftGate_evolvePure_qubitBasis`.

## Design notes

* **Why the associator (`reversedCnotLeftGate`).** Every `CNOT`/Toffoli already in the library
  either uses qubit 1 as a control (`controlledUnitary`, `ccontrolledUnitary`) or acts on the right
  pair (`onRight`); none targets qubit 1, because in the right-associated `qubit ⊗ (qubit ⊗ qubit)`
  a gate on qubits 1, 2 is not of `onRight`/`controlledUnitary` form. The honest fix is to place the
  genuine two-qubit `reversedCnotGate` on the *left* pair of the left-associated
  `(qubit ⊗ qubit) ⊗ qubit` (`reversedCnotGate.onLeft qubit`) and carry it across the associator
  system-isomorphism `QSystem.assoc` with `Evolution.congr`. `Evolution.congr_evolvePure_congr` then
  turns the truth table into the same one-tensor-factor-at-a-time computation as the other gates.
* **`cnotLeftGate` needs no associator.** A `CNOT` whose *control* is qubit 1 and target qubit 2 is
  just `C(U)` with `U = X ⊗ 1` acting on the target pair, so `controlledUnitary (pauliXGate.onLeft
  qubit)` places it directly on the right-associated system with the standard control-branch lemmas.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### Transport of gate action through a system isomorphism -/

/-- **Transport law for gate action.** A gate transported along a system isomorphism `e` acts on a
transported state exactly as the transport of the original action:
`(U.congr e).evolvePure (ψ.congr e) = (U.evolvePure ψ).congr e`. Both sides have underlying vector
`e (U.op ψ.vec)`: the left because conjugating `U.op` by `e` and then feeding `e ψ.vec` cancels the
inner `e⁻¹ ∘ e`; the right by definition of `PureState.congr` and `evolvePure`. -/
theorem Evolution.congr_evolvePure_congr {S T : QSystem} (e : S.Iso T) (U : Evolution S)
    (ψ : PureState S) :
    (U.congr e).evolvePure (ψ.congr e) = (U.evolvePure ψ).congr e := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, Evolution.congr_op, PureState.congr_vec, PureState.congr_vec,
    Evolution.evolvePure_vec]
  simp [LinearIsometryEquiv.conjStarAlgEquiv_apply]

/-- **Symm-transport law for gate action.** The `e.symm` companion of
`Evolution.congr_evolvePure_congr`: pulling the transported gate action `(U.congr e).evolvePure ψ`
back along `e.symm` is the transport-back of the original action —
`congr e.symm ((U.congr e).evolvePure ψ) = U.evolvePure (congr e.symm ψ)`. Rewriting the left side
backward through the forward law `Evolution.congr_evolvePure_congr` moves the outer `congr e.symm`
inside — onto both the gate `U.congr e` and the state `ψ` — and the gate's roundtrip `e.symm ∘ e`
then cancels (`Evolution.congr_symm_congr`).
Used to move a gate action between the two frames of a system isomorphism when the *state* is on the
target side `T` (e.g. transporting a joint dilation between the parties∣ancillas and Alice∣Bob cuts
of Nielsen & Chuang Exercise 12.22). -/
theorem Evolution.evolvePure_congr_symm {S T : QSystem} (e : S.Iso T) (U : Evolution S)
    (ψ : PureState T) :
    PureState.congr e.symm ((Evolution.congr e U).evolvePure ψ)
      = U.evolvePure (PureState.congr e.symm ψ) := by
  rw [← Evolution.congr_evolvePure_congr, Evolution.congr_symm_congr]

/-- **A transported gate acts on states by conjugation.** For `e : S ≃ₛ T`, gate `V` on `S`, and
state `χ` on `T`, `(congr e V).evolvePure χ = congr e (V.evolvePure (congr e.symm χ))`: pull `χ`
back along `e.symm`, evolve by `V`, push forward along `e`. The arbitrary-target form sitting
between
`Evolution.congr_evolvePure_congr` (state on the source side) and `Evolution.evolvePure_congr_symm`
(the `e.symm` frame): rewrite the left side backward through the roundtrip
`PureState.congr_congr_symm`, then `Evolution.evolvePure_congr_symm` moves `V` across the frame. -/
theorem Evolution.evolvePure_congr {S T : QSystem} (e : S.Iso T) (V : Evolution S)
    (χ : PureState T) :
    (Evolution.congr e V).evolvePure χ
      = PureState.congr e (V.evolvePure (PureState.congr e.symm χ)) := by
  rw [← PureState.congr_congr_symm e ((Evolution.congr e V).evolvePure χ),
    Evolution.evolvePure_congr_symm]

/-! ### `CNOT` on the left pair, control qubit 1 -/

/-- **`CNOT` on qubits 1, 2 with control qubit 1**, `|q₁, q₂, q₃⟩ ↦ |q₁, q₂ ⊕ q₁, q₃⟩`: the
single-qubit-controlled gate `C(X ⊗ 1)` flipping qubit 2 exactly when qubit 1 is `|1⟩`, qubit 3
untouched. Since the control is qubit 1 this needs no re-bracketing. -/
def cnotLeftGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  controlledUnitary (pauliXGate.onLeft qubit)

/-- **`cnotLeftGate` truth table:** `|q₁, q₂, q₃⟩ ↦ |q₁, q₂ ⊕ q₁, q₃⟩` (control qubit 1, target
qubit 2). -/
theorem cnotLeftGate_evolvePure_qubitBasis (q1 q2 q3 : Fin 2) :
    cnotLeftGate.evolvePure ((qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)))
      = (qubitBasis q1) ⊗ ((qubitBasis (q2 + q1)) ⊗ (qubitBasis q3)) := by
  rw [cnotLeftGate]
  fin_cases q1 <;>
    simp only [Fin.mk_zero, Fin.mk_one, controlledUnitary_evolvePure_ketZero,
      controlledUnitary_evolvePure_ketOne, Evolution.onLeft, Evolution.tmul_evolvePure,
      pauliXGate_evolvePure_qubitBasis, Evolution.id_evolvePure, add_zero]

/-! ### Reversed `CNOT` on the left pair, target qubit 1 -/

/-- **`CNOT` on qubits 1, 2 with control qubit 2**, `|q₁, q₂, q₃⟩ ↦ |q₁ ⊕ q₂, q₂, q₃⟩`: the
two-qubit `reversedCnotGate` (control second, target first) placed on the left pair
`(qubit ⊗ qubit) ⊗ qubit` and transported to the right-associated three-qubit system by the
associator. Its target is qubit 1, unreachable by the controlled-gate constructors. -/
def reversedCnotLeftGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (reversedCnotGate.onLeft qubit).congr (QSystem.assoc qubit qubit qubit).symm

/-- The associator (backwards) on a computational-basis state re-brackets left to right:
`((ψ ⊗ φ) ⊗ χ).congr (assoc).symm = ψ ⊗ (φ ⊗ χ)`. -/
theorem pureState_congr_assocSymm {A B C : QSystem} (ψ : PureState A) (φ : PureState B)
    (χ : PureState C) :
    ((ψ ⊗ φ) ⊗ χ).congr (QSystem.assoc A B C).symm = ψ ⊗ (φ ⊗ χ) := by
  apply PureState.ext
  rw [PureState.congr_vec, PureState.tmul_vec, PureState.tmul_vec, PureState.tmul_vec,
    PureState.tmul_vec, show (QSystem.assoc A B C).symm.toIsometry
      = (TensorProduct.assocIsometry ℂ A.space B.space C.space).symm.symm from rfl,
    LinearIsometryEquiv.symm_symm]
  exact (TensorProduct.assocIsometry_apply _).trans (TensorProduct.assoc_tmul ψ.vec φ.vec χ.vec)

/-- **`reversedCnotLeftGate` truth table:** `|q₁, q₂, q₃⟩ ↦ |q₁ ⊕ q₂, q₂, q₃⟩` (control qubit 2,
target qubit 1). Computed by re-bracketing to the left pair (`pureState_congr_assocSymm`), running
`reversedCnotGate` on qubits 1, 2 (`Evolution.congr_evolvePure_congr`), and re-bracketing back. -/
theorem reversedCnotLeftGate_evolvePure_qubitBasis (q1 q2 q3 : Fin 2) :
    reversedCnotLeftGate.evolvePure ((qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)))
      = (qubitBasis (q1 + q2)) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)) := by
  rw [reversedCnotLeftGate, ← pureState_congr_assocSymm (qubitBasis q1) (qubitBasis q2)
    (qubitBasis q3), Evolution.congr_evolvePure_congr, Evolution.onLeft,
    Evolution.tmul_evolvePure, reversedCnotGate_evolvePure_qubitBasis, Evolution.id_evolvePure,
    pureState_congr_assocSymm]

end AxQM
