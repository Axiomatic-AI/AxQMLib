/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.CnotPauliPropagation
import AxQM.Concrete.TensorScalar

/-!
# AxQM.Postulates.API — support for Toffoli Pauli propagation

Building blocks for the Toffoli-gate error-propagation identities of Nielsen &
Chuang **Exercise 10.67** (the `X`/`Z` commutation rules used to move a Toffoli through Pauli
byproducts in the fault-tolerant π/8 and Toffoli constructions, Exercises 10.66–10.68).

The Toffoli acts on the right-associated three-qubit system `qubit ⊗ (qubit ⊗ qubit)` with controls
on qubits 1, 2 and target qubit 3.  The two propagation rules need a gate the existing vocabulary
does not name — the **controlled-`Z` on the two control wires (qubits 1, 2)** — together with the
diagonal computational-basis actions of that gate and of `Z` on qubit 3.  All three are supplied
here.

## What is formalised

* `controlledZLeftGate = C(Z ⊗ 1)` — the controlled-`Z` on qubits 1, 2 (control qubit 1, phase `Z`
  on qubit 2), qubit 3 untouched.  Mirrors `cnotLeftGate` (`Postulates/API/LeftPairGate.lean`), the
  `CNOT` on the same left pair.
* `controlledZLeftGate_op_apply_qubitBasis` — its diagonal action
  `|q₁,q₂,q₃⟩ ↦ (-1)^{q₁q₂}|q₁,q₂,q₃⟩` (it phase-flips exactly `|11q₃⟩`).
* `pauliZGate_onRight_onRight_op_apply_qubitBasis` — `Z` on qubit 3 acts by `(-1)^{q₃}`.

The propagation rules themselves (Exercise 10.67) are in `AxQM/NC/Ch10/`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The controlled-`Z` gate on the left pair (control qubit 1) -/

/-- **Controlled-`Z` on qubits 1, 2 with control qubit 1**, `|q₁, q₂, q₃⟩ ↦ (-1)^{q₁q₂}|q₁, q₂,
q₃⟩`: the single-qubit-controlled gate `C(Z ⊗ 1)` applying the phase flip `Z` to qubit 2 exactly
when qubit 1 is `|1⟩`, qubit 3 untouched.  The controlled-`Z` companion of `cnotLeftGate`.  Since
the control is qubit 1 this needs no re-bracketing. -/
def controlledZLeftGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  controlledUnitary (pauliZGate.onLeft qubit)

/-- **`controlledZLeftGate` diagonal action:** `|q₁, q₂, q₃⟩ ↦ (-1)^{q₁·q₂}|q₁, q₂, q₃⟩`.  On
control `|0⟩` it is the identity; on control `|1⟩` it applies `Z ⊗ 1` to qubits 2, 3, i.e. the phase
`(-1)^{q₂}` on qubit 2 — so only `|11q₃⟩` acquires a sign. -/
theorem controlledZLeftGate_op_apply_qubitBasis (q1 q2 q3 : Fin 2) :
    controlledZLeftGate.op ((qubitBasis q1).tmul ((qubitBasis q2).tmul (qubitBasis q3))).vec
      = (-1 : ℂ) ^ ((q1 : ℕ) * (q2 : ℕ))
          • ((qubitBasis q1).tmul ((qubitBasis q2).tmul (qubitBasis q3))).vec := by
  rw [← Evolution.evolvePure_vec, controlledZLeftGate]
  fin_cases q1 <;>
    simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, controlledUnitary_evolvePure_ketZero,
      controlledUnitary_evolvePure_ketOne, PureState.tmul_vec, Evolution.evolvePure_vec,
      Evolution.onLeft_op_tmul, pauliZGate_op_apply_qubitBasis, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul, zero_mul, one_mul, pow_zero]
  all_goals first
    | exact (one_smul _ _).symm
    | exact TensorProduct.tmul_smul (R := ℂ) ((-1 : ℂ) ^ (q2 : ℕ)) (qubitBasis 1).vec
        ((qubitBasis q2).vec ⊗ₜ[ℂ] (qubitBasis q3).vec)

/-! ### `Z` on qubit 3 -/

/-- **`Z` on qubit 3 acts by the phase `(-1)^{q₃}`:** `(1 ⊗ 1 ⊗ Z)|q₁, q₂, q₃⟩ = (-1)^{q₃}|q₁, q₂,
q₃⟩`.  The two `onRight`s carry the identity across qubits 1, 2 and `Z|q₃⟩ = (-1)^{q₃}|q₃⟩` supplies
the phase. -/
theorem pauliZGate_onRight_onRight_op_apply_qubitBasis (q1 q2 q3 : Fin 2) :
    ((pauliZGate.onRight qubit).onRight qubit).op
        ((qubitBasis q1).tmul ((qubitBasis q2).tmul (qubitBasis q3))).vec
      = (-1 : ℂ) ^ (q3 : ℕ)
          • ((qubitBasis q1).tmul ((qubitBasis q2).tmul (qubitBasis q3))).vec := by
  rw [PureState.tmul_vec, PureState.tmul_vec]
  have h1 := Evolution.onRight_op_tmul (pauliZGate.onRight qubit) qubit (qubitBasis q1).vec
    ((qubitBasis q2).vec ⊗ₜ[ℂ] (qubitBasis q3).vec)
  rw [h1]
  have h2 := Evolution.onRight_op_tmul pauliZGate qubit (qubitBasis q2).vec (qubitBasis q3).vec
  rw [h2, pauliZGate_op_apply_qubitBasis]
  exact Concrete.tmul_tmul_smul ((-1 : ℂ) ^ (q3 : ℕ)) (qubitBasis q1).vec (qubitBasis q2).vec
    (qubitBasis q3).vec

end AxQM
