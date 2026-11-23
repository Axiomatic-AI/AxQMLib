/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasureObservable
import AxQM.Postulates.API.Teleportation

/-!
# AxQM.Postulates.API — computational and `X`-eigenstates of the Pauli gates

Reusable **gate-level** eigenstate facts for the Pauli-`Z` and Pauli-`X` gates, viewed as
`Evolution`s.  The observable analogues (`qubitKet0_hasEigenstate_pauliZ`,
`qubitPlus_hasEigenstate_pauliX`, …) record the *observable* eigenstate of `pauliZObservable` /
`pauliXObservable`; here we record the same facts for the *gates* `pauliZGate`
/ `pauliXGate` (whose operators coincide with the observables'), so that any circuit built from
those gates can read them off directly.

## What is formalised

* `pauliZGate_hasEigenstate_one_qubitBasisZero` / `_negOne_qubitBasisOne` — `Z|0⟩ = |0⟩`,
  `Z|1⟩ = -|1⟩`, from the phase-flip action `pauliZGate_op_apply_qubitBasis`.
* `pauliXGate_hasEigenstate_one_qubitPlus` / `_negOne_qubitMinus` — `X|+⟩ = |+⟩`, `X|-⟩ = -|-⟩`,
  transported from `pauliXObservable_apply_xPlus` / `_apply_xMinus` through
  `pauliXObservable.op = pauliXGate.op`.

They are used in `AxQM/NC/Ch10/Exercise10_58.lean` (the operator-measurement circuits of N&C
Exercise 10.58) and in `AxQM/NC/Ch10/Exercise10_72_ToffoliAncilla.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-! ### Computational eigenstates of the Pauli-`Z` gate -/

/-- **`|0⟩` is the `+1` eigenstate of the Pauli-`Z` gate:** `Z|0⟩ = |0⟩`. -/
theorem pauliZGate_hasEigenstate_one_qubitBasisZero :
    pauliZGate.HasEigenstate 1 (qubitBasis 0) := by
  change pauliZGate.op (qubitBasis 0).vec = (1 : ℂ) • (qubitBasis 0).vec
  rw [pauliZGate_op_apply_qubitBasis]
  norm_num

/-- **`|1⟩` is the `-1` eigenstate of the Pauli-`Z` gate:** `Z|1⟩ = -|1⟩`. -/
theorem pauliZGate_hasEigenstate_negOne_qubitBasisOne :
    pauliZGate.HasEigenstate (-1) (qubitBasis 1) := by
  change pauliZGate.op (qubitBasis 1).vec = (-1 : ℂ) • (qubitBasis 1).vec
  rw [pauliZGate_op_apply_qubitBasis]
  norm_num

/-! ### `X`-eigenstates of the Pauli-`X` gate -/

/-- **`|+⟩` is the `+1` eigenstate of the Pauli-`X` gate:** `X|+⟩ = |+⟩`.  The gate reading of the
observable eigenstate `pauliXObservable_apply_xPlus` (`pauliXObservable.op = pauliXGate.op`). -/
theorem pauliXGate_hasEigenstate_one_qubitPlus :
    pauliXGate.HasEigenstate 1 qubitPlus := by
  change pauliXGate.op qubitPlus.vec = (1 : ℂ) • qubitPlus.vec
  rw [pauliXGate_op, ← pauliXObservable_op, qubitPlus_vec]
  exact pauliXObservable_apply_xPlus

/-- **`|-⟩` is the `-1` eigenstate of the Pauli-`X` gate:** `X|-⟩ = -|-⟩`.  The gate reading of the
observable eigenstate `pauliXObservable_apply_xMinus`. -/
theorem pauliXGate_hasEigenstate_negOne_qubitMinus :
    pauliXGate.HasEigenstate (-1) qubitMinus := by
  change pauliXGate.op qubitMinus.vec = (-1 : ℂ) • qubitMinus.vec
  rw [pauliXGate_op, ← pauliXObservable_op, qubitMinus_vec, pauliXObservable_apply_xMinus]
  congr 1

end AxQM
