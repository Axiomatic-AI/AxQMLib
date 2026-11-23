/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ToffoliPauliPropagation

/-!
# Nielsen & Chuang, Exercise 10.67 (Toffoli error-propagation circuit identities)

*(N&C p. 487.)*

Show the given circuit identities (a) and (b) hold (X/Z propagation through controlled gates).

These are the **Clifford propagation rules for the Toffoli gate** — how a single-qubit Pauli error
on an input commutes to the output — the Toffoli analogues of the `CNOT` rules
`cnotGate_comp_pauliXGate_onLeft` / `cnotGate_comp_pauliZGate_onRight`
(`Postulates/API/CnotPauliPropagation`).  N&C introduces them precisely so that the "commutation
rules from Exercise 10.67" can move the final Toffoli of the fault-tolerant construction "all the
way back to the left side" in Exercise 10.68.

The Toffoli, the single-qubit Paulis, `CNOT`, and controlled-`Z` are all closed-system evolutions
(Postulate 5 / `Evolution`); each identity is an equality of gates on the right-associated
three-qubit system `qubit ⊗ (qubit ⊗ qubit)`, with controls on qubits 1, 2 and target qubit 3.

## The two circuit identities (the exercise's claim)

* `toffoliGate_comp_pauliXGate_control_propagates` — **identity (a):** an `X` on the first control
  copies onto the target *conditioned on the second control*, `T·X₁ = (X₁·CNOT₂₃)·T`.  Flipping
  control 1 before the Toffoli changes whether the target is flipped exactly when control 2 is `|1⟩`
  — a `CNOT` from qubit 2 to qubit 3 — so pushing the `X₁` past the Toffoli leaves that `CNOT₂₃`
  behind (`CNOT₂₃ = cnotGate.onRight qubit = 1 ⊗ CNOT`).
* `toffoliGate_comp_pauliZGate_target_propagates` — **identity (b):** a `Z` on the target copies
  *back* onto the two controls as a controlled-`Z`, `T·Z₃ = (Z₃·CZ₁₂)·T`.  A `Z` on the target
  multiplies `|t⟩` by `(-1)ᵗ`; after the Toffoli sends `t ↦ t ⊕ q₁q₂`, that phase reads
  `(-1)^{t ⊕ q₁q₂} = (-1)ᵗ(-1)^{q₁q₂}` (the exponents differ by an even `2q₁q₂`), i.e. the original
  `Z` on the target *and* a `(-1)^{q₁q₂}` controlled-`Z` on the controls
  (`CZ₁₂ = controlledZLeftGate`).

## Design notes

* **Fidelity / statement shape.**  N&C draws each identity as an equality of the two three-qubit
  *circuits* (Figure, p. 488), so they are rendered as genuine `Evolution` equalities on
  `qubit ⊗ (qubit ⊗ qubit)` — holding on every input, not up to phase or on selected states — in the
  **commutation form** `T·P = P'·T` (the form the Exercise 10.68 gate-moving argument uses), exactly
  parallel to the `CNOT` propagation rules.
* **Proof.**  Each identity is verified on the eight computational-basis inputs via
  `threeQubit_evolution_ext`.  Identity (a) is a permutation fact (Toffoli, `X`, `CNOT` are all
  bit-permutations), so it stays at the `PureState`/`evolvePure` level: both sides send
  `|q₁,q₂,q₃⟩` to `|q₁⊕1, q₂, q₃ ⊕ (q₁⊕1)q₂⟩ = |q₁⊕1, q₂, q₃ ⊕ q₁q₂ ⊕ q₂⟩` (using
  `toffoliGate_evolvePure_qubitBasis`, `cnotGate_evolvePure_qubitBasis` and the `X` truth table).
  Identity (b) carries the phase `Z|q₃⟩ = (-1)^{q₃}|q₃⟩`, so it descends to the vector level where
  the sign is a scalar, using the diagonal actions
  `controlledZLeftGate_op_apply_qubitBasis` and `pauliZGate_onRight_onRight_op_apply_qubitBasis`
  (`Postulates/API/ToffoliPauliPropagation`) and `toffoliGate_op_qubitBasis_vec`; the two phases
  on the right multiply to `(-1)^{q₁q₂}·(-1)^{q₃⊕q₁q₂} = (-1)^{q₃}`, the phase on the left.
* **Reuse.**  The controlled-`Z` on the two control wires — the gate the exercise draws but the
  existing vocabulary does not name — is factored out as `controlledZLeftGate` in
  `Postulates/API/ToffoliPauliPropagation` (the sibling of `cnotLeftGate`), together with the two
  op-level diagonal actions the phase bookkeeping needs.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Identity (a) of N&C Exercise 10.67:** an `X` on the first control of the Toffoli propagates,
past the gate, to an `X` on that control together with a `CNOT` from the second control to the
target: `T · X₁ = (X₁ · CNOT₂₃) · T` on `qubit ⊗ (qubit ⊗ qubit)`, where `X₁ = pauliXGate.onLeft
(qubit ⊗ qubit)` and `CNOT₂₃ = cnotGate.onRight qubit`.  Both sides send `|q₁,q₂,q₃⟩` to
`|q₁⊕1, q₂, q₃ ⊕ (q₁⊕1)·q₂⟩`; a permutation identity, verified on the computational basis. -/
theorem toffoliGate_comp_pauliXGate_control_propagates :
    toffoliGate.comp (pauliXGate.onLeft (qubit ⊗ qubit))
      = ((pauliXGate.onLeft (qubit ⊗ qubit)).comp (cnotGate.onRight qubit)).comp toffoliGate := by
  apply threeQubit_evolution_ext
  intro q1 q2 q3
  simp only [Evolution.evolvePure_comp, Evolution.onLeft_evolvePure, Evolution.onRight_evolvePure,
    pauliXGate_evolvePure_qubitBasis, cnotGate_evolvePure_qubitBasis,
    toffoliGate_evolvePure_qubitBasis]
  fin_cases q1 <;> fin_cases q2 <;> fin_cases q3 <;> rfl

/-- **Identity (b) of N&C Exercise 10.67:** a `Z` on the Toffoli target propagates, past the gate,
*back* to a `Z` on the target together with a controlled-`Z` between the two controls:
`T · Z₃ = (Z₃ · CZ₁₂) · T` on `qubit ⊗ (qubit ⊗ qubit)`, where `Z₃ = (pauliZGate.onRight
qubit).onRight qubit` and `CZ₁₂ = controlledZLeftGate`.  The target's phase `(-1)^{q₃}` is read
through the Toffoli's `q₃ ↦ q₃ ⊕ q₁q₂`, producing the extra `(-1)^{q₁q₂}` controlled-`Z`; verified
on the computational basis at the vector level, where the phases are scalars. -/
theorem toffoliGate_comp_pauliZGate_target_propagates :
    toffoliGate.comp ((pauliZGate.onRight qubit).onRight qubit)
      = (((pauliZGate.onRight qubit).onRight qubit).comp controlledZLeftGate).comp toffoliGate := by
  apply threeQubit_evolution_ext
  intro q1 q2 q3
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, Evolution.comp_op, ContinuousLinearMap.comp_apply,
    pauliZGate_onRight_onRight_op_apply_qubitBasis, map_smul, toffoliGate_op_qubitBasis_vec,
    controlledZLeftGate_op_apply_qubitBasis, smul_smul]
  congr 1
  fin_cases q1 <;> fin_cases q2 <;> fin_cases q3 <;> simp

end AxQM
