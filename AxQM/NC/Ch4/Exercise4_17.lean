/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledZ
import AxQM.NC.Ch2.Exercise2_52

/-!
# Nielsen & Chuang, Exercise 4.17 (Building CNOT from controlled-`Z` gates)

Construct CNOT from one controlled-Z gate and two Hadamard gates.

The controlled-`Z` gate, the Hadamard gate, and `CNOT` are all closed-system evolutions
(Postulate 2 / `Evolution`); the exercise is a *circuit identity* between these gates. The
faithful statement is therefore an equality of `Evolution`s: `CNOT` equals the controlled-`Z` gate
with its **target** qubit conjugated by a Hadamard on each side.

## The formalisation

* `AxQM.cnotGate_eq_hadamard_conj_controlledZGate` — **the exercise:**
  `CNOT = (1 ⊗ H) · CZ · (1 ⊗ H)`, i.e.
  `cnotGate = (Evolution.onRight hadamardGate qubit) · controlledZGate · (Evolution.onRight
  hadamardGate qubit)`. The control qubit is the left factor; the two Hadamards act on the
  **target** (right) qubit via `Evolution.onRight` (`1 ⊗ H`) — the sense in which the exercise asks
  us to specify the control and target qubits: the target is the qubit whose basis the Hadamards
  transform.

It uses `controlledZGate = controlledUnitary pauliZGate` (the controlled-`Z` gate,
`diag(1, 1, 1, -1)`) and the general target-conjugation identity `controlledUnitary_onRight_conj`,
both in `AxQM/Postulates/API/ControlledZ.lean` / `AxQM/Postulates/API/ControlledUnitary.lean`.

## Design notes

* **Why this shape.** N&C fixes the controlled-`Z` gate by its matrix
  `diag(1, 1, 1, -1)`; here that gate is `controlledZGate = controlledUnitary pauliZGate`, whose
  operator `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ Z` *is* that matrix in the computational basis. The construction
  is the exact identity `CNOT = (1 ⊗ H) · CZ · (1 ⊗ H)`, not a weaker "up to phase / on basis
  states" surrogate: it is a genuine equality of the gate `Evolution`s, so it holds on every input,
  as a full unitary identity.
* **Proof.** Immediate from the general circuit identity
  `controlledUnitary_onRight_conj : (1 ⊗ V) · C(U) · (1 ⊗ W) = C(V U W)` (valid when `V W = 1`),
  instantiated at `U = Z`, `V = W = H`: the hypothesis `H H = 1` is `hadamardGate_sq` (Exercise
  2.52), and `V U W = H Z H = X` is `hadamardGate_comp_pauliZGate_comp_hadamardGate` (Exercise 4.13
  at the gate level), so the right-hand side collapses to `C(X) = cnotGate`. The tensor/operator
  work is entirely inside that lemma; the theorem only *applies* it.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.17: `CNOT` from one controlled-`Z` gate and two Hadamards.** The
controlled-`NOT` gate equals the controlled-`Z` gate `controlledZGate` conjugated on its **target**
qubit by a Hadamard on each side:
`cnotGate = (1 ⊗ H) · controlledZGate · (1 ⊗ H)`,
where `Evolution.onRight hadamardGate qubit = 1 ⊗ H` applies `H` to the target (right) qubit while
leaving the control (left) qubit untouched. Instantiating the general target-conjugation identity
`controlledUnitary_onRight_conj` at `U = Z`, `V = W = H` reduces the right-hand side to
`controlledUnitary (H · Z · H) = controlledUnitary X = cnotGate`, using `hadamardGate_sq` (`H² = I`)
and the gate identity `H Z H = X`. -/
theorem cnotGate_eq_hadamard_conj_controlledZGate :
    cnotGate = (Evolution.onRight hadamardGate qubit).comp
      (controlledZGate.comp (Evolution.onRight hadamardGate qubit)) := by
  -- `H H = 1` in the gate monoid (Exercise 2.52), as the `V W = 1` hypothesis of the conjugation
  -- identity.
  have hHH : hadamardGate.comp hadamardGate = Evolution.id := by
    rw [← Evolution.mul_def, ← sq, hadamardGate_sq, Evolution.one_def]
  -- Unfold `cnotGate = C(X)` and `controlledZGate = C(Z)` (both defeq) via `change`, then apply the
  -- conjugation identity and `H Z H = X`.
  change controlledUnitary pauliXGate = (Evolution.onRight hadamardGate qubit).comp
      ((controlledUnitary pauliZGate).comp (Evolution.onRight hadamardGate qubit))
  rw [controlledUnitary_onRight_conj pauliZGate hadamardGate hadamardGate hHH,
    hadamardGate_comp_pauliZGate_comp_hadamardGate]

end AxQM
