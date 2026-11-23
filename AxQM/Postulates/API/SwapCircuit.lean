/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Fredkin
import AxQM.Postulates.API.ControlledUnitaryDecomposition
import AxQM.Postulates.API.ToffoliHadamard

/-!
# AxQM.Postulates.API — the `SWAP` gate as a circuit of `CNOT`s and controlled-`Z`

Circuit identities decomposing the two-qubit `SWAP` gate into `CNOT`s, and the
reversed `CNOT` into a controlled-`Z` conjugated by Hadamards. These are the two-qubit building
blocks of **Nielsen & Chuang Exercise 7.49** (the NMR `SWAP` gate): the exercise says "you may start
from the circuit in Figure 1.7", which is exactly `SWAP = CNOT · CNOT' · CNOT`, and the NMR
apparatus realises each `CNOT` through a controlled-`Z` (Exercise 7.41) plus single-qubit rotations.

## What is here

* `swapGate_eq_cnot_reversedCnot_cnot` — **Figure 1.7**: the `SWAP` gate is three alternating
  `CNOT`s, `SWAP = CNOT · reversedCNOT · CNOT`, where the middle gate `reversedCnotGate` is the
  `CNOT` with control and target interchanged. Proved on the computational basis
  (`twoQubit_evolution_ext`) from the two truth tables `|c,t⟩ ↦ |c, t⊕c⟩` (`CNOT`) and
  `|a,b⟩ ↦ |a⊕b, b⟩` (`reversedCNOT`): tracing `|q₁,q₂⟩` through the three gates gives `|q₂,q₁⟩`,
  the `SWAP` action, using `x ⊕ x = 0` in `Fin 2`.
* `reversedCnotGate_eq_hadamard_conj_controlledZGate` — the **reversed `CNOT` from a controlled-`Z`
  and two Hadamards on the *first* qubit**: `reversedCNOT = (H ⊗ 1) · CZ · (H ⊗ 1)`. This is the
  mirror image of `cnotGate = (1 ⊗ H) · CZ · (1 ⊗ H)` (N&C Exercise 4.17): the reversed `CNOT` has
  its target on the first qubit, so the Hadamards sit on the left factor. Proved algebraically from
  `reversedCNOT = SWAP · CNOT · SWAP` by pushing the two factor-`SWAP`s through the sandwich —
  `SWAP · (1 ⊗ H) · SWAP = H ⊗ 1` (`Evolution.swap_comp_onRight_comp_swap`) and `SWAP · CZ · SWAP =
  CZ` (the symmetry of `CZ`, `controlledZGate_swap_conj_op`).

## Proof ingredients

The statements involve the gates `Evolution.swap`, `cnotGate`, `reversedCnotGate`,
`controlledZGate`, `hadamardGate` and their composites (`Evolution.comp`/`.onLeft`/`.onRight`). The
proofs use the `evolvePure` truth tables and the operator-level `commIsometry`/`mapL` algebra. The
`CNOT`-from-`CZ` and `CZ`-symmetry facts (Exercises 4.17 and 4.18) are derived here from
`controlledUnitary_onRight_conj`, `hadamardGate_comp_pauliZGate_comp_hadamardGate` and
`controlledZGate_swap_conj_op`. Compare `AxQM/Postulates/API/Fredkin.lean`, where `reversedCnotGate`
is defined.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### Swap-conjugation of a single-factor gate -/

/-- **Swap-conjugation exchanges the two factors of a single-factor gate:**
`SWAP · (1 ⊗ V) · SWAP = V ⊗ 1`, i.e. `Evolution.swap · V.onRight S · Evolution.swap = V.onLeft S`.
Conjugating a gate that acts on the *right* factor by the factor-`SWAP` turns it into the same gate
acting on the *left* factor — the operator content of "relabelling which qubit a local gate acts
on". In terms of operators: `SWAP.op = commIsometry` (`Evolution.swap_op_eq`) and
`(1 ⊗ V).op = mapL 1 V.op` (`Evolution.tmul_op`), so this is the identity
`TensorProduct.commIsometry_conj_mapL` (which swaps the two `mapL` arguments) read at
`mapL 1 V.op ↦ mapL V.op 1`. -/
theorem Evolution.swap_comp_onRight_comp_swap (V : Evolution S) :
    (Evolution.swap (S := S)).comp ((V.onRight S).comp (Evolution.swap (S := S))) = V.onLeft S := by
  apply Evolution.ext
  rw [Evolution.comp_op, Evolution.comp_op, Evolution.swap_op_eq, Evolution.onRight,
    Evolution.onLeft, Evolution.tmul_op, Evolution.tmul_op, Evolution.id_op]
  exact TensorProduct.commIsometry_conj_mapL 1 V.op

/-! ### `SWAP` as three `CNOT`s (Figure 1.7) -/

/-- **Nielsen & Chuang, Figure 1.7:** the two-qubit `SWAP` gate is three alternating `CNOT`s,
`SWAP = CNOT · reversedCNOT · CNOT`, where `reversedCnotGate` is the `CNOT` controlled on the second
qubit. Read right to left on `|q₁, q₂⟩`: the first `CNOT` gives `|q₁, q₂ ⊕ q₁⟩`, the reversed `CNOT`
gives `|q₂, q₂ ⊕ q₁⟩` (its first slot becomes `q₁ ⊕ (q₂ ⊕ q₁) = q₂`), and the last `CNOT` gives
`|q₂, q₁⟩` — the `SWAP` action `|q₁, q₂⟩ ↦ |q₂, q₁⟩`. Proved on the four computational basis states
(`twoQubit_evolution_ext`) from the `CNOT`/reversed-`CNOT` truth tables and `Fin 2` arithmetic. -/
theorem swapGate_eq_cnot_reversedCnot_cnot :
    Evolution.swap = cnotGate.comp (reversedCnotGate.comp cnotGate) := by
  apply twoQubit_evolution_ext
  intro q1 q2
  rw [Evolution.swap_evolvePure_tmul, Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    cnotGate_evolvePure_qubitBasis, reversedCnotGate_evolvePure_qubitBasis,
    cnotGate_evolvePure_qubitBasis]
  fin_cases q1 <;> fin_cases q2 <;> rfl

/-! ### The reversed `CNOT` from a controlled-`Z` -/

/-- **The reversed `CNOT` is a controlled-`Z` conjugated by Hadamards on the first qubit:**
`reversedCNOT = (H ⊗ 1) · CZ · (H ⊗ 1)`. The reversed `CNOT` has its target on the *first* qubit
(control on the second), so — mirroring `CNOT = (1 ⊗ H) · CZ · (1 ⊗ H)` (N&C Exercise 4.17) — the
Hadamards conjugate the *left* factor. Proved from the definition
`reversedCNOT = SWAP · CNOT · SWAP` by substituting `CNOT = (1 ⊗ H) · CZ · (1 ⊗ H)` and pushing the
outer `SWAP`s through:
`SWAP · (1 ⊗ H) · SWAP = H ⊗ 1` (`Evolution.swap_comp_onRight_comp_swap`) and the symmetry of the
controlled-`Z`, `SWAP · CZ · SWAP = CZ` (`controlledZGate_swap_conj_op`). -/
theorem reversedCnotGate_eq_hadamard_conj_controlledZGate :
    reversedCnotGate
      = (hadamardGate.onLeft qubit).comp (controlledZGate.comp (hadamardGate.onLeft qubit)) := by
  -- CNOT from CZ and Hadamards on the target (right) qubit, re-derived in-layer (cf. Ex 4.17).
  have cnot_eq : (hadamardGate.onRight qubit).comp
      (controlledZGate.comp (hadamardGate.onRight qubit)) = cnotGate := by
    have h := controlledUnitary_onRight_conj (S := qubit) pauliZGate hadamardGate hadamardGate
      hadamardGate_comp_self
    rwa [hadamardGate_comp_pauliZGate_comp_hadamardGate] at h
  -- The controlled-Z is symmetric between the two qubits (cf. Ex 4.18), at the Evolution level.
  have cz_symm : (Evolution.swap (S := qubit)).comp
      (controlledZGate.comp (Evolution.swap (S := qubit))) = controlledZGate := by
    apply Evolution.ext
    rw [Evolution.comp_op, Evolution.comp_op]
    exact controlledZGate_swap_conj_op
  -- Collapsing an inner SWAP·SWAP pair.
  have swap_swap : ∀ X : Evolution (qubit ⊗ qubit),
      (Evolution.swap (S := qubit)).comp ((Evolution.swap (S := qubit)).comp X) = X := fun X => by
    rw [← Evolution.comp_assoc, Evolution.swap_comp_self, Evolution.id_comp]
  simp only [reversedCnotGate, ← cnot_eq]
  conv_rhs => rw [← cz_symm, ← Evolution.swap_comp_onRight_comp_swap hadamardGate]
  simp only [Evolution.comp_assoc, swap_swap]

end AxQM
