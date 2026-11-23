/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CnotXBasis
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.NC.Ch2.Exercise2_52

/-!
# Nielsen & Chuang, Exercise 4.20 (CNOT basis transformations)

*(N&C p. 179.)*

Show CNOT conjugated by Hadamards swaps control/target; give ± basis action.

`CNOT` and the Hadamard gate are closed-system evolutions (Postulate 5 / `Evolution`); the
exercise is a set of statements about how the gate `cnotGate` acts on states of `qubit ⊗ qubit`
(using `cnotGate`, `hadamardGate`, `evolvePure`, `qubitBasis`, `qubitPlus`, `qubitMinus`, `⊗`).

## The formalisation

* `cnotGate_evolvePure_qubitPlus_qubitPlus` — eq. (4.24): `CNOT(|+⟩ ⊗ |+⟩) = |+⟩ ⊗ |+⟩`.
* `cnotGate_evolvePure_qubitMinus_qubitPlus` — eq. (4.25): `CNOT(|-⟩ ⊗ |+⟩) = |-⟩ ⊗ |+⟩`.
* `cnotGate_evolvePure_qubitPlus_qubitMinus` — eq. (4.26): `CNOT(|+⟩ ⊗ |-⟩) = |-⟩ ⊗ |-⟩`.
* `cnotGate_evolvePure_qubitMinus_qubitMinus` — eq. (4.27): `CNOT(|-⟩ ⊗ |-⟩) = |+⟩ ⊗ |-⟩`.
* `cnotGate_evolvePure_hadamard_tmul` — the unifying `X`-basis truth table
  `CNOT(H|a⟩ ⊗ H|b⟩) = H|a ⊕ b⟩ ⊗ H|b⟩`, of which (4.24)–(4.27) are the four instances.
* `cnotGate_hadamardConj_evolvePure_qubitBasis` — **the circuit identity** (the "swaps
  control/target" statement): the Hadamard-conjugated CNOT `(H ⊗ H) · CNOT · (H ⊗ H)` sends the
  computational basis state `|c⟩ ⊗ |t⟩` to `|c ⊕ t⟩ ⊗ |t⟩` — the *reversed* CNOT truth table
  (control on the second qubit, target on the first), the sense in which conjugating by Hadamards
  interchanges control and target.

## Design notes

* **The circuit-identity statement.** N&C's Part 1 is the *gate* equality
  `(H ⊗ H) · CNOT · (H ⊗ H) = CNOT_reversed`. We render it as the action of that conjugated gate on
  every computational basis state, `|c⟩ ⊗ |t⟩ ↦ |c ⊕ t⟩ ⊗ |t⟩` — the reversed CNOT truth table.
  Since the computational product states form a basis and a unitary is determined by its action on a
  basis, this is equivalent to the gate equality, and it makes the "control and target swapped"
  content explicit: the *second* qubit `t` is now the control (it is unchanged and XORed into the
  first), and the *first* qubit `c` is now the target. The library has no separately-named
  reversed-CNOT gate object, so the basis-action characterisation is the self-contained
  statement.
* **The `|±⟩` states are the `X`-eigenstates** `qubitPlus`/`qubitMinus` from
  `AxQM/Postulates/API/RelativePhase.lean`, which are exactly `(|0⟩ ± |1⟩)/√2`; `hadamardGate`
  carries the computational basis to them (`hadamardGate_evolvePure_qubitBasis_zero`/`_one`), so
  `H|a⟩` is `|+⟩`/`|-⟩` and the `X`-basis truth table specialises to (4.24)–(4.27).
* **Proof route.** Each `±`-equation reduces via `PureState.ext` to the vector-level identity
  `cnotGate.op (|±⟩.vec ⊗ |±⟩.vec) = …`, which is
  `cnotGate_op_qubitPlus_qubitPlus_vec` (etc.) proved in `AxQM/Postulates/API/CnotXBasis.lean`
  (expanding `|±⟩` in the computational basis and applying the CNOT truth
  table `cnotGate_op_qubitBasis_tmul` term by term). The unifying
  `X`-basis truth table `cnotGate_evolvePure_hadamard_tmul` collects them; the circuit identity is
  then a short derivation: `(H ⊗ H) · CNOT · (H ⊗ H)` on `|c⟩ ⊗ |t⟩` sends it via `H ⊗ H` to
  `H|c⟩ ⊗ H|t⟩`, then via CNOT (the `X`-basis truth table) to `H|c ⊕ t⟩ ⊗ H|t⟩`, then via `H ⊗ H`
  (Hadamard involution `H² = 1`) back to `|c ⊕ t⟩ ⊗ |t⟩`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The `±`-basis action of `CNOT` (N&C eqs. 4.24–4.27) -/

/-- **N&C eq. (4.24):** `CNOT(|+⟩ ⊗ |+⟩) = |+⟩ ⊗ |+⟩`. -/
theorem cnotGate_evolvePure_qubitPlus_qubitPlus :
    cnotGate.evolvePure (qubitPlus ⊗ qubitPlus) = qubitPlus ⊗ qubitPlus := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec]
  exact cnotGate_op_qubitPlus_qubitPlus_vec

/-- **N&C eq. (4.25):** `CNOT(|-⟩ ⊗ |+⟩) = |-⟩ ⊗ |+⟩`. -/
theorem cnotGate_evolvePure_qubitMinus_qubitPlus :
    cnotGate.evolvePure (qubitMinus ⊗ qubitPlus) = qubitMinus ⊗ qubitPlus := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec]
  exact cnotGate_op_qubitMinus_qubitPlus_vec

/-- **N&C eq. (4.26):** `CNOT(|+⟩ ⊗ |-⟩) = |-⟩ ⊗ |-⟩` — the control flips because the target is
`|-⟩`. -/
theorem cnotGate_evolvePure_qubitPlus_qubitMinus :
    cnotGate.evolvePure (qubitPlus ⊗ qubitMinus) = qubitMinus ⊗ qubitMinus := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec]
  exact cnotGate_op_qubitPlus_qubitMinus_vec

/-- **N&C eq. (4.27):** `CNOT(|-⟩ ⊗ |-⟩) = |+⟩ ⊗ |-⟩` — the control flips because the target is
`|-⟩`. -/
theorem cnotGate_evolvePure_qubitMinus_qubitMinus :
    cnotGate.evolvePure (qubitMinus ⊗ qubitMinus) = qubitPlus ⊗ qubitMinus := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec]
  exact cnotGate_op_qubitMinus_qubitMinus_vec

/-! ### The unifying `X`-basis truth table and the reversed-CNOT circuit identity -/

/-- **`CNOT` in the `X`-eigenbasis:** `CNOT(H|a⟩ ⊗ H|b⟩) = H|a ⊕ b⟩ ⊗ H|b⟩`. Since `H|0⟩ = |+⟩` and
`H|1⟩ = |-⟩`, this collects the four `±`-basis equations (4.24)–(4.27) into one truth table: the
target `H|b⟩` is unchanged, while the control index is XORed with `b` (equivalently, the control
sign flips exactly when the target is `|-⟩`, i.e. `b = 1`). -/
theorem cnotGate_evolvePure_hadamard_tmul (a b : Fin 2) :
    cnotGate.evolvePure
        ((hadamardGate.evolvePure (qubitBasis a)) ⊗ (hadamardGate.evolvePure (qubitBasis b)))
      = (hadamardGate.evolvePure (qubitBasis (a + b)))
        ⊗ (hadamardGate.evolvePure (qubitBasis b)) := by
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.mk_zero, Fin.mk_one, Fin.reduceAdd, hadamardGate_evolvePure_qubitBasis_zero,
      hadamardGate_evolvePure_qubitBasis_one]
  · exact cnotGate_evolvePure_qubitPlus_qubitPlus
  · exact cnotGate_evolvePure_qubitPlus_qubitMinus
  · exact cnotGate_evolvePure_qubitMinus_qubitPlus
  · exact cnotGate_evolvePure_qubitMinus_qubitMinus

/-- **The circuit identity `(H ⊗ H) · CNOT · (H ⊗ H) = CNOT_reversed` (N&C Exercise 4.20, Part 1),
as a reversed truth table.** Conjugating `CNOT` (control on the first qubit, target on the second)
by a Hadamard on each qubit sends the computational basis state `|c⟩ ⊗ |t⟩` to `|c ⊕ t⟩ ⊗ |t⟩`:
the *second* qubit `t` now plays the role of the control (unchanged, and XORed into the first
qubit), while the *first* qubit `c` is the target. Control and target have interchanged roles.

Proof: `(H ⊗ H)` carries `|c⟩ ⊗ |t⟩` to `H|c⟩ ⊗ H|t⟩` (`Evolution.tmul_evolvePure`); `CNOT`
then acts by the `X`-basis truth table `cnotGate_evolvePure_hadamard_tmul` to give
`H|c ⊕ t⟩ ⊗ H|t⟩`; the outer `(H ⊗ H)` and the Hadamard involution `H² = 1`
(`hadamardGate_evolvePure_involutive`) return this to `|c ⊕ t⟩ ⊗ |t⟩`. -/
theorem cnotGate_hadamardConj_evolvePure_qubitBasis (c t : Fin 2) :
    ((hadamardGate ⊗ hadamardGate).comp
          (cnotGate.comp (hadamardGate ⊗ hadamardGate))).evolvePure
        ((qubitBasis c) ⊗ (qubitBasis t))
      = (qubitBasis (c + t)) ⊗ (qubitBasis t) := by
  rw [Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    Evolution.tmul_evolvePure, cnotGate_evolvePure_hadamard_tmul,
    Evolution.tmul_evolvePure, hadamardGate_evolvePure_involutive,
    hadamardGate_evolvePure_involutive]

end AxQM
