/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch4.Exercise4_31
import AxQM.NC.Ch4.Exercise4_20
import AxQM.Postulates.API.Fredkin
import AxQM.Postulates.API.ControlledUnitaryDecomposition
import AxQM.Postulates.API.ToffoliHadamard
import AxQM.Postulates.API.AugmentedOracleBlock
import AxQM.Postulates.API.EvolutionTensorHom

/-!
# Nielsen & Chuang, Exercise 10.64 (Back propagation of errors)

*(N&C p. 484.)*

Z error on CNOT target propagates back to control; show via stabilizer formalism and circuit
identities.

`CNOT`, the single-qubit Pauli gates, and the Hadamard gate are closed-system evolutions
(Postulate 5 / `Evolution`); each statement is an equality of gates on `qubit ⊗ qubit`. Qubit 1 is
the *left* tensor factor (the control) and qubit 2 the *right* factor (the target), so
`P₁ = P.onLeft qubit` (`= P ⊗ 1`) and `P₂ = P.onRight qubit` (`= 1 ⊗ P`); the conjugation `C·P·C`
is `cnotGate.comp (P.comp cnotGate)`.

## The two error-propagation facts (the exercise's claim)

* `cnotGate_pauliXGate_control_propagates` — the "clear" fact: an `X` on the control copies onto the
  target, `C·X₁·C = X₁·X₂` (N&C eq. 4.32).
* `cnotGate_pauliZGate_target_backPropagates` — the surprising fact, **via the stabilizer
  formalism**: a `Z` on the target copies *back* onto the control, `C·Z₂·C = Z₁·Z₂` (N&C eq. 4.37).

## The circuit-identity view (the "directly using circuit identities" method)

The two facts are the *same phenomenon* seen in conjugate bases, which is exactly what Exercise 4.20
makes precise: conjugating `CNOT` by a Hadamard on each qubit interchanges the roles of control and
target.

* `hadamardConj_cnotGate_eq_reversedCnotGate` — **the Exercise 4.20 circuit identity, as a gate
  equality**: `(H ⊗ H) · CNOT · (H ⊗ H) = reversedCNOT`, where `reversedCNOT` is the `CNOT` with the
  *second* qubit as control and the *first* as target. (Exercise 4.20 established this as a reversed
  truth table on the computational basis; this is its operator form, now that a first-class
  `reversedCnotGate` object exists.)
* `reversedCnotGate_pauliXGate_control_propagates` — the mirror of eq. 4.32 for the reversed gate:
  an `X` on `reversedCNOT`'s control (the *second* qubit) copies onto its target (the *first*),
  `R·X₂·R = X₁·X₂`.

Reading the back-propagation off these: a `Z` on the target is an `X` on the target *in the
`X`-eigenbasis* (`Z = H·X·H`); passing to that basis turns `CNOT` into `reversedCNOT`
(`hadamardConj_cnotGate_eq_reversedCnotGate`), whose control is the *second* qubit; the `X` there
propagates onto the *first* qubit (`reversedCnotGate_pauliXGate_control_propagates`); returning to
the computational basis turns those `X`s back into `Z`s — a `Z` on *both* qubits. So the `Z` on the
target has propagated back to the control, exactly as the stabilizer calculation
`cnotGate_pauliZGate_target_backPropagates` shows directly.

## Design notes

* **Fidelity / statement shape.** N&C states both propagations as operator facts about `CNOT`
  (`CX₁C = X₁X₂`, `CZ₂C = Z₁Z₂`), so we render them as genuine `Evolution` equalities on
  `qubit ⊗ qubit` (not actions on selected states, not up to phase), matching Exercise 4.31.
* **Both methods.** The stabilizer method is the conjugation identity itself: the two facts are
  discharged by the Exercise 4.31 results `cnotGate_conj_pauliXGate_onLeft` (eq. 4.32) and
  `cnotGate_conj_pauliZGate_onRight` (eq. 4.37) — each proved there from a Clifford *commutation*
  rule and the `CNOT` involution via `Evolution.comp_comp_self_of_comm`. The circuit-identity method
  is Exercise 4.20's role reversal, now packaged as the gate equality
  `hadamardConj_cnotGate_eq_reversedCnotGate`, together with the reversed-gate propagation
  `reversedCnotGate_pauliXGate_control_propagates`.
* **Proof routes (no new infrastructure).** `hadamardConj_cnotGate_eq_reversedCnotGate` lifts the
  two computational-basis truth tables `cnotGate_hadamardConj_evolvePure_qubitBasis` (Exercise 4.20)
  and `reversedCnotGate_evolvePure_qubitBasis` (`Postulates/API/Fredkin`) — which both send
  `|c⟩ ⊗ |t⟩ ↦ |c ⊕ t⟩ ⊗ |t⟩` — to a gate equality via `twoQubit_evolution_ext` (a two-qubit gate
  is determined by its action on the computational basis). `reversedCnotGate_pauliXGate_control_`
  `propagates` is the same computational verification: both sides send `|q₁⟩ ⊗ |q₂⟩` to
  `|q₁ ⊕ 1⟩ ⊗ |q₂ ⊕ 1⟩`, tracking `reversedCNOT`'s `|a, b⟩ ↦ |a ⊕ b, b⟩` truth table twice around a
  bit flip on the second wire.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The two error-propagation facts (stabilizer formalism) -/

/-- **An `X` error on the control of `CNOT` propagates to the target** (the "clear" direction):
`C·X₁·C = X₁·X₂` (N&C eq. 4.32). Flipping the control before the `CNOT` also flips the value copied
onto the target, so conjugating an `X` on the control by `CNOT` leaves an `X` on *both* qubits.
This is `cnotGate_conj_pauliXGate_onLeft` of Exercise 4.31, restated in the
error-propagation framing of Exercise 10.64. -/
theorem cnotGate_pauliXGate_control_propagates :
    cnotGate.comp ((pauliXGate.onLeft qubit).comp cnotGate)
      = (pauliXGate.onLeft qubit).comp (pauliXGate.onRight qubit) :=
  cnotGate_conj_pauliXGate_onLeft

/-- **A `Z` error on the target of `CNOT` propagates *back* to the control** (the surprising
direction), **via the stabilizer formalism**: `C·Z₂·C = Z₁·Z₂` (N&C eq. 4.37). A `Z` on the target
multiplies `|t⟩` by `(-1)ᵗ`; after `CNOT` sends `t ↦ t ⊕ c`, that phase reads `(-1)^{t ⊕ c}`, i.e. a
`Z` on *both* qubits. This is `cnotGate_conj_pauliZGate_onRight` of Exercise 4.31, restated
in the error-propagation framing of Exercise 10.64. -/
theorem cnotGate_pauliZGate_target_backPropagates :
    cnotGate.comp ((pauliZGate.onRight qubit).comp cnotGate)
      = (pauliZGate.onLeft qubit).comp (pauliZGate.onRight qubit) :=
  cnotGate_conj_pauliZGate_onRight

/-! ### The circuit-identity view (Exercise 4.20) -/

/-- **The Exercise 4.20 circuit identity, as a gate equality:** `(H ⊗ H) · CNOT · (H ⊗ H) =
reversedCNOT`. Conjugating `CNOT` (control on the first qubit) by a Hadamard on each qubit yields
the *reversed* `CNOT` (control on the second qubit, target on the first) — control and target have
interchanged roles. Lifted to a gate equality from the two computational-basis truth tables
`cnotGate_hadamardConj_evolvePure_qubitBasis` and `reversedCnotGate_evolvePure_qubitBasis`, which
both send `|c⟩ ⊗ |t⟩ ↦ |c ⊕ t⟩ ⊗ |t⟩`, via `twoQubit_evolution_ext`. -/
theorem hadamardConj_cnotGate_eq_reversedCnotGate :
    (hadamardGate ⊗ hadamardGate).comp (cnotGate.comp (hadamardGate ⊗ hadamardGate))
      = reversedCnotGate := by
  apply twoQubit_evolution_ext
  intro c t
  rw [cnotGate_hadamardConj_evolvePure_qubitBasis, reversedCnotGate_evolvePure_qubitBasis]

/-- **The reversed `CNOT` propagates an `X` on *its* control (the second qubit) to *its* target (the
first qubit):** `R·X₂·R = X₁·X₂`, the mirror of eq. 4.32 for `reversedCNOT`. Together with the
circuit identity `hadamardConj_cnotGate_eq_reversedCnotGate` and `Z = H·X·H`, this is the
"directly using quantum circuit identities" derivation of the `Z` back-propagation: a target `Z`
becomes a target `X` in the `X`-eigenbasis, where `CNOT` acts as `reversedCNOT` and the `X`
propagates onto the (first-qubit) control. Verified on the computational basis via
`twoQubit_evolution_ext`: both sides send `|q₁⟩ ⊗ |q₂⟩` to `|q₁ ⊕ 1⟩ ⊗ |q₂ ⊕ 1⟩`, using the
reversed-`CNOT` truth table `|a, b⟩ ↦ |a ⊕ b, b⟩` twice around a bit flip on the second wire. -/
theorem reversedCnotGate_pauliXGate_control_propagates :
    reversedCnotGate.comp ((pauliXGate.onRight qubit).comp reversedCnotGate)
      = (pauliXGate.onLeft qubit).comp (pauliXGate.onRight qubit) := by
  apply twoQubit_evolution_ext
  intro q1 q2
  rw [Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    reversedCnotGate_evolvePure_qubitBasis, Evolution.onRight_evolvePure,
    pauliXGate_evolvePure_qubitBasis, reversedCnotGate_evolvePure_qubitBasis,
    Evolution.evolvePure_comp, Evolution.onRight_evolvePure, pauliXGate_evolvePure_qubitBasis,
    Evolution.onLeft_evolvePure, pauliXGate_evolvePure_qubitBasis]
  fin_cases q1 <;> fin_cases q2 <;> rfl

/-! ### Assembling the circuit-identity derivation of the `Z` back-propagation

We now carry the argument of the previous section all the way through to a *second proof* of the
`Z` back-propagation `C·Z₂·C = Z₁·Z₂` — the one N&C asks for "directly using quantum circuit
identities", independent of the stabilizer/commutation calculation behind
`cnotGate_pauliZGate_target_backPropagates`. The engine is conjugation by `H ⊗ H`: it turns `CNOT`
into `reversedCNOT` (`hadamardConj_cnotGate_eq_reversedCnotGate`) and each Pauli into its
`H`-conjugate (`H·X·H = Z`, `H·Z·H = X`), so applying it to the reversed-gate propagation
`R·X₂·R = X₁·X₂` reproduces `C·Z₂·C = Z₁·Z₂`. -/

/-- **`H ⊗ H` is an involution:** `(H ⊗ H) · (H ⊗ H) = 1`, from `H² = 1` factorwise. -/
theorem hadamardTmul_comp_self :
    (hadamardGate ⊗ hadamardGate).comp (hadamardGate ⊗ hadamardGate) = Evolution.id := by
  rw [Evolution.tmul_comp, hadamardGate_comp_self, Evolution.id_tmul_id]

/-- **Conjugation by `H ⊗ H` distributes over composition:**
`(H⊗H)·(A·B)·(H⊗H) = ((H⊗H)·A·(H⊗H)) · ((H⊗H)·B·(H⊗H))`. The `H⊗H` involution
(`hadamardTmul_comp_self`) cancels in the middle, so conjugation by `H ⊗ H` is a monoid
homomorphism. -/
theorem hadamardTmul_conj_comp (A B : Evolution (qubit ⊗ qubit)) :
    (hadamardGate ⊗ hadamardGate).comp ((A.comp B).comp (hadamardGate ⊗ hadamardGate))
      = ((hadamardGate ⊗ hadamardGate).comp (A.comp (hadamardGate ⊗ hadamardGate))).comp
          ((hadamardGate ⊗ hadamardGate).comp (B.comp (hadamardGate ⊗ hadamardGate))) := by
  simp only [← Evolution.comp_assoc]
  rw [Evolution.comp_assoc ((hadamardGate ⊗ hadamardGate).comp A) (hadamardGate ⊗ hadamardGate)
        (hadamardGate ⊗ hadamardGate), hadamardTmul_comp_self, Evolution.comp_id]

/-- **`H ⊗ H` conjugates an `X` on the right factor to a `Z`:** `(H⊗H)·X₂·(H⊗H) = Z₂`, from
`H·X·H = Z` factorwise (`H·1·H = 1` on the left). -/
theorem hadamardTmul_conj_pauliXGate_onRight :
    (hadamardGate ⊗ hadamardGate).comp
        ((pauliXGate.onRight qubit).comp (hadamardGate ⊗ hadamardGate))
      = pauliZGate.onRight qubit := by
  simp only [Evolution.onRight]
  rw [Evolution.tmul_comp, Evolution.tmul_comp, Evolution.id_comp, hadamardGate_comp_self,
    hadamardGate_comp_pauliXGate_comp_hadamardGate]

/-- **`H ⊗ H` conjugates an `X` on the left factor to a `Z`:** `(H⊗H)·X₁·(H⊗H) = Z₁`, from
`H·X·H = Z` factorwise (`H·1·H = 1` on the right). -/
theorem hadamardTmul_conj_pauliXGate_onLeft :
    (hadamardGate ⊗ hadamardGate).comp
        ((pauliXGate.onLeft qubit).comp (hadamardGate ⊗ hadamardGate))
      = pauliZGate.onLeft qubit := by
  simp only [Evolution.onLeft]
  rw [Evolution.tmul_comp, Evolution.tmul_comp, Evolution.id_comp, hadamardGate_comp_self,
    hadamardGate_comp_pauliXGate_comp_hadamardGate]

/-- **`H ⊗ H` conjugates `reversedCNOT` back to `CNOT`:** `(H⊗H)·reversedCNOT·(H⊗H) = CNOT`, the
inverse reading of the Exercise 4.20 circuit identity `hadamardConj_cnotGate_eq_reversedCnotGate`
(using that `H ⊗ H` is an involution). -/
theorem hadamardConj_reversedCnotGate_eq_cnotGate :
    (hadamardGate ⊗ hadamardGate).comp (reversedCnotGate.comp (hadamardGate ⊗ hadamardGate))
      = cnotGate := by
  rw [← hadamardConj_cnotGate_eq_reversedCnotGate, Evolution.comp_assoc,
    ← Evolution.comp_assoc (hadamardGate ⊗ hadamardGate) (hadamardGate ⊗ hadamardGate),
    hadamardTmul_comp_self, Evolution.id_comp, Evolution.comp_assoc, hadamardTmul_comp_self,
    Evolution.comp_id]

/-- **A `Z` error on the target of `CNOT` propagates back to the control, *derived directly from
quantum circuit identities* (N&C Exercise 10.64, second method):** `C·Z₂·C = Z₁·Z₂`. Independent of
the stabilizer calculation `cnotGate_pauliZGate_target_backPropagates`: conjugating the
reversed-gate propagation `reversedCnotGate_pauliXGate_control_propagates` (`R·X₂·R = X₁·X₂`) by
`H ⊗ H` turns `R` back into `CNOT` (`hadamardConj_reversedCnotGate_eq_cnotGate`), the middle `X₂`
into `Z₂` and the output `X₁·X₂` into `Z₁·Z₂` (`hadamardTmul_conj_pauliXGate_on{Right,Left}`), the
conjugation distributing over the products via `hadamardTmul_conj_comp`. Thus the very same `H ⊗ H`
role reversal of Exercise 4.20 that sends "X on the control forwards to the target" to "X on the
reversed control forwards to the reversed target" sends it, in the computational basis, to "Z on the
target backwards to the control". -/
theorem cnotGate_pauliZGate_target_backPropagates_via_circuit :
    cnotGate.comp ((pauliZGate.onRight qubit).comp cnotGate)
      = (pauliZGate.onLeft qubit).comp (pauliZGate.onRight qubit) := by
  have key := congrArg
    (fun A => (hadamardGate ⊗ hadamardGate).comp (A.comp (hadamardGate ⊗ hadamardGate)))
    reversedCnotGate_pauliXGate_control_propagates
  simp only [hadamardTmul_conj_comp, hadamardConj_reversedCnotGate_eq_cnotGate,
    hadamardTmul_conj_pauliXGate_onRight, hadamardTmul_conj_pauliXGate_onLeft] at key
  exact key

end AxQM
