/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RelativePhaseToffoli
import AxQM.Postulates.API.ControlledUnitaryDecomposition
import AxQM.Postulates.API.ControlledZ

/-!
# Nielsen & Chuang, Exercise 7.32 (the ion-trap `CNOT` circuit of Figure 7.14)

Show the ion-trap circuit of Fig 7.14 is equivalent (up to phases) to a controlled-NOT with phonon
as control.

(N&C p. 324, §7.6.3, "Experiment".) In the trapped-ion controlled-`NOT` experiment, the top wire of
Figure 7.14 is the **phonon** (motional) qubit and the bottom wire the ion's internal **hyperfine**
qubit. N&C realises the gate with three laser pulses (p. 322): an `R_y(π/2)` rotation on the
internal-state qubit, then a controlled-`Z` between the two qubits, then an `R_y(-π/2)` rotation on
the internal-state qubit. Reading right to left as a matrix product, the circuit is therefore

`U = R_y(-π/2)₂ · CZ · R_y(π/2)₂`,

where the subscript `₂` marks the rotations acting on the second (internal-state) qubit and `CZ` is
the (symmetric) controlled-`Z`. The exercise is to show `U` is a controlled-`NOT` with the
*phonon* (first qubit) as control, up to relative phases.

The rotation gates `R_y(±π/2)`, the controlled-`Z`, and the target `CNOT` are all closed-system
evolutions (Postulate 2 / `Evolution`); the exercise is a *circuit identity* between these gate
objects, exactly as for Exercises 4.17 and 7.23. The faithful statement is an equality of
`Evolution`s, built from gates and gate composition (`Evolution.comp`,
`Evolution.onLeft`/`onRight`, `controlledUnitary`).

## The formalisation

* `ionTrapCnotCircuit` — **the circuit of Figure 7.14** as an `Evolution` on `qubit ⊗ qubit`,
  `R_y(-π/2)₂ · CZ · R_y(π/2)₂`, with the two rotations placed on the right (internal-state) qubit
  via `Evolution.onRight` and `CZ = controlledZGate`.
* `ionTrapCnotCircuit_eq_controlledUnitary_pauliZ_pauliX_pauliZ` — the circuit is the **controlled**
  single-qubit gate `C(Z·X·Z)` with the phonon (left) qubit as control:
  `ionTrapCnotCircuit = controlledUnitary (Z · X · Z)`. Since `Z·X·Z = -X` (a Pauli-`X` up to the
  global phase `-1`), this exhibits the circuit as a controlled-`NOT` on the internal-state qubit
  *conditioned on the phonon*, with the `|1⟩`-control branch carrying the relative phase `-1`.
* `ionTrapCnotCircuit_eq_pauliZ_control_comp_cnot` — **Exercise 7.32:**
  `ionTrapCnotCircuit = (Z ⊗ 1) · CNOT`, an exact equality of two-qubit gates in which `CNOT` has
  the phonon (first) qubit as control and the prefactor `Z ⊗ 1 = diag(1, 1, -1, -1)` is a *relative
  phase* (a diagonal, unit-modulus, basis-state-dependent phase, not a global one). On each
  computational-basis input this gives `(Z ⊗ 1) · CNOT |q₁, q₂⟩ = (-1)^{q₁} |q₁, q₂ ⊕ q₁⟩` — the
  controlled-`NOT` truth table (phonon `q₁` controlling the flip of the ion qubit `q₂`) up to the
  relative phase `(-1)^{q₁}`. This is the sense in which Figure 7.14 realises a `CNOT` with the
  phonon as control.

## Design notes

* **Why this shape.** The result is an exact gate equality holding on
  every input, not an "up to global phase" or "on basis states only" surrogate. The deviation from a
  bare `CNOT` is exhibited *explicitly* as the diagonal relative-phase gate `Z ⊗ 1`, which is what
  "up to relative phases" means and is stronger than merely asserting existence of some phase. The
  two forms are complementary: `C(Z·X·Z)` displays the controlled-single-qubit structure (control =
  phonon), and `(Z ⊗ 1) · CNOT` displays the deviation from `CNOT` as a manifest relative phase.
* **Proof.** Two moves. (1) The rotations conjugate the controlled-`Z`'s *target*: by the general
  target-conjugation identity `controlledUnitary_onRight_conj` (with `R_y(-π/2) · R_y(π/2) = 1`,
  from `rotYGate_comp`), `ionTrapCnotCircuit = C(R_y(-π/2) · Z · R_y(π/2))`, and the inner
  single-qubit product collapses to `Z · X · Z`: both `R_y(-π/2) · Z · R_y(π/2)` and `Z · X · Z`
  reduce to `R_y(-2π) · X` by the Pauli–rotation algebra (`rotYGate_neg_pi_comp_pauliXGate`
  `R_y(-π)·X = Z`, `pauliXGate_comp_rotYGate` `X·R_y(θ) = R_y(-θ)·X`, `rotYGate_comp`), so no matrix
  arithmetic and no `cos`/`sin` values are ever touched. (2) `C(Z·X·Z) = (Z ⊗ 1) · CNOT` is checked
  on the four computational-basis states (`twoQubit_evolution_ext`); the `-1` from `Z·X·Z = -X` on
  the control-`|1⟩` branch matches the `-1` that `Z ⊗ 1` places on the phonon-`|1⟩` states, read off
  from `Z|i⟩ = (-1)^i|i⟩` (`pauliZGate_op_apply_qubitBasis`) and `X|i⟩ = |i ⊕ 1⟩`
  (`pauliXGate_op_apply_qubitBasis`).
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **The ion-trap controlled-`NOT` circuit of Nielsen & Chuang, Figure 7.14** as an `Evolution` on
`qubit ⊗ qubit` (phonon ⊗ internal-state). Following N&C's three-pulse realisation (p. 322), reading
right to left: an `R_y(π/2)` rotation on the internal-state (second) qubit, then a controlled-`Z`
between the two qubits, then an `R_y(-π/2)` rotation on the internal-state qubit —
`R_y(-π/2)₂ · CZ · R_y(π/2)₂`. The rotations act on the right (internal-state) qubit via
`Evolution.onRight`; `CZ = controlledZGate`. -/
def ionTrapCnotCircuit : Evolution (qubit ⊗ qubit) :=
  ((rotYGate (-(Real.pi / 2))).onRight qubit).comp
    (controlledZGate.comp ((rotYGate (Real.pi / 2)).onRight qubit))

/-- **The circuit is a controlled single-qubit gate with the phonon as control.**
`ionTrapCnotCircuit = C(Z · X · Z)`: the controlled-`U` gate (control = phonon, the left qubit)
whose target gate is `Z · X · Z`. Since `Z · X · Z = -X` (Pauli-`X` up to the global phase `-1`),
this is a controlled-`NOT` on the internal-state qubit conditioned on the phonon, with the
control-`|1⟩` branch carrying the relative phase `-1`.

The `R_y(±π/2)` rotations sit on the controlled-`Z`'s target, so by the general target-conjugation
identity `controlledUnitary_onRight_conj` (valid since `R_y(-π/2) · R_y(π/2) = 1`) the circuit
equals `C(R_y(-π/2) · Z · R_y(π/2))`; that inner product equals `Z · X · Z` because both it and
`Z · X · Z` reduce to `R_y(-2π) · X` via the Pauli–rotation algebra. -/
theorem ionTrapCnotCircuit_eq_controlledUnitary_pauliZ_pauliX_pauliZ :
    ionTrapCnotCircuit = controlledUnitary (pauliZGate.comp (pauliXGate.comp pauliZGate)) := by
  -- `R_y(-π/2) · R_y(π/2) = 1`, the hypothesis of the target-conjugation identity.
  have hinv : (rotYGate (-(Real.pi / 2))).comp (rotYGate (Real.pi / 2)) = Evolution.id := by
    rw [rotYGate_comp, show -(Real.pi / 2) + Real.pi / 2 = 0 by ring, rotYGate_zero]
  -- `R_y(-π/2) · Z · R_y(π/2) = R_y(-2π) · X`: bubble the `X` (hidden in `Z = R_y(-π)·X`) right.
  have hL : (rotYGate (-(Real.pi / 2))).comp (pauliZGate.comp (rotYGate (Real.pi / 2)))
      = (rotYGate (-(2 * Real.pi))).comp pauliXGate := by
    rw [← rotYGate_neg_pi_comp_pauliXGate, Evolution.comp_assoc, pauliXGate_comp_rotYGate,
      ← Evolution.comp_assoc, rotYGate_comp, ← Evolution.comp_assoc, rotYGate_comp,
      show -(Real.pi / 2) + -Real.pi + -(Real.pi / 2) = -(2 * Real.pi) by ring]
  -- `Z · X · Z = R_y(-2π) · X`: the same normal form, via `Z = R_y(-π)·X`.
  have hR : pauliZGate.comp (pauliXGate.comp pauliZGate)
      = (rotYGate (-(2 * Real.pi))).comp pauliXGate := by
    rw [← rotYGate_neg_pi_comp_pauliXGate, pauliXGate_comp_rotYGate_comp,
      pauliXGate_comp_pauliXGate, Evolution.comp_id, Evolution.comp_assoc, pauliXGate_comp_rotYGate,
      ← Evolution.comp_assoc, rotYGate_comp,
      show -Real.pi + -(- -Real.pi) = -(2 * Real.pi) by ring]
  unfold ionTrapCnotCircuit controlledZGate
  rw [controlledUnitary_onRight_conj pauliZGate (rotYGate (-(Real.pi / 2)))
      (rotYGate (Real.pi / 2)) hinv, hL.trans hR.symm]

/-- **Nielsen & Chuang, Exercise 7.32.** The Figure 7.14 circuit is a controlled-`NOT` with the
**phonon** (first qubit) as control, up to relative phases:
`ionTrapCnotCircuit = (Z ⊗ 1) · CNOT`,
an exact equality of two-qubit gates. Here `CNOT = cnotGate` has the phonon (first) qubit as
control and the internal-state (second) qubit as target, and the prefactor
`Z ⊗ 1 = pauliZGate.onLeft qubit = diag(1, 1, -1, -1)` is a *relative* phase — diagonal, of unit
modulus, depending on the (phonon) basis state, not a single global scalar. On a computational-basis
input this reads `(Z ⊗ 1)·CNOT |q₁, q₂⟩ = (-1)^{q₁} |q₁, q₂ ⊕ q₁⟩`: the `CNOT` truth table (phonon
`q₁` controls the flip of the ion qubit `q₂`) up to the relative phase `(-1)^{q₁}`.

Proved from `ionTrapCnotCircuit_eq_controlledUnitary_pauliZ_pauliX_pauliZ` by checking both gates on
the four computational-basis states (`twoQubit_evolution_ext`): the `-1` carried by `Z·X·Z = -X` on
the control-`|1⟩` branch is exactly the `-1` that `Z ⊗ 1` puts on the phonon-`|1⟩` states. -/
theorem ionTrapCnotCircuit_eq_pauliZ_control_comp_cnot :
    ionTrapCnotCircuit = (pauliZGate.onLeft qubit).comp cnotGate := by
  rw [ionTrapCnotCircuit_eq_controlledUnitary_pauliZ_pauliX_pauliZ]
  -- `Z·X·Z` acts as `-X` on the computational basis: `(Z·X·Z)|t⟩ = -|t ⊕ 1⟩`.
  have hZXZ : ∀ t : Fin 2, (pauliZGate.comp (pauliXGate.comp pauliZGate)).op (qubitBasis t).vec
      = -(qubitBasis (t + 1)).vec := by
    intro t
    simp only [Evolution.comp_op, ContinuousLinearMap.comp_apply, pauliZGate_op_apply_qubitBasis,
      map_smul, pauliXGate_op_apply_qubitBasis]
    fin_cases t <;>
      simp only [pow_zero, pow_one, Fin.zero_eta, Fin.mk_one, Fin.isValue, zero_add, Fin.reduceAdd,
        Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.zero_mod, qubitBasis_vec, neg_smul, one_smul] <;>
      first
        | exact neg_one_smul ℂ _
        | exact congrArg Neg.neg (one_smul ℂ _)
  apply twoQubit_evolution_ext
  intro q1 q2
  apply PureState.ext
  rw [Evolution.evolvePure_comp]
  -- On `|0⟩` control both gates fix `|0, q₂⟩`; on `|1⟩` control the ion qubit flips and the `-1` of
  -- `Z·X·Z = -X` matches the `-1` that `Z ⊗ 1` puts on the phonon-`|1⟩` states.
  fin_cases q1 <;> fin_cases q2 <;>
    simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue, controlledUnitary_evolvePure_ketZero,
      controlledUnitary_evolvePure_ketOne, cnotGate_evolvePure_qubitBasis,
      Evolution.onLeft_evolvePure, PureState.tmul_vec, Evolution.evolvePure_vec, hZXZ,
      pauliZGate_op_apply_qubitBasis] <;>
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, Fin.reduceAdd, one_smul,
      neg_one_smul, TensorProduct.tmul_neg, TensorProduct.neg_tmul] <;>
      rfl

end AxQM
