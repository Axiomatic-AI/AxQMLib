/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ToffoliHadamard
import AxQM.Postulates.API.ToffoliFigure49
import AxQM.Postulates.API.GateCommute

/-!
# Nielsen & Chuang, Exercise 4.24 (Figure 4.9 implements the Toffoli gate)

*(N&C p. 182.)*

Verify Figure 4.9 implements the Toffoli gate from H,S,CNOT,T gates.

Figure 4.9 is Nielsen & Chuang's circuit for the Toffoli gate `C²(X)` built from *just* the
Hadamard, phase (`S`), controlled-`NOT` and `π/8` (`T`) gates. On three qubits `q₁ ⊗ (q₂ ⊗ q₃)`
(controls `q₁, q₂`, target `q₃`) the circuit is, reading left to right (so the leftmost gate acts
first),

`H₃ · [target block] · H₃ · [control block]`,

with a `Hadamard` `H₃` bracketing a block of `CNOT`/`T`/`T†` gates on the target wire, followed by a
block of `CNOT`/`T`/`T†`/`S` gates on the two control wires. This file assembles that full circuit
and verifies it equals the Toffoli gate.

## The formalisation

Every gate is a closed-system evolution (`Evolution`) and the exercise is a *circuit identity*
between them, so the faithful statement is an equality of `Evolution`s, built from `hadamardGate`,
`phaseShiftGate`, `cnotGate`, `controlledUnitary`, `pauliXGate`,
`Evolution.onLeft`/`onRight`/`comp` and the gate-monoid composition.

* `figure49TargetBlock` — the eight `CNOT`/`T`/`T†` gates of Figure 4.9 that lie **between** the two
  target-wire `Hadamard`s (the block `Q` conjugated by `H₃`).
* `figure49ControlBlock` — the six `CNOT`/`T†`/`T`/`S` gates of Figure 4.9 that come **after** the
  second `Hadamard`, all on the two control wires (the block `P`).
* `toffoliFig49Circuit` — **the full Figure 4.9 circuit**, `P · H₃ · Q · H₃`.
* `toffoliFig49Circuit_eq_toffoliGate` — **the exercise:** `toffoliFig49Circuit = toffoliGate`.

## Proof strategy

The two hard steps are done in `AxQM/Postulates/API/`, so this file only assembles them:

* `figure49HadamardFree_eq_ccontrolledZ` (`ToffoliFigure49.lean`): deleting the two `Hadamard`s
  leaves a **monomial** circuit equal to the doubly-controlled `Z`, `P · Q = C²(Z)` — the
  superposition-free crux, checked on the eight basis states.
* `toffoliGate_eq_hadamardConj_ccontrolledZ` (`ToffoliHadamard.lean`):
  `toffoliGate = H₃ · C²(Z) · H₃`, since `X = H Z H`.

Combining them, `toffoliGate = H₃ · (P · Q) · H₃`, whereas the drawn circuit is `P · H₃ · Q · H₃`.
The two agree because the control block `P` acts only on the control wires `q₁, q₂` while `H₃` acts
only on the target `q₃`, so `P` and `H₃` **commute** (`P · H₃ = H₃ · P`) — the physical fact that
gates on disjoint wires can be reordered. Sliding `H₃` to the front turns `P · H₃ · Q · H₃` into
`H₃ · P · Q · H₃ = H₃ · (P · Q) · H₃ = toffoliGate`.

The commutation `P · H₃ = H₃ · P` is built up from the single-gate commutations of the six control
gates with `H₃`, each an instance of the disjoint-factor lemmas
`Evolution.onLeft_comm_onRight` / `controlledUnitary_comm_onRight` (`GateCommute.lean`), assembled
via the `Evolution` monoid's `Commute` API.

## Fidelity to Figure 4.9

The gate sequence and wiring are transcribed exactly as in `figure49HadamardFree`
(`ToffoliFigure49.lean`), which was verified basis-state-by-basis-state to be `C²(Z)`; here it is
split at the two-blocks boundary into `figure49ControlBlock · figure49TargetBlock`
(`figure49HadamardFree_eq_control_comp_target`, an associativity rearrangement), and the two
`Hadamard`s are reinstated in their drawn positions. `T = phaseShiftGate (π/4)`,
`T† = phaseShiftGate (-π/4)`, `S = phaseShiftGate (π/2)`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **The target-wire block of Figure 4.9** (`Q`): the eight gates between the two `Hadamard`s on
the target `q₃`, reading Figure 4.9 left to right (earliest gate innermost) —
`CNOT₂₃, T†₃, CNOT₁₃, T₃, CNOT₂₃, T†₃, CNOT₁₃, T₃`. These are exactly the target-wire gates of
`figure49HadamardFree`. -/
def figure49TargetBlock : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (((phaseShiftGate (Real.pi / 4)).onRight qubit).onRight qubit).comp
  ((controlledUnitary (pauliXGate.onRight qubit)).comp
  ((((phaseShiftGate (-(Real.pi / 4))).onRight qubit).onRight qubit).comp
  ((cnotGate.onRight qubit).comp
  ((((phaseShiftGate (Real.pi / 4)).onRight qubit).onRight qubit).comp
  ((controlledUnitary (pauliXGate.onRight qubit)).comp
  ((((phaseShiftGate (-(Real.pi / 4))).onRight qubit).onRight qubit).comp
  (cnotGate.onRight qubit)))))))

/-- **The control-wire block of Figure 4.9** (`P`): the six gates after the second `Hadamard`, all
on the control wires `q₁, q₂`, reading Figure 4.9 left to right (earliest gate innermost) —
`T†₂, CNOT₁₂, T†₂, CNOT₁₂, T₁, S₂`. These are exactly the control-wire gates of
`figure49HadamardFree`. -/
def figure49ControlBlock : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (((phaseShiftGate (Real.pi / 2)).onLeft qubit).onRight qubit).comp
  ((((phaseShiftGate (Real.pi / 4)).onLeft (qubit ⊗ qubit))).comp
  ((controlledUnitary (pauliXGate.onLeft qubit)).comp
  ((((phaseShiftGate (-(Real.pi / 4))).onLeft qubit).onRight qubit).comp
  ((controlledUnitary (pauliXGate.onLeft qubit)).comp
  (((phaseShiftGate (-(Real.pi / 4))).onLeft qubit).onRight qubit)))))

/-- **The full Figure 4.9 circuit** implementing the Toffoli gate (Nielsen & Chuang §4.3), on the
three-qubit system `qubit ⊗ (qubit ⊗ qubit)` (`q₁ ⊗ (q₂ ⊗ q₃)`). It is `P · H₃ · Q · H₃`: the target
block `figure49TargetBlock` (`Q`) is conjugated by the target `Hadamard`
`H₃ = (hadamardGate.onRight qubit).onRight qubit`, then the control block `figure49ControlBlock`
(`P`) is applied. Reading right to left (the innermost `comp` acts first): initial `H₃`, target
block, second `H₃`, control block. -/
def toffoliFig49Circuit : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  figure49ControlBlock.comp
    (((hadamardGate.onRight qubit).onRight qubit).comp
      (figure49TargetBlock.comp ((hadamardGate.onRight qubit).onRight qubit)))

/-- **The Hadamard-free block splits as control-block ∘ target-block.** `figure49HadamardFree`
(defined as a single 14-gate composite in `ToffoliFigure49.lean`) equals
`figure49ControlBlock · figure49TargetBlock`; this is a pure reassociation of the same gate sequence
at the boundary between the control (`P`) and target (`Q`) blocks. -/
theorem figure49HadamardFree_eq_control_comp_target :
    figure49HadamardFree = figure49ControlBlock.comp figure49TargetBlock := by
  simp only [figure49HadamardFree, figure49ControlBlock, figure49TargetBlock, Evolution.comp_assoc]

/-- **Nielsen & Chuang, Exercise 4.24: Figure 4.9 implements the Toffoli gate.** The full Figure 4.9
circuit equals the Toffoli gate `C²(X)`: `toffoliFig49Circuit = toffoliGate`.

Proof: `toffoliGate = H₃ · C²(Z) · H₃` (`toffoliGate_eq_hadamardConj_ccontrolledZ`) and
`C²(Z) = P · Q` (`figure49HadamardFree_eq_ccontrolledZ` composed with the block split), so
`toffoliGate = H₃ · P · Q · H₃`. The drawn circuit is `P · H₃ · Q · H₃`, and the control block `P`
commutes with `H₃` (it acts only on the control wires), so sliding `H₃` to the front gives the two
circuits are equal. The commutation `P · H₃ = H₃ · P` is assembled from the six single-gate
commutations, each an instance of `Evolution.onLeft_comm_onRight` /
`controlledUnitary_comm_onRight`. -/
theorem toffoliFig49Circuit_eq_toffoliGate : toffoliFig49Circuit = toffoliGate := by
  -- The six control-block gates each commute with the target Hadamard `H₃` (disjoint wires),
  -- each reduced to `Evolution.onLeft_comm_onRight` / `controlledUnitary_comm_onRight`.
  have cS₂ : Commute ((hadamardGate.onRight qubit).onRight qubit)
      (((phaseShiftGate (Real.pi / 2)).onLeft qubit).onRight qubit) := by
    change _ * _ = _ * _
    rw [Evolution.mul_def, Evolution.mul_def, Evolution.onRight_comp, Evolution.onRight_comp,
      Evolution.onLeft_comm_onRight]
  have cT₁ : Commute ((hadamardGate.onRight qubit).onRight qubit)
      ((phaseShiftGate (Real.pi / 4)).onLeft (qubit ⊗ qubit)) := by
    change _ * _ = _ * _
    rw [Evolution.mul_def, Evolution.mul_def,
      ← Evolution.onLeft_comm_onRight (phaseShiftGate (Real.pi / 4)) (hadamardGate.onRight qubit)]
  have cCX : Commute ((hadamardGate.onRight qubit).onRight qubit)
      (controlledUnitary (pauliXGate.onLeft qubit)) := by
    change _ * _ = _ * _
    rw [Evolution.mul_def, Evolution.mul_def,
      ← controlledUnitary_comm_onRight (pauliXGate.onLeft qubit) (hadamardGate.onRight qubit)
        (Evolution.onLeft_comm_onRight pauliXGate hadamardGate)]
  have cTd : Commute ((hadamardGate.onRight qubit).onRight qubit)
      (((phaseShiftGate (-(Real.pi / 4))).onLeft qubit).onRight qubit) := by
    change _ * _ = _ * _
    rw [Evolution.mul_def, Evolution.mul_def, Evolution.onRight_comp, Evolution.onRight_comp,
      Evolution.onLeft_comm_onRight]
  -- Hence `H₃` commutes with the whole control block `P`.
  have hcomm : figure49ControlBlock.comp ((hadamardGate.onRight qubit).onRight qubit)
      = ((hadamardGate.onRight qubit).onRight qubit).comp figure49ControlBlock := by
    have hC : Commute ((hadamardGate.onRight qubit).onRight qubit) figure49ControlBlock := by
      rw [figure49ControlBlock]
      exact cS₂.mul_right (cT₁.mul_right (cCX.mul_right (cTd.mul_right (cCX.mul_right cTd))))
    exact hC.eq.symm
  -- Assemble: rewrite `toffoliGate = H₃ · (P · Q) · H₃`, then slide `H₃` past `P`.
  rw [toffoliGate_eq_hadamardConj_ccontrolledZ, ← figure49HadamardFree_eq_ccontrolledZ,
    figure49HadamardFree_eq_control_comp_target, toffoliFig49Circuit, Evolution.comp_assoc,
    ← Evolution.comp_assoc figure49ControlBlock ((hadamardGate.onRight qubit).onRight qubit)
      (figure49TargetBlock.comp ((hadamardGate.onRight qubit).onRight qubit)),
    hcomm, Evolution.comp_assoc]

end AxQM
