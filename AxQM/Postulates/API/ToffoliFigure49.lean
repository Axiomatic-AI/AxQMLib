/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.ControlledUnitaryDecomposition
import AxQM.Postulates.API.Teleportation

/-!
# AxQM.Postulates.API — the Hadamard-free block of Figure 4.9 is `C²(Z)`

This file supplies the **superposition-free crux** of Nielsen & Chuang, Exercise 4.24 ("verify that
Figure 4.9 implements the Toffoli gate"). Figure 4.9's circuit is `P · H₃ · Q · H₃`, where `H₃` is a
Hadamard on the target qubit and `P`, `Q` are the two `Hadamard`-free blocks of phase (`T`, `T†`,
`S`) and `CNOT` gates. Combined with the reduction `toffoliGate = H₃ · C²(Z) · H₃`
(`toffoliGate_eq_hadamardConj_ccontrolledZ`, the file `ToffoliHadamard.lean`), verifying Figure 4.9
reduces to the identity proved here:

`figure49HadamardFree = ccontrolledUnitary pauliZGate = C²(Z)`,

where `figure49HadamardFree = P · Q` is the entire circuit with the two `Hadamard`s deleted. Because
every remaining gate is diagonal in the computational basis (`T`, `T†`, `S`, `Z`) or a permutation
(`CNOT`), both sides are **monomial** — they send each computational-basis state to a scalar
multiple of itself — so the identity is verified basis state by basis state (eight cases) with no
superposition bookkeeping. The phase kickback of the `T`/`T†`/`S` gates through the `CNOT` network
produces the phase `(-1)^{q₁q₂q₃}` of `C²(Z)`: `+1` on the seven states with `q₁q₂q₃ = 0` and `-1`
on `|111⟩`.

## Main results

* `figure49HadamardFree` — the `Hadamard`-free block of Figure 4.9 (the 14 phase/`CNOT` gates), as a
  single `Evolution` of `qubit ⊗ (qubit ⊗ qubit)`.
* `figure49HadamardFree_eq_ccontrolledZ` — `figure49HadamardFree = ccontrolledUnitary pauliZGate`,
  the monomial identity behind Figure 4.9.

Supporting reusable **computational-basis action** lemmas at the operator level (`Evolution.op`
applied to a basis tensor `|q₁⟩ ⊗ |q₂⟩ ⊗ |q₃⟩`), one per gate shape used by the circuit:

* `cnot23_op`, `cnot13_op`, `cnot12_op` — the three `CNOT`s (control/target `2→3`, `1→3`, `1→2`),
  each a permutation of the basis (a single target bit XORed with a control bit).
* `phase1_op`, `phase2_op`, `phase3_op` — a phase-shift gate `P(α)` on wire `1`, `2`, `3`, each a
  scalar `[1, e^{iα}]` on the basis depending on that wire's bit.
* `ccontrolledZ_op` — the action of `C²(Z)`: the phase `(-1)^{q₁q₂q₃}` on `|q₁q₂q₃⟩`.

## Fidelity to Figure 4.9

The phase gates are written as `phaseShiftGate`: `T = P(π/4)`, `T† = P(-π/4)`, `S = P(π/2)` — the
diagonal gates `diag(1, e^{iπ/4})`, `diag(1, e^{-iπ/4})`, `diag(1, i)` that Figure 4.9 draws as
`T`, `T†`, `S`. The gate order and wiring are transcribed directly from the figure (read
left-to-right, so the earliest gate is the innermost `comp`): reading the target (bottom) wire,
`H, CNOT₂₃, T†, CNOT₁₃, T, CNOT₂₃, T†, CNOT₁₃, T, H`; the control wires carry `T†, T†, S` (on `q₂`),
`T` (on `q₁`) and the two `CNOT₁₂`s. Deleting the two `H`s (both on `q₃`) leaves
`figure49HadamardFree`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-! ### Computational-basis action of the circuit's gates

Each lemma computes a gate's `Evolution.op` on the computational-basis vector
`|q₁⟩ ⊗ |q₂⟩ ⊗ |q₃⟩ = (qubitBasis a ⊗ (qubitBasis b ⊗ qubitBasis c)).vec`, returned in the same form
(a permuted basis vector, or a scalar times the basis vector). Kept in the `PureState.tmul` `.vec`
form so the lemmas chain along a `comp` of gates without tensor-head bookkeeping. -/

/-- **`CNOT` with control `q₂`, target `q₃`** (`cnotGate.onRight qubit`) flips `q₃` by `q₂`:
`|q₁,q₂,q₃⟩ ↦ |q₁,q₂,q₃ ⊕ q₂⟩`. -/
theorem cnot23_op (a b c : Fin 2) :
    (cnotGate.onRight qubit).op ((qubitBasis a ⊗ (qubitBasis b ⊗ qubitBasis c)).vec)
      = (qubitBasis a ⊗ (qubitBasis b ⊗ qubitBasis (c + b))).vec := by
  rw [← Evolution.evolvePure_vec, Evolution.onRight_evolvePure, cnotGate_evolvePure_qubitBasis]

/-- **`CNOT` with control `q₁`, target `q₃`** (`controlledUnitary (pauliXGate.onRight qubit)`) flips
`q₃` by `q₁`: `|q₁,q₂,q₃⟩ ↦ |q₁,q₂,q₃ ⊕ q₁⟩`. -/
theorem cnot13_op (a b c : Fin 2) :
    (controlledUnitary (pauliXGate.onRight qubit)).op
        ((qubitBasis a ⊗ (qubitBasis b ⊗ qubitBasis c)).vec)
      = (qubitBasis a ⊗ (qubitBasis b ⊗ qubitBasis (c + a))).vec := by
  rw [← Evolution.evolvePure_vec]
  fin_cases a <;>
    simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, controlledUnitary_evolvePure_ketZero,
      controlledUnitary_evolvePure_ketOne, Evolution.onRight_evolvePure,
      pauliXGate_evolvePure_qubitBasis, add_zero]

/-- **`CNOT` with control `q₁`, target `q₂`** (`controlledUnitary (pauliXGate.onLeft qubit)`) flips
`q₂` by `q₁`: `|q₁,q₂,q₃⟩ ↦ |q₁,q₂ ⊕ q₁,q₃⟩`. -/
theorem cnot12_op (a b c : Fin 2) :
    (controlledUnitary (pauliXGate.onLeft qubit)).op
        ((qubitBasis a ⊗ (qubitBasis b ⊗ qubitBasis c)).vec)
      = (qubitBasis a ⊗ (qubitBasis (b + a) ⊗ qubitBasis c)).vec := by
  rw [← Evolution.evolvePure_vec]
  fin_cases a <;>
    simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, controlledUnitary_evolvePure_ketZero,
      controlledUnitary_evolvePure_ketOne, Evolution.onLeft_evolvePure,
      pauliXGate_evolvePure_qubitBasis, add_zero]

/-- **Phase-shift gate on wire `1`** (`(phaseShiftGate α).onLeft (qubit ⊗ qubit)`): multiplies the
basis state by `[1, e^{iα}]_{q₁}` (the identity when `q₁ = 0`, `e^{iα}` when `q₁ = 1`). -/
theorem phase1_op (α : ℝ) (a b c : Fin 2) :
    ((phaseShiftGate α).onLeft (qubit ⊗ qubit)).op
        ((qubitBasis a ⊗ (qubitBasis b ⊗ qubitBasis c)).vec)
      = ![(1 : ℂ), Complex.exp ((α : ℂ) * Complex.I)] a •
          ((qubitBasis a ⊗ (qubitBasis b ⊗ qubitBasis c)).vec) := by
  rw [← Evolution.evolvePure_vec, Evolution.onLeft_evolvePure]
  simp only [PureState.tmul_vec, Evolution.evolvePure_vec, phaseShiftGate_op_apply_qubitBasis]
  exact TensorProduct.smul_tmul' _ _ _

/-- **Phase-shift gate on wire `2`** (`((phaseShiftGate α).onLeft qubit).onRight qubit`): multiplies
the basis state by `[1, e^{iα}]_{q₂}`. -/
theorem phase2_op (α : ℝ) (a b c : Fin 2) :
    (((phaseShiftGate α).onLeft qubit).onRight qubit).op
        ((qubitBasis a ⊗ (qubitBasis b ⊗ qubitBasis c)).vec)
      = ![(1 : ℂ), Complex.exp ((α : ℂ) * Complex.I)] b •
          ((qubitBasis a ⊗ (qubitBasis b ⊗ qubitBasis c)).vec) := by
  rw [← Evolution.evolvePure_vec, Evolution.onRight_evolvePure, Evolution.onLeft_evolvePure]
  simp only [PureState.tmul_vec, Evolution.evolvePure_vec, phaseShiftGate_op_apply_qubitBasis]
  rw [← TensorProduct.smul_tmul']
  exact TensorProduct.tmul_smul _ _ _

/-- **Phase-shift gate on wire `3`** (`((phaseShiftGate α).onRight qubit).onRight qubit`):
multiplies the basis state by `[1, e^{iα}]_{q₃}`. -/
theorem phase3_op (α : ℝ) (a b c : Fin 2) :
    (((phaseShiftGate α).onRight qubit).onRight qubit).op
        ((qubitBasis a ⊗ (qubitBasis b ⊗ qubitBasis c)).vec)
      = ![(1 : ℂ), Complex.exp ((α : ℂ) * Complex.I)] c •
          ((qubitBasis a ⊗ (qubitBasis b ⊗ qubitBasis c)).vec) := by
  rw [← Evolution.evolvePure_vec, Evolution.onRight_evolvePure, Evolution.onRight_evolvePure]
  simp only [PureState.tmul_vec, Evolution.evolvePure_vec, phaseShiftGate_op_apply_qubitBasis,
    TensorProduct.tmul_smul]
  exact TensorProduct.tmul_smul _ _ _

/-- **The doubly-controlled `Z`** `C²(Z)` acts on the computational basis by the phase
`(-1)^{q₁·q₂·q₃}`: `|q₁,q₂,q₃⟩ ↦ (-1)^{q₁q₂q₃} |q₁,q₂,q₃⟩` (the `-1` only on `|111⟩`). -/
theorem ccontrolledZ_op (q1 q2 q3 : Fin 2) :
    (ccontrolledUnitary pauliZGate).op
        ((qubitBasis q1 ⊗ (qubitBasis q2 ⊗ qubitBasis q3)).vec)
      = (-1 : ℂ) ^ ((q1 : ℕ) * (q2 : ℕ) * (q3 : ℕ)) •
          ((qubitBasis q1 ⊗ (qubitBasis q2 ⊗ qubitBasis q3)).vec) := by
  rw [← Evolution.evolvePure_vec]
  fin_cases q1 <;> fin_cases q2 <;> fin_cases q3 <;>
    simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Fin.val_zero, Fin.val_one,
      ccontrolledUnitary_evolvePure_ketZero_left, ccontrolledUnitary_evolvePure_ketOne_left,
      controlledUnitary_evolvePure_ketZero, controlledUnitary_evolvePure_ketOne,
      Evolution.evolvePure_vec, PureState.tmul_vec, pauliZGate_op_apply_qubitBasis,
      Nat.mul_zero, Nat.mul_one, pow_zero, pow_one, one_smul, TensorProduct.tmul_smul]
  all_goals first
    | exact TensorProduct.tmul_smul _ _ _
    | exact (one_smul _ _).symm

/-! ### The Hadamard-free block of Figure 4.9 -/

/-- **The `Hadamard`-free block of Figure 4.9** — the entire Figure-4.9 Toffoli circuit with its two
`Hadamard`s (both on the target `q₃`) deleted. Reading Figure 4.9 left-to-right (so the earliest
gate is the innermost `comp`) and dropping the two `H`s leaves these 14 gates: the target-wire
block `CNOT₂₃, T†₃, CNOT₁₃, T₃, CNOT₂₃, T†₃, CNOT₁₃, T₃` interleaved with the control-wire phases,
followed by `T†₂, CNOT₁₂, T†₂, CNOT₁₂, T₁, S₂`. Here `T = phaseShiftGate (π/4)`,
`T† = phaseShiftGate (-π/4)`, `S = phaseShiftGate (π/2)`, `CNOTᵢⱼ` is the `CNOT` with control `qᵢ`
and target `qⱼ`, and a subscript `k` places the single-qubit gate on wire `qₖ`. -/
def figure49HadamardFree : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (((phaseShiftGate (Real.pi / 2)).onLeft qubit).onRight qubit).comp
  ((((phaseShiftGate (Real.pi / 4)).onLeft (qubit ⊗ qubit))).comp
  ((controlledUnitary (pauliXGate.onLeft qubit)).comp
  ((((phaseShiftGate (-(Real.pi / 4))).onLeft qubit).onRight qubit).comp
  ((controlledUnitary (pauliXGate.onLeft qubit)).comp
  ((((phaseShiftGate (-(Real.pi / 4))).onLeft qubit).onRight qubit).comp
  ((((phaseShiftGate (Real.pi / 4)).onRight qubit).onRight qubit).comp
  ((controlledUnitary (pauliXGate.onRight qubit)).comp
  ((((phaseShiftGate (-(Real.pi / 4))).onRight qubit).onRight qubit).comp
  ((cnotGate.onRight qubit).comp
  ((((phaseShiftGate (Real.pi / 4)).onRight qubit).onRight qubit).comp
  ((controlledUnitary (pauliXGate.onRight qubit)).comp
  ((((phaseShiftGate (-(Real.pi / 4))).onRight qubit).onRight qubit).comp
  (cnotGate.onRight qubit)))))))))))))

/-- **The `Hadamard`-free block of Figure 4.9 is the doubly-controlled `Z`** (the monomial crux of
Nielsen & Chuang, Exercise 4.24): `figure49HadamardFree = ccontrolledUnitary pauliZGate`. Both sides
are monomial in the computational basis, so the identity is checked on the eight basis states via
`threeQubit_evolution_ext`. On each, the `CNOT`s permute the target bit while the `T`/`T†`/`S` phase
gates accumulate a phase; the phase kickback sums to `0` on the seven states with `q₁q₂q₃ = 0`
and to `π` (hence `-1`) on `|111⟩`, exactly the phase `(-1)^{q₁q₂q₃}` of `C²(Z)`
(`ccontrolledZ_op`). -/
theorem figure49HadamardFree_eq_ccontrolledZ :
    figure49HadamardFree = ccontrolledUnitary pauliZGate := by
  refine threeQubit_evolution_ext (fun q1 q2 q3 => ?_)
  apply PureState.ext
  rw [Evolution.evolvePure_vec, Evolution.evolvePure_vec, figure49HadamardFree]
  simp only [Evolution.comp_op, ContinuousLinearMap.comp_apply, map_smul,
    cnot23_op, cnot13_op, cnot12_op, phase1_op, phase2_op, phase3_op, ccontrolledZ_op]
  fin_cases q1 <;> fin_cases q2 <;> fin_cases q3 <;>
    simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Nat.mul_zero, pow_zero, pow_one,
      smul_smul, one_mul, mul_one, ← Complex.exp_add, Fin.reduceAdd] <;>
    congr 1 <;>
    first
      | exact (congrArg Complex.exp (show _ = (0 : ℂ) by push_cast; ring)).trans Complex.exp_zero
      | exact (congrArg Complex.exp (show _ = (↑Real.pi * Complex.I) by push_cast; ring)).trans
          Complex.exp_pi_mul_I

end AxQM
