/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.NMRControlledZ
import AxQM.Postulates.API.NMRSingleQubitSynthesis
import AxQM.Postulates.API.Teleportation

/-!
# AxQM.Postulates.API — the NMR Grover oracles (N&C Ex 7.50)

The **two-qubit Grover search oracles** `O` and their **NMR
realisations** (Nielsen & Chuang Exercise 7.50). For a four-element search (`n = 2` qubits) the
oracle `O` for a marked item `x₀ ∈ {0,1,2,3}` flips the sign of the basis state `|x₀⟩` and fixes
every other, i.e. `O = diag` with a single `-1`. N&C give the `x₀ = 3` case (`O = diag(1,1,1,-1)`,
the controlled-`Z`) as `nmrControlledZSequence` (Exercise 7.41); **this file supplies the `x₀ = 0,
1, 2` oracles and their circuits**, obtained by conjugating the controlled-`Z` with bit-flips that
move `|x₀⟩` to the `|11⟩` corner. The statement of Exercise 7.50 is in
`AxQM/NC/Ch7/Exercise7_50.lean`.

## What is here

* **Gate algebra for the conjugation** — `rotXGate_pi_eq_globalPhaseGate_comp_pauliXGate`
  (`R_x(π) = e^{-iπ/2}·X`, the NMR bit-flip pulse *is* `X` up to a global phase), its right/left
  factor forms `rotXGate_pi_on{Right,Left}_eq` (the structural lemmas
  `globalPhaseGate_on{Right,Left}` / `_zero` — a global phase on one factor is a global phase on the
  whole system; `globalPhaseGate 0 = 1` — are in
  `AxQM/Postulates/API/NMRControlledZ.lean`, used here through that import),
  and the phase-collection lemmas
  `globalPhaseGate_conj_collect`/`_collect₂` that pull all the global phases of a symmetric
  conjugation to the front (real-angle arithmetic, no `i²`).
* `groverOracle{Zero,One,Two}` — the **ideal oracle gates** for `x₀ = 0, 1, 2`: the controlled-`Z`
  conjugated by the Pauli-`X` bit-flips that carry `|x₀⟩ ↔ |11⟩` (`X₁X₂`, `X₁`, `X₂`
  respectively), together with `groverOracle{..}_op_apply_qubitBasis` proving each flips the sign of
  exactly `|x₀⟩` — i.e. that these gates really are the Grover oracles.
* `nmrGroverOracle{Zero,One,Two}` — the **NMR circuits** realising those oracles: the same
  conjugation with the ideal `X` replaced by the physical `R_x(π)` pulse and the ideal
  controlled-`Z` by `nmrControlledZSequence` — built from just single-qubit rotations and the free
  `J`-coupling `e^{-iH/2ℏJ}`, exactly the building blocks Exercise 7.50 allows.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### Gate algebra for the bit-flip conjugation -/

/-- **The `180°` `x`-rotation as a gate equals `X` up to the global phase `e^{-iπ/2} = -i`:**
`R_x(π) = e^{-iπ/2}·X`, an `Evolution` identity on the qubit. Lifts the concrete matrix identity
`R_x(π) = -i·X` (`cos(π/2) = 0`, `sin(π/2) = 1`) through `Matrix.toEuclideanCLM`, with `-i` reified
as the global-phase gate `globalPhaseGate (-π/2)`. -/
theorem rotXGate_pi_eq_globalPhaseGate_comp_pauliXGate :
    rotXGate Real.pi = (globalPhaseGate (-(Real.pi / 2))).comp pauliXGate := by
  apply Evolution.ext
  have hmat : Concrete.rotX Real.pi = (-Complex.I) • Concrete.pauliX := by
    rw [Concrete.rotX_eq, Concrete.pauliX]; ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Real.cos_pi_div_two, Real.sin_pi_div_two, Matrix.smul_apply]
  have hI : Complex.exp ((-(Real.pi / 2) : ℝ) * Complex.I) = -Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  rw [rotXGate_op, Evolution.comp_op, globalPhaseGate_op, pauliXGate_op, hmat, map_smul, hI]
  exact ((ContinuousLinearMap.smul_comp _ _ _).trans
    (congrArg _ (ContinuousLinearMap.id_comp _))).symm

/-- **The right-factor `R_x(π)` pulse is the right-factor `X` up to the global phase `e^{-iπ/2}`:**
`(R_x(π))₂ = e^{-iπ/2}·X₂` on `S ⊗ qubit`. Immediate from
`rotXGate_pi_eq_globalPhaseGate_comp_pauliXGate` and the functoriality of `onRight`. -/
theorem rotXGate_pi_onRight_eq (S : QSystem) :
    (rotXGate Real.pi).onRight S
      = (globalPhaseGate (-(Real.pi / 2))).comp (pauliXGate.onRight S) := by
  rw [rotXGate_pi_eq_globalPhaseGate_comp_pauliXGate, ← Evolution.onRight_comp,
    globalPhaseGate_onRight]

/-- **The left-factor `R_x(π)` pulse is the left-factor `X` up to the global phase `e^{-iπ/2}`:**
`(R_x(π))₁ = e^{-iπ/2}·X₁` on `qubit ⊗ T`. -/
theorem rotXGate_pi_onLeft_eq (T : QSystem) :
    (rotXGate Real.pi).onLeft T
      = (globalPhaseGate (-(Real.pi / 2))).comp (pauliXGate.onLeft T) := by
  rw [rotXGate_pi_eq_globalPhaseGate_comp_pauliXGate, ← Evolution.onLeft_comp,
    globalPhaseGate_onLeft]

/-- **Collect the global phases of a single-pulse conjugation.** Conjugating a gate `B` by a
phase-prefixed pulse `(e^{ia}·1)·A` on both sides pulls all three global phases to the front:
`((e^{ia}·A)·(e^{ib}·B)·(e^{ia}·A)) = e^{i(a+b+a)}·(A·B·A)`. The global phase is central, so it
factors out of the conjugation; proved at the operator level with the scalars combined via
`e^{ix}e^{iy} = e^{i(x+y)}` (no `i²` arithmetic). -/
theorem globalPhaseGate_conj_collect {S : QSystem} (a b : ℝ) (A B : Evolution S) :
    ((globalPhaseGate a).comp A).comp
        (((globalPhaseGate b).comp B).comp ((globalPhaseGate a).comp A))
      = (globalPhaseGate (a + b + a)).comp (A.comp (B.comp A)) := by
  apply Evolution.ext
  simp only [Evolution.comp_op, globalPhaseGate_op, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    smul_smul, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- **Collect the global phases of a two-pulse conjugation.** As `globalPhaseGate_conj_collect`, but
with the conjugating operator itself a product of two phase-prefixed pulses `(e^{ia}·P)·(e^{ia}·Q)`:
`(e^{i(a+a+b+a+a)})·((P·Q)·B·(P·Q))`. Used for the `x₀ = 0` oracle, whose bit-flip conjugation
flips *both* spins. -/
theorem globalPhaseGate_conj_collect₂ {S : QSystem} (a b : ℝ) (P Q B : Evolution S) :
    (((globalPhaseGate a).comp P).comp ((globalPhaseGate a).comp Q)).comp
        (((globalPhaseGate b).comp B).comp
          (((globalPhaseGate a).comp P).comp ((globalPhaseGate a).comp Q)))
      = (globalPhaseGate (a + a + b + a + a)).comp ((P.comp Q).comp (B.comp (P.comp Q))) := by
  apply Evolution.ext
  simp only [Evolution.comp_op, globalPhaseGate_op, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    smul_smul, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-! ### The ideal Grover oracle gates -/

/-- **The Grover oracle for `x₀ = 0`** (`O = diag(-1,1,1,1)`): the controlled-`Z` conjugated by
`X₁X₂`, the bit-flips that carry `|00⟩ ↔ |11⟩`. It flips the sign of `|00⟩` only
(`groverOracleZero_op_apply_qubitBasis`). -/
def groverOracleZero : Evolution (qubit ⊗ qubit) :=
  ((pauliXGate.onLeft qubit).comp (pauliXGate.onRight qubit)).comp
    (controlledZGate.comp ((pauliXGate.onLeft qubit).comp (pauliXGate.onRight qubit)))

/-- **The Grover oracle for `x₀ = 1`** (`O = diag(1,-1,1,1)`): the controlled-`Z` conjugated by
`X₁`, the bit-flip on the first spin that carries `|01⟩ ↔ |11⟩`. It flips the sign of `|01⟩` only
(`groverOracleOne_op_apply_qubitBasis`). -/
def groverOracleOne : Evolution (qubit ⊗ qubit) :=
  (pauliXGate.onLeft qubit).comp (controlledZGate.comp (pauliXGate.onLeft qubit))

/-- **The Grover oracle for `x₀ = 2`** (`O = diag(1,1,-1,1)`): the controlled-`Z` conjugated by
`X₂`, the bit-flip on the second spin that carries `|10⟩ ↔ |11⟩`. It flips the sign of `|10⟩` only
(`groverOracleTwo_op_apply_qubitBasis`). -/
def groverOracleTwo : Evolution (qubit ⊗ qubit) :=
  (pauliXGate.onRight qubit).comp (controlledZGate.comp (pauliXGate.onRight qubit))

/-- **`groverOracleZero` flips exactly `|00⟩`.** On the computational basis, `groverOracleZero`
sends `|a⟩⊗|b⟩` to `-|a⟩⊗|b⟩` at `|00⟩` and to `|a⟩⊗|b⟩` at every other state, so this gate is the
Grover oracle `O = diag(-1,1,1,1)` (`x₀ = 0`). Proof: unfold the two conjugating bit-flips and the
controlled-`Z` on the computational basis (`onLeft`/`onRight_op_tmul`,
`pauliXGate_op_apply_qubitBasis`, `controlledZGate_op_apply_qubitBasis`) and evaluate the sign in
each of the four cases. -/
theorem groverOracleZero_op_apply_qubitBasis (a b : Fin 2) :
    groverOracleZero.op ((qubitBasis a) ⊗ (qubitBasis b)).vec
      = (if a = 0 ∧ b = 0 then (-1 : ℂ) else 1) • ((qubitBasis a) ⊗ (qubitBasis b)).vec := by
  change (pauliXGate.onLeft qubit).op ((pauliXGate.onRight qubit).op (controlledZGate.op
      ((pauliXGate.onLeft qubit).op
        ((pauliXGate.onRight qubit).op ((qubitBasis a ⊗ qubitBasis b).vec))))) = _
  simp only [PureState.tmul_vec, Evolution.onRight_op_tmul, Evolution.onLeft_op_tmul,
    pauliXGate_op_apply_qubitBasis]
  rw [← PureState.tmul_vec, controlledZGate_op_apply_qubitBasis]
  simp only [PureState.tmul_vec,
    ]
  fin_cases a <;> fin_cases b <;>
    first
      | (simp; done)
      | (erw [map_smul]
         rw [Evolution.onRight_op_tmul]
         erw [map_smul]
         rw [Evolution.onLeft_op_tmul]
         rw [pauliXGate_op_apply_qubitBasis]
         try rw [pauliXGate_op_apply_qubitBasis]
         simp [Fin.isValue, Fin.reduceAdd])

/-- **`groverOracleOne` flips exactly `|01⟩`.** On the computational basis, `groverOracleOne` sends
`|a⟩⊗|b⟩` to `-|a⟩⊗|b⟩` at `|01⟩` and to `|a⟩⊗|b⟩` elsewhere, so this gate is the Grover oracle
`O = diag(1,-1,1,1)` (`x₀ = 1`). -/
theorem groverOracleOne_op_apply_qubitBasis (a b : Fin 2) :
    groverOracleOne.op ((qubitBasis a) ⊗ (qubitBasis b)).vec
      = (if a = 0 ∧ b = 1 then (-1 : ℂ) else 1) • ((qubitBasis a) ⊗ (qubitBasis b)).vec := by
  change (pauliXGate.onLeft qubit).op (controlledZGate.op
      ((pauliXGate.onLeft qubit).op ((qubitBasis a ⊗ qubitBasis b).vec))) = _
  simp only [PureState.tmul_vec, Evolution.onLeft_op_tmul, pauliXGate_op_apply_qubitBasis]
  rw [← PureState.tmul_vec, controlledZGate_op_apply_qubitBasis]
  simp only [PureState.tmul_vec]
  fin_cases a <;> fin_cases b <;>
    first
      | (simp; done)
      | (erw [map_smul]
         rw [Evolution.onLeft_op_tmul]
         rw [show ∀ i : Fin 2, pauliXGate.op (qubitBasis i).vec = (qubitBasis (i + 1)).vec
           from pauliXGate_op_apply_qubitBasis]
         simp [Fin.isValue, Fin.reduceAdd])

/-- **`groverOracleTwo` flips exactly `|10⟩`.** On the computational basis, `groverOracleTwo` sends
`|a⟩⊗|b⟩` to `-|a⟩⊗|b⟩` at `|10⟩` and to `|a⟩⊗|b⟩` elsewhere, so this gate is the Grover oracle
`O = diag(1,1,-1,1)` (`x₀ = 2`). -/
theorem groverOracleTwo_op_apply_qubitBasis (a b : Fin 2) :
    groverOracleTwo.op ((qubitBasis a) ⊗ (qubitBasis b)).vec
      = (if a = 1 ∧ b = 0 then (-1 : ℂ) else 1) • ((qubitBasis a) ⊗ (qubitBasis b)).vec := by
  change (pauliXGate.onRight qubit).op (controlledZGate.op
      ((pauliXGate.onRight qubit).op ((qubitBasis a ⊗ qubitBasis b).vec))) = _
  simp only [PureState.tmul_vec, Evolution.onRight_op_tmul, pauliXGate_op_apply_qubitBasis]
  rw [← PureState.tmul_vec, controlledZGate_op_apply_qubitBasis]
  simp only [PureState.tmul_vec,
    ]
  fin_cases a <;> fin_cases b <;>
    first
      | (simp; done)
      | (erw [map_smul]
         rw [Evolution.onRight_op_tmul]
         rw [show ∀ i : Fin 2, pauliXGate.op (qubitBasis i).vec = (qubitBasis (i + 1)).vec
           from pauliXGate_op_apply_qubitBasis]
         simp [Fin.isValue, Fin.reduceAdd])

/-! ### The NMR circuits -/

/-- **The NMR circuit for the `x₀ = 0` oracle.** The controlled-`Z` sequence conjugated by the
physical `R_x(π)` bit-flip pulses on *both* spins — built from single-qubit rotations and the free
`J`-coupling `e^{-iH/2ℏJ}` only. At `c·t = π/4` it realises `groverOracleZero` up to a global phase
(see `AxQM/NC/Ch7/Exercise7_50.lean`). -/
def nmrGroverOracleZero (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  (((rotXGate Real.pi).onLeft qubit).comp ((rotXGate Real.pi).onRight qubit)).comp
    ((nmrControlledZSequence c t).comp
      (((rotXGate Real.pi).onLeft qubit).comp ((rotXGate Real.pi).onRight qubit)))

/-- **The NMR circuit for the `x₀ = 1` oracle.** The controlled-`Z` sequence conjugated by the
physical `R_x(π)` bit-flip pulse on the first spin — single-qubit rotations and `e^{-iH/2ℏJ}` only.
At `c·t = π/4` it realises `groverOracleOne` up to a global phase. -/
def nmrGroverOracleOne (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((rotXGate Real.pi).onLeft qubit).comp
    ((nmrControlledZSequence c t).comp ((rotXGate Real.pi).onLeft qubit))

/-- **The NMR circuit for the `x₀ = 2` oracle.** The controlled-`Z` sequence conjugated by the
physical `R_x(π)` bit-flip pulse on the second spin — single-qubit rotations and `e^{-iH/2ℏJ}` only.
At `c·t = π/4` it realises `groverOracleTwo` up to a global phase. -/
def nmrGroverOracleTwo (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((rotXGate Real.pi).onRight qubit).comp
    ((nmrControlledZSequence c t).comp ((rotXGate Real.pi).onRight qubit))

end AxQM
