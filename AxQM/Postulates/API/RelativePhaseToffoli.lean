/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Fredkin
import AxQM.Postulates.API.ControlledRotation
import AxQM.Postulates.API.Teleportation
import AxQM.Concrete.Rotation

/-!
# AxQM.Postulates.API — the relative-phase Toffoli circuit (N&C Exercise 4.26)

The three-qubit circuit of **Nielsen & Chuang, Exercise 4.26**, made
of four `R_y(±π/4)` rotations on the target qubit interleaved with three `CNOT`s (two controlled by
the second qubit, one by the first) that implements a Toffoli gate *up to relative phases*.

## What is formalised

* `relativePhaseToffoliGate` — the circuit of Exercise 4.26 as an `Evolution` on
  `qubit ⊗ (qubit ⊗ qubit)`: reading left to right on the target (third) qubit,
  `R_y(π/4) · CNOT₂₃ · R_y(π/4) · CNOT₁₃ · R_y(-π/4) · CNOT₂₃ · R_y(-π/4)`, where `CNOT₂₃` is the
  `CNOT` with control qubit 2 and `CNOT₁₃` the one with control qubit 1, both targeting qubit 3.
* `relativePhaseToffoliGate_evolvePure_vec` — **the exercise's claim** in terms of state vectors: on
  every computational-basis input the circuit produces `e^{iθ(c₁,c₂,t)} |c₁, c₂, t ⊕ c₁·c₂⟩`, the
  Toffoli output up to a phase `toffoliRelPhase c₁ c₂ t ∈ {±1}` (the only nontrivial phase is `-1`,
  at `|1,0,1⟩`). That this differs from the Toffoli gate only
  by a *relative* phase, via N&C's own `PureState.RelativePhaseEquiv`, is stated in
  `AxQM/NC/Ch4/Exercise4_26.lean`.

## Design notes

* **Proof strategy — factor onto the target qubit, cancel angles at the gate level.** Every gate in
  the circuit fixes the two control qubits (in a computational-basis state) and acts on the target
  qubit by a single-qubit gate set by the controls; `relativePhaseToffoliGate_evolvePure_factor`
  makes this precise, reducing the three-qubit action to `relativePhaseToffoliTargetGate c₁ c₂`
  acting on the target. Crucially this keeps the target state *symbolic*, so the four `R_y(±π/4)`
  rotations collapse by the group law `rotYGate_comp` and the `X`-conjugation
  `pauliXGate_comp_rotYGate_comp_pauliXGate` — the angles cancel *before* any state is plugged in,
  so the proof never touches `cos(π/8)`/`sin(π/8)`. The four control settings reduce the target gate
  to `1` (`(0,0)`, `(0,1)`), `X` (`(1,1)`) or `Z` (`(1,0)`); only the last carries a phase, via
  `pauliZGate_op_apply_qubitBasis` (`Z|t⟩ = (-1)^t|t⟩`).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### Single-qubit gate algebra used to collapse the target rotations -/

/-- **`X` is an involution:** `X · X = 1` as a gate. Proved from the `X`-conjugation lemma at
`θ = 0`, so no matrix computation is needed. -/
theorem pauliXGate_comp_pauliXGate : pauliXGate.comp pauliXGate = Evolution.id := by
  have h : pauliXGate.comp pauliXGate = pauliXGate.comp ((rotYGate 0).comp pauliXGate) := by
    rw [rotYGate_zero, Evolution.id_comp]
  rw [h, pauliXGate_comp_rotYGate_comp_pauliXGate, neg_zero, rotYGate_zero]

/-- **`X` moves through `R_y` by flipping the angle:** `X · R_y(θ) = R_y(-θ) · X`. The one-sided
form of the `X`-conjugation `X · R_y(θ) · X = R_y(-θ)`. -/
theorem pauliXGate_comp_rotYGate (θ : ℝ) :
    pauliXGate.comp (rotYGate θ) = (rotYGate (-θ)).comp pauliXGate := by
  calc pauliXGate.comp (rotYGate θ)
      = pauliXGate.comp ((rotYGate θ).comp (pauliXGate.comp pauliXGate)) := by
          rw [pauliXGate_comp_pauliXGate, Evolution.comp_id]
    _ = (pauliXGate.comp ((rotYGate θ).comp pauliXGate)).comp pauliXGate := by
          rw [Evolution.comp_assoc, Evolution.comp_assoc]
    _ = (rotYGate (-θ)).comp pauliXGate := by rw [pauliXGate_comp_rotYGate_comp_pauliXGate]

/-- **`X` moves right past an `R_y` in a longer product:** `X · (R_y(θ) · g) = R_y(-θ) · (X · g)`.
Lets an `X` bubble to the right through a chain of rotations. -/
theorem pauliXGate_comp_rotYGate_comp (θ : ℝ) (g : Evolution qubit) :
    pauliXGate.comp ((rotYGate θ).comp g) = (rotYGate (-θ)).comp (pauliXGate.comp g) := by
  rw [← Evolution.comp_assoc, pauliXGate_comp_rotYGate, Evolution.comp_assoc]

/-- **Two `X`s in a product cancel:** `X · (X · g) = g`. -/
theorem pauliXGate_comp_pauliXGate_comp (g : Evolution qubit) :
    pauliXGate.comp (pauliXGate.comp g) = g := by
  rw [← Evolution.comp_assoc, pauliXGate_comp_pauliXGate, Evolution.id_comp]

/-- **The `π`-rotation about `ŷ`, then `X`, is `Z`:** `R_y(-π) · X = Z` as a gate. This carries the
lone relative phase of Exercise 4.26 (the `|1,0⟩` control branch). The image, under the `⋆`-algebra
isomorphism `Matrix.toEuclideanCLM`, of the concrete matrix identity `R_y(-π) · X = Z`
(as `R_y(-π) = !![0, 1; -1, 0]`). -/
theorem rotYGate_neg_pi_comp_pauliXGate : (rotYGate (-Real.pi)).comp pauliXGate = pauliZGate := by
  have hmat : Concrete.rotY (-Real.pi) * Concrete.pauliX = Concrete.pauliZ := by
    rw [Concrete.rotY_eq]
    have hc : Real.cos (-Real.pi / 2) = 0 := by
      rw [show (-Real.pi / 2) = -(Real.pi / 2) by ring, Real.cos_neg, Real.cos_pi_div_two]
    have hs : Real.sin (-Real.pi / 2) = -1 := by
      rw [show (-Real.pi / 2) = -(Real.pi / 2) by ring, Real.sin_neg, Real.sin_pi_div_two]
    rw [hc, hs]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Concrete.pauliX, Concrete.pauliZ]
  apply Evolution.ext
  simp only [Evolution.comp_op, rotYGate_op, pauliXGate_op, pauliZGate_op]
  rw [← hmat, map_mul]; rfl

/-! ### The circuit and its target-qubit reduction -/

/-- The single-qubit gate applied to the target when a control is `c` (`X` if `c = 1`, identity if
`c = 0`): `X^c`. -/
def targetXPow (c : Fin 2) : Evolution qubit := if c = 0 then Evolution.id else pauliXGate

@[simp] theorem targetXPow_zero : targetXPow 0 = Evolution.id := rfl

@[simp] theorem targetXPow_one : targetXPow 1 = pauliXGate := rfl

/-- **`X^c` (the target gate `targetXPow`) acts on a computational basis ket by `d ↦ d + c`:**
`(targetXPow c)|d⟩ = |d + c⟩`. The `evolvePure` companion used to compute the parity a `CNOT` XORs
onto its target. -/
theorem targetXPow_evolvePure_qubitBasis (c d : Fin 2) :
    (targetXPow c).evolvePure (qubitBasis d) = qubitBasis (d + c) := by
  fin_cases c <;>
    simp [targetXPow, Evolution.id_evolvePure, pauliXGate_evolvePure_qubitBasis]

/-- **The target-qubit action of the circuit for a fixed control setting `(c₁, c₂)`:** the product
of the four `R_y(±π/4)` rotations with `X^{c₂}`, `X^{c₁}`, `X^{c₂}` inserted where the three `CNOT`s
fire. This is the single-qubit gate `relativePhaseToffoliGate` applies to the target when the
controls are `|c₁⟩, |c₂⟩` (see `relativePhaseToffoliGate_evolvePure_factor`). -/
def relativePhaseToffoliTargetGate (c₁ c₂ : Fin 2) : Evolution qubit :=
  (rotYGate (-(Real.pi / 4))).comp ((targetXPow c₂).comp ((rotYGate (-(Real.pi / 4))).comp
    ((targetXPow c₁).comp ((rotYGate (Real.pi / 4)).comp
      ((targetXPow c₂).comp (rotYGate (Real.pi / 4)))))))

/-- **`R_y(θ)` on the target (third) qubit** of `qubit ⊗ (qubit ⊗ qubit)`: `1 ⊗ (1 ⊗ R_y θ)`. -/
def rotYThirdGate (θ : ℝ) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  ((rotYGate θ).onRight qubit).onRight qubit

/-- **`CNOT` with control qubit 1 and target qubit 3**, `C(1 ⊗ X)`: fires `X` on the third qubit
when the first (control) qubit is `|1⟩`, leaving the second qubit untouched. -/
def cnotFirstThirdGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  controlledUnitary (pauliXGate.onRight qubit)

/-- **The relative-phase Toffoli circuit of Nielsen & Chuang, Exercise 4.26.** On
`qubit ⊗ (qubit ⊗ qubit)`, reading left to right on the target (third) qubit: `R_y(π/4)`, `CNOT₂₃`,
`R_y(π/4)`, `CNOT₁₃`, `R_y(-π/4)`, `CNOT₂₃`, `R_y(-π/4)`, where `CNOT₂₃` (`cnotGate.onRight qubit`)
has control qubit 2 and `CNOT₁₃` (`cnotFirstThirdGate`) has control qubit 1, both with target
qubit 3. It equals a Toffoli gate up to relative phases
(`relativePhaseToffoliGate_evolvePure_vec`). -/
def relativePhaseToffoliGate : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (rotYThirdGate (-(Real.pi / 4))).comp ((cnotGate.onRight qubit).comp
    ((rotYThirdGate (-(Real.pi / 4))).comp (cnotFirstThirdGate.comp
      ((rotYThirdGate (Real.pi / 4)).comp ((cnotGate.onRight qubit).comp
        (rotYThirdGate (Real.pi / 4)))))))

/-! ### Factorised action on computational-basis inputs -/

/-- **`R_y(θ)` on the third qubit passes the two control qubits through.** -/
theorem rotYThirdGate_evolvePure (θ : ℝ) (c₁ c₂ : Fin 2) (φ : PureState qubit) :
    (rotYThirdGate θ).evolvePure (qubitBasis c₁ ⊗ (qubitBasis c₂ ⊗ φ))
      = qubitBasis c₁ ⊗ (qubitBasis c₂ ⊗ (rotYGate θ).evolvePure φ) := by
  rw [rotYThirdGate, Evolution.onRight_evolvePure, Evolution.onRight_evolvePure]

/-- **`CNOT₂₃` acts on the target by `X^{c₂}`**, passing both controls through. -/
theorem cnotSecondThirdGate_evolvePure (c₁ c₂ : Fin 2) (φ : PureState qubit) :
    (cnotGate.onRight qubit).evolvePure (qubitBasis c₁ ⊗ (qubitBasis c₂ ⊗ φ))
      = qubitBasis c₁ ⊗ (qubitBasis c₂ ⊗ (targetXPow c₂).evolvePure φ) := by
  rw [Evolution.onRight_evolvePure, cnotGate_def]
  congr 1
  fin_cases c₂ <;>
    simp only [Fin.mk_zero, Fin.mk_one, controlledUnitary_evolvePure_ketZero,
      controlledUnitary_evolvePure_ketOne, targetXPow_zero, targetXPow_one, Evolution.id_evolvePure]

/-- **`CNOT₁₃` acts on the target by `X^{c₁}`**, passing both controls through. -/
theorem cnotFirstThirdGate_evolvePure (c₁ c₂ : Fin 2) (φ : PureState qubit) :
    cnotFirstThirdGate.evolvePure (qubitBasis c₁ ⊗ (qubitBasis c₂ ⊗ φ))
      = qubitBasis c₁ ⊗ (qubitBasis c₂ ⊗ (targetXPow c₁).evolvePure φ) := by
  rw [cnotFirstThirdGate]
  fin_cases c₁ <;>
    simp only [Fin.mk_zero, Fin.mk_one, controlledUnitary_evolvePure_ketZero,
      controlledUnitary_evolvePure_ketOne, Evolution.onRight_evolvePure, targetXPow_zero,
      targetXPow_one, Evolution.id_evolvePure]

/-- **The circuit factors through its target-qubit gate:** on a computational-basis control setting
`(c₁, c₂)` and any target state `φ`, `relativePhaseToffoliGate` fixes the controls and applies
`relativePhaseToffoliTargetGate c₁ c₂` to the target. -/
theorem relativePhaseToffoliGate_evolvePure_factor (c₁ c₂ : Fin 2) (φ : PureState qubit) :
    relativePhaseToffoliGate.evolvePure (qubitBasis c₁ ⊗ (qubitBasis c₂ ⊗ φ))
      = qubitBasis c₁ ⊗ (qubitBasis c₂ ⊗
          (relativePhaseToffoliTargetGate c₁ c₂).evolvePure φ) := by
  rw [relativePhaseToffoliGate, relativePhaseToffoliTargetGate]
  simp only [Evolution.evolvePure_comp, rotYThirdGate_evolvePure, cnotSecondThirdGate_evolvePure,
    cnotFirstThirdGate_evolvePure]

/-! ### Collapsing the target gate for each control setting -/

/-- Control `|0,0⟩`: the four rotations cancel, `R_y(-π/4)·R_y(-π/4)·R_y(π/4)·R_y(π/4) = 1`. -/
theorem relativePhaseToffoliTargetGate_zero_zero :
    relativePhaseToffoliTargetGate 0 0 = Evolution.id := by
  rw [relativePhaseToffoliTargetGate]
  simp only [targetXPow_zero, Evolution.id_comp]
  rw [rotYGate_comp, rotYGate_comp, rotYGate_comp,
    show (-(Real.pi / 4) + (-(Real.pi / 4) + (Real.pi / 4 + Real.pi / 4))) = 0 by ring,
    rotYGate_zero]

/-- Control `|0,1⟩`: the two `X`s (from qubit 2) cancel and the rotations sum to `0`, giving `1`. -/
theorem relativePhaseToffoliTargetGate_zero_one :
    relativePhaseToffoliTargetGate 0 1 = Evolution.id := by
  rw [relativePhaseToffoliTargetGate]
  simp only [targetXPow_zero, targetXPow_one, Evolution.id_comp]
  rw [pauliXGate_comp_rotYGate_comp, pauliXGate_comp_rotYGate_comp, pauliXGate_comp_pauliXGate_comp,
    rotYGate_comp, rotYGate_comp, rotYGate_comp,
    show (-(Real.pi / 4) + (- -(Real.pi / 4) + (-(Real.pi / 4) + Real.pi / 4))) = 0 by ring,
    rotYGate_zero]

/-- Control `|1,0⟩`: the single `X` (from qubit 1) bubbles right, the four rotations sum to `-π`,
and `R_y(-π)·X = Z` — the branch carrying the relative phase. -/
theorem relativePhaseToffoliTargetGate_one_zero :
    relativePhaseToffoliTargetGate 1 0 = pauliZGate := by
  rw [relativePhaseToffoliTargetGate]
  simp only [targetXPow_zero, targetXPow_one, Evolution.id_comp]
  rw [pauliXGate_comp_rotYGate_comp, pauliXGate_comp_rotYGate, ← Evolution.comp_assoc,
    rotYGate_comp, ← Evolution.comp_assoc, rotYGate_comp, ← Evolution.comp_assoc, rotYGate_comp,
    show (-(Real.pi / 4) + -(Real.pi / 4) + -(Real.pi / 4) + -(Real.pi / 4)) = -Real.pi by ring,
    rotYGate_neg_pi_comp_pauliXGate]

/-- Control `|1,1⟩`: the three `X`s reduce to one and the rotations cancel, giving `X` — here the
Toffoli flips the target. -/
theorem relativePhaseToffoliTargetGate_one_one :
    relativePhaseToffoliTargetGate 1 1 = pauliXGate := by
  rw [relativePhaseToffoliTargetGate]
  simp only [targetXPow_one]
  rw [pauliXGate_comp_rotYGate_comp, pauliXGate_comp_pauliXGate_comp, pauliXGate_comp_rotYGate,
    ← Evolution.comp_assoc, rotYGate_comp, ← Evolution.comp_assoc, rotYGate_comp,
    ← Evolution.comp_assoc, rotYGate_comp,
    show (-(Real.pi / 4) + - -(Real.pi / 4) + Real.pi / 4 + -(Real.pi / 4)) = 0 by ring,
    rotYGate_zero, Evolution.id_comp]

/-! ### The relative phase and the state-vector identity -/

/-- The relative phase `e^{iθ(c₁,c₂,t)}` of Exercise 4.26: `-1` exactly on the input `|1,0,1⟩` (the
`Z` control branch acting on `|1⟩`), and `+1` on every other computational-basis input. -/
def toffoliRelPhase (c₁ c₂ t : Fin 2) : ℂ := if c₁ = 1 ∧ c₂ = 0 ∧ t = 1 then -1 else 1

/-- **Nielsen & Chuang, Exercise 4.26 (state-vector form).** The circuit takes each
computational-basis state `|c₁, c₂, t⟩` to `e^{iθ(c₁,c₂,t)} |c₁, c₂, t ⊕ c₁·c₂⟩`: the Toffoli
output `|c₁, c₂, t ⊕ c₁·c₂⟩` scaled by the relative phase `toffoliRelPhase c₁ c₂ t ∈ {±1}`. Proved
by factoring onto the target qubit (`relativePhaseToffoliGate_evolvePure_factor`), collapsing the
target gate to `1`/`X`/`Z` for each control setting, and reading off `Z|t⟩ = (-1)^t|t⟩`. -/
theorem relativePhaseToffoliGate_evolvePure_vec (c₁ c₂ t : Fin 2) :
    (relativePhaseToffoliGate.evolvePure
          (qubitBasis c₁ ⊗ (qubitBasis c₂ ⊗ qubitBasis t))).vec
      = toffoliRelPhase c₁ c₂ t •
          (qubitBasis c₁ ⊗ (qubitBasis c₂ ⊗ qubitBasis (t + c₁ * c₂))).vec := by
  rw [relativePhaseToffoliGate_evolvePure_factor]
  fin_cases c₁ <;> fin_cases c₂
  · simp only [Fin.zero_eta, Fin.isValue, relativePhaseToffoliTargetGate_zero_zero,
      Evolution.id_evolvePure, PureState.tmul_vec, qubitBasis_vec, toffoliRelPhase, zero_ne_one,
      true_and, false_and, ↓reduceIte, mul_zero, add_zero]
    exact (one_smul ℂ _).symm
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, relativePhaseToffoliTargetGate_zero_one,
      Evolution.id_evolvePure, PureState.tmul_vec, qubitBasis_vec, toffoliRelPhase, zero_ne_one,
      one_ne_zero, false_and, and_self, ↓reduceIte, mul_one, add_zero]
    exact (one_smul ℂ _).symm
  · have hs : ((-1 : ℂ) ^ (t : ℕ)) = toffoliRelPhase 1 0 t := by
      fin_cases t <;> simp [toffoliRelPhase]
    -- `simp only [tmul_smul]` pulls the phase out of the inner pair; the outer level does not
    -- fire under `simp` (nested-tensor `CompatibleSMul` instance), so close it explicitly.
    simp only [Fin.mk_zero, Fin.mk_one, relativePhaseToffoliTargetGate_one_zero, mul_zero,
      add_zero, PureState.tmul_vec, Evolution.evolvePure_vec, pauliZGate_op_apply_qubitBasis, hs,
      TensorProduct.tmul_smul]
    exact TensorProduct.tmul_smul (R := ℂ) (toffoliRelPhase 1 0 t) (qubitBasis 1).vec
      ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis t).vec)
  · simp only [Fin.mk_one, Fin.isValue, relativePhaseToffoliTargetGate_one_one,
      pauliXGate_evolvePure_qubitBasis, PureState.tmul_vec, qubitBasis_vec, toffoliRelPhase,
      one_ne_zero, false_and, and_false, ↓reduceIte, mul_one]
    exact (one_smul ℂ _).symm

end AxQM
