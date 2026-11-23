/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledPhaseShift
import AxQM.Postulates.API.ControlledZ

/-!
# AxQM.Postulates.API — phase-shift gate algebra and the `P(π) = Z` bridge

Small lemmas about the single-qubit phase-shift gate
`P(α) = phaseShiftGate α = diag(1, e^{iα})` and its consequences for the controlled phase gate:

* `qubit_evolution_ext` — a single-qubit gate is determined by its action on the computational
  basis `|0⟩, |1⟩` (the one-qubit analogue of `twoQubit_evolution_ext`).
* `phaseShiftGate_neg_comp_self` — the phase gate is inverted by negating its angle:
  `P(-α) · P(α) = 1`. The single-photon phase shifts of the optical Kerr gate (7.87) are undone
  by this identity when reducing that gate to a controlled phase.
* `phaseShiftGate_pi` — `P(π) = Z`: the relative-phase gate at angle `π` is the Pauli-`Z` gate,
  since `e^{iπ} = -1`.
* `controlledPhaseShift_pi_eq_controlledZGate` — `C(P(π)) = CZ`: a controlled phase rotation by `π`
  is exactly the controlled-`Z` gate. This is the conceptual core of the Δ = π specialisation in
  Nielsen & Chuang's optical logic gate (Exercise 7.23): a conditional π phase is a controlled-`Z`.

-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **A single-qubit gate is determined by its action on the computational basis.** Two evolutions
`A`, `B` of `qubit` are equal as soon as their operators agree on the two basis vectors `|0⟩`,
`|1⟩`. The one-qubit analogue of `twoQubit_evolution_ext`. -/
theorem qubit_evolution_ext {A B : Evolution qubit}
    (h : ∀ i : Fin 2, A.op (qubitBasis i).vec = B.op (qubitBasis i).vec) : A = B := by
  apply Evolution.ext
  apply ContinuousLinearMap.coe_injective
  refine Module.Basis.ext (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis (fun i => ?_)
  have hb : (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis i = (qubitBasis i).vec := by
    rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, qubitBasis_vec]
  rw [hb]
  exact h i

/-- **The phase-shift gate is inverted by negating its angle:** `P(-α) · P(α) = 1`, since applying
`P(α)` then `P(-α)` multiplies `|i⟩` by `[1, e^{iα}]ᵢ · [1, e^{-iα}]ᵢ = 1`. -/
theorem phaseShiftGate_neg_comp_self (α : ℝ) :
    (phaseShiftGate (-α)).comp (phaseShiftGate α) = Evolution.id := by
  apply qubit_evolution_ext
  intro i
  rw [Evolution.comp_op, ContinuousLinearMap.comp_apply, phaseShiftGate_op_apply_qubitBasis,
    map_smul, phaseShiftGate_op_apply_qubitBasis, Evolution.id_op, one_apply_eq_self,
    smul_smul]
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_neg,
          neg_mul,
      mul_one, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, qubitBasis_vec] <;>
    exact one_smul _ _

/-- **`P(π) = Z`.** The relative-phase gate at angle `π` is the Pauli-`Z` gate: on `|i⟩` it acts as
`[1, e^{iπ}]ᵢ = [1, -1]ᵢ = (-1)ⁱ`, exactly the action of `Z`. -/
theorem phaseShiftGate_pi : phaseShiftGate Real.pi = pauliZGate := by
  apply qubit_evolution_ext
  intro i
  rw [phaseShiftGate_op_apply_qubitBasis, pauliZGate_op_apply_qubitBasis]
  fin_cases i <;> simp [Complex.exp_pi_mul_I]

/-- **`P(0) = I`.** The relative-phase gate at angle `0` is the identity: `[1, e^{i·0}]ᵢ = [1, 1]ᵢ`
applies no relative phase, so `P(0)` fixes both `|0⟩` and `|1⟩`. -/
theorem phaseShiftGate_zero : phaseShiftGate 0 = Evolution.id := by
  apply qubit_evolution_ext
  intro i
  rw [phaseShiftGate_op_apply_qubitBasis, Evolution.id_op, one_apply_eq_self]
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, qubitBasis_vec] <;>
    exact one_smul ℂ _

/-- **`C(P(π)) = CZ`.** A controlled phase rotation by `π` is exactly the controlled-`Z` gate — the
conceptual core of the Δ = π specialisation of Nielsen & Chuang's optical logic gate (Exercise
7.23): a conditional `π` phase flip is a controlled-`Z`. Immediate from `P(π) = Z`
(`phaseShiftGate_pi`) and `controlledZGate = controlledUnitary pauliZGate`. -/
theorem controlledPhaseShift_pi_eq_controlledZGate :
    controlledPhaseShift Real.pi = controlledZGate := by
  rw [controlledPhaseShift_eq, phaseShiftGate_pi, controlledZGate]

end AxQM
