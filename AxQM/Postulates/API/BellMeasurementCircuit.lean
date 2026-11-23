/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Teleportation
import AxQM.Postulates.API.HadamardGate
import AxQM.Postulates.API.CnotXBasis
import AxQM.Postulates.API.CnotPauliYPropagation
import AxQM.Postulates.API.ToffoliHadamard
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.RelativePhase

/-!
# The Bell-basis measurement circuit (Nielsen & Chuang, Exercise 4.33)

N&C's circuit model measures only in the computational basis; to measure in another basis one first
*unitarily transforms that basis to the computational basis, then measures*.  For the Bell basis the
transforming circuit is a `CNOT` (control = first qubit, target = second) followed by a Hadamard on
the first qubit.  This file builds that circuit, proves it rotates the Bell basis onto the
computational basis (and its inverse prepares the Bell states), and derives Exercise 4.33's operator
answer: the induced measurement is the Bell-basis measurement `bellMeasurement`, whose measurement
operators and POVM elements are the four projectors onto the Bell states.

The statement of Exercise 4.33 is in `AxQM/NC/Ch4/Exercise4_33.lean`.

## Main definitions

* `bellPrepCircuit` — `CNOT ∘ (H ⊗ 1)`, the Bell-state **preparation** circuit `|xy⟩ ↦ |β_xy⟩`.
* `bellMeasurementCircuit` — `(H ⊗ 1) ∘ CNOT`, the exercise's **measurement** circuit
  `|β_xy⟩ ↦ |xy⟩`, the inverse of `bellPrepCircuit`.

## Main results

* `bellPrepCircuit_evolvePure_qubitBasis` — `bellPrepCircuit |xy⟩ = |β_xy⟩`.
* `bellMeasurementCircuit_evolvePure_bellState` — `bellMeasurementCircuit |β_xy⟩ = |xy⟩`.
* `bellMeasurementCircuit_op_adjoint_qubitBasis` — `U† |xy⟩ = |β_xy⟩`.
* `bellMeasurement_op_eq_bellMeasurementCircuit_conj` — **the measurement operators**: the induced
  measurement operator is `U† |xy⟩⟨xy| U = bellMeasurement.op (x, y) = |β_xy⟩⟨β_xy|`.

The companion **POVM elements** answer `bellMeasurement_toPOVM_elements_eq_bellProjector`
(`bellMeasurement.toPOVM.elements (x, y) = |β_xy⟩⟨β_xy|`) is a basic property of `bellMeasurement`
independent of the measurement circuit, so it is proved with `bellMeasurement` in
`AxQM/Postulates/API/Teleportation.lean` (imported here).
-/

open AxQM

namespace AxQM

noncomputable section

/-- **Bell-state preparation circuit** `CNOT ∘ (H ⊗ 1)`: apply a Hadamard to the first qubit, then a
`CNOT` (control = first qubit, target = second).  It sends the computational basis state `|xy⟩` to
the Bell state `|β_xy⟩`. -/
def bellPrepCircuit : Evolution (qubit ⊗ qubit) :=
  cnotGate.comp (hadamardGate.onLeft qubit)

/-- **Bell-basis measurement circuit** `(H ⊗ 1) ∘ CNOT` (Nielsen & Chuang Exercise 4.33): apply a
`CNOT` (control = first qubit, target = second), then a Hadamard to the first qubit.  It is the
inverse of `bellPrepCircuit` and rotates the Bell basis onto the computational basis, so
measuring it in the computational basis realises a measurement in the Bell basis. -/
def bellMeasurementCircuit : Evolution (qubit ⊗ qubit) :=
  (hadamardGate.onLeft qubit).comp cnotGate

/-- `CNOT (|+⟩ ⊗ |y⟩) = |β_{0y}⟩`: the `x = 0` prong of the Bell-state preparation, from expanding
`|+⟩ = (|0⟩ + |1⟩)/√2` and applying the CNOT truth table `CNOT|c,t⟩ = |c, t ⊕ c⟩`. -/
theorem cnotGate_evolvePure_qubitPlus_tmul (y : Fin 2) :
    cnotGate.evolvePure (qubitPlus.tmul (qubitBasis y)) = bellState 0 y := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, PureState.tmul_vec, bellState_vec, bellBasisVec,
    qubitPlus_vec_eq_smul_add, ← TensorProduct.smul_tmul', TensorProduct.add_tmul]
  simp only [cnotGate_op_smul, cnotGate_op_add, cnotGate_op_qubitBasisVec_tmul,
    PureState.tmul_vec, Fin.isValue, add_zero, Fin.val_zero, pow_zero, Concrete.invSqrt2]
  change (Real.sqrt 2 : ℂ)⁻¹ • ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis y).vec +
      (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis (y + 1)).vec) =
    (Real.sqrt 2 : ℂ)⁻¹ • ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis y).vec +
      (1 : ℂ) • ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis (y + 1)).vec :
        TensorProduct ℂ qubit.space qubit.space))
  rw [one_smul]

/-- `CNOT (|−⟩ ⊗ |y⟩) = |β_{1y}⟩`: the `x = 1` prong of the Bell-state preparation, from expanding
`|−⟩ = (|0⟩ − |1⟩)/√2` and applying the CNOT truth table `CNOT|c,t⟩ = |c, t ⊕ c⟩`. -/
theorem cnotGate_evolvePure_qubitMinus_tmul (y : Fin 2) :
    cnotGate.evolvePure (qubitMinus.tmul (qubitBasis y)) = bellState 1 y := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, PureState.tmul_vec, bellState_vec, bellBasisVec,
    qubitMinus_vec_eq_smul_add, ← TensorProduct.smul_tmul', TensorProduct.add_tmul,
    ← TensorProduct.smul_tmul']
  simp only [cnotGate_op_smul, cnotGate_op_add, cnotGate_op_qubitBasisVec_tmul,
    PureState.tmul_vec, Fin.isValue, add_zero, Fin.val_one, pow_one, Concrete.invSqrt2]

/-- **Bell-state preparation:** `bellPrepCircuit |xy⟩ = |β_xy⟩`, i.e. `|β_xy⟩ = CNOT (H ⊗ 1) |xy⟩`
(Nielsen & Chuang eqs. 1.24–1.25). -/
theorem bellPrepCircuit_evolvePure_qubitBasis (x y : Fin 2) :
    bellPrepCircuit.evolvePure ((qubitBasis x).tmul (qubitBasis y)) = bellState x y := by
  rw [bellPrepCircuit, Evolution.evolvePure_comp, Evolution.onLeft_evolvePure]
  fin_cases x <;>
    simp [hadamardGate_evolvePure_qubitBasis_zero, hadamardGate_evolvePure_qubitBasis_one,
      cnotGate_evolvePure_qubitPlus_tmul, cnotGate_evolvePure_qubitMinus_tmul]

/-- **Bell-basis measurement rotation:** `bellMeasurementCircuit |β_xy⟩ = |xy⟩`.  The circuit
rotates the Bell basis onto the computational basis.  Proof: `CNOT` is an involution, so
`CNOT |β_xy⟩ = H|x⟩ ⊗ |y⟩` (the inverse of the preparation), and the final Hadamard undoes the `H`
(`H² = 1`). -/
theorem bellMeasurementCircuit_evolvePure_bellState (x y : Fin 2) :
    bellMeasurementCircuit.evolvePure (bellState x y) = (qubitBasis x).tmul (qubitBasis y) := by
  have hcnot : cnotGate.evolvePure (bellState x y)
      = (hadamardGate.evolvePure (qubitBasis x)).tmul (qubitBasis y) := by
    conv_lhs => rw [← bellPrepCircuit_evolvePure_qubitBasis x y, bellPrepCircuit,
      Evolution.evolvePure_comp, Evolution.onLeft_evolvePure, ← Evolution.evolvePure_comp,
      cnotGate_comp_cnotGate, Evolution.id_evolvePure]
  rw [bellMeasurementCircuit, Evolution.evolvePure_comp, hcnot, Evolution.onLeft_evolvePure,
    ← Evolution.evolvePure_comp, hadamardGate_comp_self, Evolution.id_evolvePure]

/-- The adjoint of the measurement circuit sends `|xy⟩` back to the Bell state `|β_xy⟩`.  Since the
circuit is unitary, `U†` is its inverse, and `U |β_xy⟩ = |xy⟩` gives `U† |xy⟩ = |β_xy⟩`. -/
theorem bellMeasurementCircuit_op_adjoint_qubitBasis (x y : Fin 2) :
    (ContinuousLinearMap.adjoint bellMeasurementCircuit.op)
        ((qubitBasis x).vec ⊗ₜ[ℂ] (qubitBasis y).vec) = (bellState x y).vec := by
  have hrot : bellMeasurementCircuit.op (bellState x y).vec
      = (qubitBasis x).vec ⊗ₜ[ℂ] (qubitBasis y).vec := by
    have := congrArg PureState.vec (bellMeasurementCircuit_evolvePure_bellState x y)
    rwa [Evolution.evolvePure_vec, PureState.tmul_vec] at this
  rw [← hrot, ← ContinuousLinearMap.comp_apply, Evolution.adjoint_comp_self,
    one_apply_eq_self]

/-- **The measurement operators (Nielsen & Chuang Exercise 4.33).**  Running the circuit `U` and
then measuring in the computational basis induces, for outcome `(x, y)`, the measurement operator
`U† |xy⟩⟨xy| U`; here written as the equal rank-one projector `|U†xy⟩⟨U†xy|` onto `U† |xy⟩`.  This
equals `bellMeasurement.op (x, y) = |β_xy⟩⟨β_xy|` (`bellMeasurement_op`), since `U† |xy⟩ = |β_xy⟩`
(`bellMeasurementCircuit_op_adjoint_qubitBasis`).  So the CNOT+H circuit realises the Bell-basis
measurement, with the four Bell projectors as its measurement operators. -/
theorem bellMeasurement_op_eq_bellMeasurementCircuit_conj (x y : Fin 2) :
    bellMeasurement.op (x, y)
      = ((InnerProductSpace.rankOne ℂ ((ContinuousLinearMap.adjoint bellMeasurementCircuit.op)
            ((qubitBasis x).vec ⊗ₜ[ℂ] (qubitBasis y).vec)))
          ((ContinuousLinearMap.adjoint bellMeasurementCircuit.op)
            ((qubitBasis x).vec ⊗ₜ[ℂ] (qubitBasis y).vec))) := by
  simp only [bellMeasurementCircuit_op_adjoint_qubitBasis, bellMeasurement_op, bellState_vec]

end

end AxQM
