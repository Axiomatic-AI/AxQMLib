/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledUnitary
import AxQM.Postulates.API.CompositeMeasurement

/-!
# AxQM — measuring the control commutes with a controlled gate (N&C Exercise 4.35)

The control-qubit instance of the deferred-measurement engine
(`AxQM/Postulates/API/DeferredMeasurement.lean`): the concrete measurement, gate family,
and — the crux — the operator commutation that N&C's Exercise 4.35 turns on.

* `controlMeasurement S` — the projective **measurement of the control qubit** in the computational
  basis, on `qubit ⊗ S`: the two-qubit-basis measurement `Mᵢ = |i⟩⟨i|` of the left factor lifted by
  `Measurement.onLeft`, so `Mᵢ = |i⟩⟨i| ⊗ 1` on `qubit ⊗ S` (`controlMeasurement_op`).
* `classicalControl U` — the **classically-controlled gate** applied on the branch of outcome `i`:
  the identity on outcome `0` and `1 ⊗ U` (`Evolution.onRight U qubit`) on outcome `1`. This is the
  gate the rightmost circuit of Exercise 4.35 applies conditioned on the measured control bit.
* `controlMeasurement_op_comp_controlledUnitary` — **the commutation** `Mᵢ · C(U) = Wᵢ · Mᵢ`, the
  hypothesis the deferred-measurement engine consumes. With control `|0⟩` both sides project onto
  `|0⟩` (`W₀ = 1`); with control `|1⟩` both sides give `|1⟩⟨1| ⊗ U` (`W₁ = 1 ⊗ U`). This is why
  measuring the control commutes with `C(U)`.

The two physical readings — the measurement statistics and the post-measurement state agree between
"apply `C(U)` then measure the control" and "measure the control then apply the classical gate" —
are the theorems in `AxQM/NC/Ch4/Exercise4_35.lean`, obtained by
feeding this commutation to the engine.

## Proof of the commutation

Both `Mᵢ = |i⟩⟨i| ⊗ 1` and `C(U) = |0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ U` are block operators, so the composite is
the block algebra of `controlledUnitary` (restated at the raw tensor head via `change`, then
`TensorProduct.mapL_comp` over the sum): the projector products `|i⟩⟨i| |j⟩⟨j| = δᵢⱼ |i⟩⟨i|`
collapse the diagonal, leaving `M₀ · C(U) = |0⟩⟨0| ⊗ 1 = M₀` and
`M₁ · C(U) = |1⟩⟨1| ⊗ U = (1 ⊗ U) · M₁`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The projective **measurement of the control qubit** in the computational basis, on `qubit ⊗ S`:
the two-outcome basis measurement `Mᵢ = |i⟩⟨i|` of the qubit (`Measurement.ofOrthonormalBasis` of
the standard basis) lifted to the *left* factor by `Measurement.onLeft`, so its operators are
`Mᵢ = |i⟩⟨i| ⊗ 1` (`controlMeasurement_op`). This is the measurement N&C's Exercise 4.35 performs on
the control wire. -/
def controlMeasurement (S : QSystem) : Measurement (Fin 2) (qubit ⊗ S) :=
  (Measurement.ofOrthonormalBasis (EuclideanSpace.basisFun (Fin 2) ℂ)).onLeft S

/-- The operators of `controlMeasurement` are the computational-basis control projectors
`Mᵢ = |i⟩⟨i| ⊗ 1` on `qubit ⊗ S`. Rewrites the standard-basis vectors `EuclideanSpace.single i 1`
to the qubit computational-basis states `(qubitBasis i).vec`. -/
theorem controlMeasurement_op (S : QSystem) (i : Fin 2) :
    (controlMeasurement S).op i
      = TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec)
          (1 : S.space →L[ℂ] S.space) := by
  rw [controlMeasurement, Measurement.onLeft_op]
  -- `(ofOrthonormalBasis b).op i = rankOne ℂ (b i) (b i)` (`ofOrthonormalBasis_op`, itself `rfl`)
  -- and `basisFun i = single i 1 = (qubitBasis i).vec` are both matched up to the
  -- `qubit.space`/`EuclideanSpace` FunLike-instance defeq (which `rw`/`simp` key on but
  -- `exact` tolerates) via `congrArg`.
  exact congrArg
    (fun v => TensorProduct.mapL (InnerProductSpace.rankOne ℂ v v) (1 : S.space →L[ℂ] S.space))
    ((EuclideanSpace.basisFun_apply (Fin 2) ℂ i).trans (qubitBasis_vec i).symm)

/-- The **classically-controlled gate** applied on the branch of measurement outcome `i`: the
identity for `i = 0` and `1 ⊗ U` (`Evolution.onRight U qubit`, i.e. `U` on the target) for `i = 1`.
This is the gate `Uᶜᵒⁿᵗʳᵒˡ` conditioned on the measured control bit in the rightmost circuit of
N&C Exercise 4.35. -/
def classicalControl (U : Evolution S) : Fin 2 → Evolution (qubit ⊗ S) :=
  ![Evolution.id, Evolution.onRight U qubit]

@[simp]
theorem classicalControl_zero (U : Evolution S) : classicalControl U 0 = Evolution.id := rfl

@[simp]
theorem classicalControl_one (U : Evolution S) :
    classicalControl U 1 = Evolution.onRight U qubit := rfl

/-- **The commutation of Exercise 4.35** `Mᵢ · C(U) = Wᵢ · Mᵢ`: composing the control-projector
`Mᵢ = |i⟩⟨i| ⊗ 1` after the controlled-`U` gate equals the classical-control gate `Wᵢ` after `Mᵢ`.
For control `|0⟩`, `M₀ · C(U) = |0⟩⟨0| ⊗ 1 = 1 · M₀` (nothing is applied); for control `|1⟩`,
`M₁ · C(U) = |1⟩⟨1| ⊗ U = (1 ⊗ U) · M₁` (`U` on the target). This is the hypothesis fed to the
deferred-measurement engine (`Measurement.postOp_evolve_of_comm` and its corollaries) to prove that
measuring the control commutes with `C(U)`. -/
theorem controlMeasurement_op_comp_controlledUnitary (U : Evolution S) (i : Fin 2) :
    ((controlMeasurement S).op i).comp (controlledUnitary U).op
      = (classicalControl U i).op.comp ((controlMeasurement S).op i) := by
  fin_cases i
  · simp only [Fin.mk_zero, Fin.isValue]
    rw [controlMeasurement_op, controlledUnitary_op, classicalControl_zero, Evolution.id_op]
    change (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
          (1 : S.space →L[ℂ] S.space)).comp
        (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec) 1
          + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
              U.op)
      = (1 : qubit.space ⊗[ℂ] S.space →L[ℂ] qubit.space ⊗[ℂ] S.space).comp
        (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec) 1)
    rw [ContinuousLinearMap.comp_add, ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp,
      rankOne_qubitBasis_comp_self 0, rankOne_qubitBasis_comp_orthogonal (by decide),
      TensorProduct.mapL_zero_left, add_zero]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_id]
  · simp only [Fin.mk_one, Fin.isValue]
    rw [controlMeasurement_op, controlledUnitary_op, classicalControl_one]
    change (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
          (1 : S.space →L[ℂ] S.space)).comp
        (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec) 1
          + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
              U.op)
      = (TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space) U.op).comp
        (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec) 1)
    rw [ContinuousLinearMap.comp_add, ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp,
      rankOne_qubitBasis_comp_orthogonal (by decide), rankOne_qubitBasis_comp_self 1,
      TensorProduct.mapL_zero_left, zero_add, ← TensorProduct.mapL_comp]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_id]

end AxQM
