/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EigenspaceCollapse
import AxQM.Postulates.API.KitaevPhaseEstimation
import AxQM.Postulates.API.MeasurementOperation

/-!
# AxQM.Postulates.API — the ancilla measurement of the Hadamard-controlled-`U` circuit

The step Nielsen & Chuang's **Exercise 4.34** ("Measuring an operator") asks for beyond the circuit
action of `MeasureObservable.lean`: *running the ancilla measurement as an explicit `Measurement`*
and showing it reproduces the projective measurement of the observable `U`.  The circuit
`measureObservableCircuit U = (H ⊗ 1)·C(U)·(H ⊗ 1)` sends `|0⟩ ⊗ |ψ⟩` to the correlated state
`|0⟩ ⊗ P₊|ψ⟩ + |1⟩ ⊗ P₋|ψ⟩`; here we *measure the ancilla in the computational basis* — the
measurement `controlMeasurement`, `Mᵢ = |i⟩⟨i| ⊗ 1` — and prove that outcome `i ∈ {0, 1}` occurs
with exactly the Born probability of the sign measurement of `U` and collapses the target onto the
corresponding `±1` eigenvector.

```
|0⟩ ─── H ───•─── H ───⊙   (measure ancilla → this file)
             │
|ψ⟩ ─────────U──────────
```

## What is formalised

The **general control-measurement engine on an un-normalised two-branch state** (generalising the
balanced, unit-branch `…_invSqrt2_branch` engine of `OneBitTeleportation`), for arbitrary target
branch vectors `a : Fin 2 → S`:

* `controlMeasurement_op_add_branch` — the projector `Mₘ = |m⟩⟨m| ⊗ 1` extracts the `m`-branch of
  `|0⟩ ⊗ a₀ + |1⟩ ⊗ a₁`, giving `|m⟩ ⊗ aₘ`.
* `controlMeasurement_bornProb_add_branch` — the Born probability of outcome `m` is `‖aₘ‖²` (the
  squared norm of the branch, with no `½` because the branches are *not* normalised).
* `controlMeasurement_postMeasurement_add_branch` — obtaining outcome `m` collapses the joint state
  to the product `|m⟩ ⊗ (aₘ / ‖aₘ‖)`: the ancilla flags `m` and the target renormalises its branch.

The **specialisation to Exercise 4.34** (`aᵢ = Mᵢ|ψ⟩` the sign-measurement operators of `U`):

* `measureObservableCircuit_controlMeasurement_bornProb` — **the statistics of `U`.** Measuring the
  ancilla after the circuit gives outcome `i` with exactly the Born probability of the projective
  sign measurement `Observable.signMeasurement` of `U`:
  `controlMeasurement.bornProb (circuit|0⟩⊗ψ) i = (signMeasurement U).bornProb ψ i`.  This is the
  precise sense in which reading the ancilla *is* the measurement of the observable `U`.
* `measureObservableCircuit_controlMeasurement_postMeasurement_zero` /
  `…_postMeasurement_one` — **the post-measurement states of `U`.** Outcome `0` collapses the joint
  state to `|0⟩ ⊗ postMeasPlus`, outcome `1` to `|1⟩ ⊗ postMeasMinus`; by
  `Observable.postMeasPlus_hasEigenstate` / `postMeasMinus_hasEigenstate` these targets are genuine
  `+1` / `−1` eigenvectors of `U`.  This is the exercise's "leaving a post-measurement state which
  is the corresponding eigenvector."

## Design notes

* **From the circuit action to the measurement.**  `MeasureObservable.lean` proved only the
  *pre-measurement* correlated state and tied its branches to the sign-measurement
  operators; the physical reading "measuring the ancilla realises the sign measurement of `U`" was
  left as an interpretation.  This file discharges that reading as Lean theorems by running the
  ancilla measurement `controlMeasurement` (the same measurement as in Kitaev's Problem 5.3 and
  Exercise 4.35).
* **The engine is un-normalised.**  Exercise 4.34's two branches are `P₊|ψ⟩` and `P₋|ψ⟩`, whose
  norms `‖P₊|ψ⟩‖`, `‖P₋|ψ⟩‖` differ (they *are* the Born weights) and do not carry the `(√2)⁻¹` of
  the balanced teleportation branches, so the `…_invSqrt2_branch` engine does not apply; the
  `…_add_branch` engine here is the general version, and specialises back to `invSqrt2` when the
  branches are equal unit vectors.
* The deterministic outcomes on a `±1` eigenstate input, in terms of `Measurement.bornProb` and
  `postMeasurement`, are stated in `AxQM/NC/Ch4/Exercise4_34.lean`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The control-measurement engine on an un-normalised two-branch state -/

/-- **Control measurement on a two-branch state (operator action).**  The control projector
`Mₘ = |m⟩⟨m| ⊗ 1` extracts the `m`-branch of `|0⟩ ⊗ a₀ + |1⟩ ⊗ a₁`, giving `|m⟩ ⊗ aₘ`; the
orthogonality `⟨m|j⟩ = δₘⱼ` kills the other branch.  The un-normalised generalisation of
`controlMeasurement_op_invSqrt2_branch` (arbitrary branch vectors `a : Fin 2 → S`, no `(√2)⁻¹`
prefactor and no normalisation of the branches).  Stated at the raw tensor head
`qubit.space ⊗[ℂ] S.space` (via the `mapL` form `controlMeasurement_op`). -/
theorem controlMeasurement_op_add_branch (a : Fin 2 → S.space) (m : Fin 2) :
    (controlMeasurement S).op m ((qubitBasis 0).vec ⊗ₜ[ℂ] a 0 + (qubitBasis 1).vec ⊗ₜ[ℂ] a 1)
      = ((qubitBasis m).vec ⊗ₜ[ℂ] a m : qubit.space ⊗[ℂ] S.space) := by
  rw [controlMeasurement_op]
  change (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis m).vec (qubitBasis m).vec)
        (1 : S.space →L[ℂ] S.space))
      ((qubitBasis 0).vec ⊗ₜ[ℂ] a 0 + (qubitBasis 1).vec ⊗ₜ[ℂ] a 1) = _
  rw [map_add, TensorProduct.mapL_tmul, TensorProduct.mapL_tmul, one_apply_eq_self,
    one_apply_eq_self]
  fin_cases m <;>
    simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue, InnerProductSpace.rankOne_apply,
      qubitBasis_inner_qubitBasis, ↓reduceIte, Fin.reduceEq, one_smul, zero_smul,
      TensorProduct.zero_tmul, add_zero, zero_add]

/-- **Born probability of the control measurement on a two-branch state: `‖aₘ‖²`.**  For a pure
state `Φ` with `|Φ⟩ = |0⟩ ⊗ a₀ + |1⟩ ⊗ a₁`, control outcome `m` occurs with probability
`‖Mₘ|Φ⟩‖² = ‖|m⟩ ⊗ aₘ‖² = ‖aₘ‖²` (the ancilla is a unit vector).  The un-normalised generalisation
of `controlMeasurement_bornProb_invSqrt2_branch` — here the branch norms are the Born weights
themselves, not a uniform `½`. -/
theorem controlMeasurement_bornProb_add_branch (Φ : PureState (qubit ⊗ S)) (a : Fin 2 → S.space)
    (h : Φ.vec = (qubitBasis 0).vec ⊗ₜ[ℂ] a 0 + (qubitBasis 1).vec ⊗ₜ[ℂ] a 1) (m : Fin 2) :
    (controlMeasurement S).bornProb Φ.toState m = ‖a m‖ ^ 2 := by
  rw [Measurement.bornProb_toState_eq_normSq, h, controlMeasurement_op_add_branch]
  change ‖((qubitBasis m).vec ⊗ₜ[ℂ] a m : qubit.space ⊗[ℂ] S.space)‖ ^ 2 = ‖a m‖ ^ 2
  rw [TensorProduct.norm_tmul, (qubitBasis m).normalized, one_mul]

/-- **Collapse of a pure state onto the projected direction.**  For any measurement `meas` on a pure
state `ψ`, if the (un-normalised) projected vector `Mᵢ|ψ⟩` points along a unit vector `|φ⟩` (i.e.
`Mᵢ|ψ⟩ = c • |φ⟩` for some `c ≠ 0`), then obtaining outcome `i` collapses the state to `|φ⟩⟨φ|`: the
post-measurement state is the direction of the projected vector, independent of length and phase.
The pure-state form of Postulate 4 (state update), reusable infrastructure that keeps the tensor
algebra of a composite branch out of the operator/rank-one computation.  Proved from
`postMeasurement_op_eq_bornProb_smul_opElement` and `bornProb_toState_eq_normSq`, with
`c · conj c = ‖c‖²` cancelling the Born normalisation. -/
theorem Measurement.postMeasurement_toState_of_op_eq_smul {ι : Type*} [Fintype ι]
    (meas : Measurement ι S) (ψ φ : PureState S) (i : ι) {c : ℂ} (hc : c ≠ 0)
    (hproj : meas.op i ψ.vec = c • φ.vec) (hp : meas.bornProb ψ.toState i ≠ 0) :
    meas.postMeasurement ψ.toState i hp = φ.toState := by
  have hpost : ContinuousLinearMap.postOp meas.op ψ.toState.op i
      = InnerProductSpace.rankOne ℂ (meas.op i ψ.vec) (meas.op i ψ.vec) := by
    simp only [ContinuousLinearMap.postOp, PureState.toState_op, InnerProductSpace.rankOne_comp,
      ContinuousLinearMap.adjoint_adjoint, InnerProductSpace.comp_rankOne]
  have hc2 : (↑(‖c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  apply State.ext
  rw [Measurement.postMeasurement_op_eq_bornProb_smul_opElement,
    Measurement.bornProb_toState_eq_normSq, Measurement.opElement_eq_postOp, hpost, hproj,
    PureState.toState_op, InnerProductSpace.rankOne_smul_smul_self, norm_smul, φ.normalized,
    mul_one, smul_smul]
  rw [show (↑(‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ * (c * starRingEnd ℂ c) = 1 by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, inv_mul_cancel₀ hc2], one_smul]

/-- **Post-measurement state of the control measurement on a two-branch state.**
For a pure `Φ` with `|Φ⟩ = |0⟩ ⊗ a₀ + |1⟩ ⊗ a₁` and `aₘ ≠ 0`, obtaining control outcome `m`
collapses the joint state to the product `|m⟩ ⊗ (aₘ / ‖aₘ‖)`: the ancilla flags `m`, and the
projected branch `Mₘ|Φ⟩ = |m⟩ ⊗ aₘ` renormalises by its Born weight `‖aₘ‖²`.  The un-normalised
generalisation of `controlMeasurement_postMeasurement_invSqrt2_branch`, obtained from the pure-state
collapse `Measurement.postMeasurement_toState_of_op_eq_smul` with `c = ‖aₘ‖`. -/
theorem controlMeasurement_postMeasurement_add_branch (Φ : PureState (qubit ⊗ S))
    (a : Fin 2 → S.space)
    (h : Φ.vec = (qubitBasis 0).vec ⊗ₜ[ℂ] a 0 + (qubitBasis 1).vec ⊗ₜ[ℂ] a 1) (m : Fin 2)
    (hne : a m ≠ 0) (hp : (controlMeasurement S).bornProb Φ.toState m ≠ 0) :
    (controlMeasurement S).postMeasurement Φ.toState m hp
      = ((qubitBasis m).tmul (PureState.normalize (a m) hne)).toState := by
  refine Measurement.postMeasurement_toState_of_op_eq_smul _ Φ _ m
    (c := (↑‖a m‖ : ℂ)) (by exact_mod_cast norm_ne_zero_iff.mpr hne) ?_ hp
  rw [h, controlMeasurement_op_add_branch, PureState.tmul_vec, PureState.normalize_vec]
  -- Both `•` sit at the composite `(qubit ⊗ S).space` head, where the raw-tensor `smul` lemmas do
  -- not fire; bridge the whole vector equation to the raw `qubit.space ⊗[ℂ] S.space` head (defeq),
  -- then cancel `‖aₘ‖ · ‖aₘ‖⁻¹ = 1` inside the branch factor.
  change ((qubitBasis m).vec ⊗ₜ[ℂ] a m : qubit.space ⊗[ℂ] S.space)
      = (‖a m‖ : ℂ) • ((qubitBasis m).vec ⊗ₜ[ℂ] ((‖a m‖ : ℂ)⁻¹ • a m) : qubit.space ⊗[ℂ] S.space)
  rw [← TensorProduct.tmul_smul, smul_smul,
    mul_inv_cancel₀ (show (‖a m‖ : ℂ) ≠ 0 by exact_mod_cast norm_ne_zero_iff.mpr hne), one_smul]

/-! ### Exercise 4.34: the ancilla measurement realises the measurement of `U` -/

/-- **The statistics of the observable `U`.**  Measuring the ancilla of the Hadamard-controlled-`U`
circuit in the computational basis, on input `|0⟩ ⊗ |ψ⟩`, gives outcome `i ∈ {0, 1}` with exactly
the Born probability of the projective sign measurement `Observable.signMeasurement` of `U`:
`controlMeasurement.bornProb (circuit |0⟩⊗ψ) i = (signMeasurement U).bornProb ψ i`.

Reading the ancilla in the computational basis (with `0 ↦ +1`, `1 ↦ −1`) therefore reproduces the
outcome statistics of the measurement of the observable `U` — the exercise's "a measurement result
indicating one of the two eigenvalues."  Proved by applying the branch-Born engine with the branches
`aᵢ = Mᵢ|ψ⟩` (the sign-measurement operators, from the circuit action `…_signMeasurement`) and
recognising `‖Mᵢ|ψ⟩‖²` as the pure-state Born rule for `signMeasurement`. -/
theorem measureObservableCircuit_controlMeasurement_bornProb (U : Evolution S)
    (hsa : IsSelfAdjoint U.op) (ψ : PureState S) (i : Fin 2) :
    (controlMeasurement S).bornProb
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0).tmul ψ)).toState i
      = ((U.toObservable hsa).signMeasurement (U.toObservable_op_mul_self hsa)).bornProb ψ.toState
          i := by
  rw [controlMeasurement_bornProb_add_branch _
      (fun j => ((U.toObservable hsa).signMeasurement (U.toObservable_op_mul_self hsa)).op j ψ.vec)
      (by rw [Evolution.evolvePure_vec, PureState.tmul_vec,
        measureObservableCircuit_op_qubitBasisZero_tmul_signMeasurement]) i,
    Measurement.bornProb_toState_eq_normSq]

/-- **The post-measurement state of `U`, outcome `0` (`+1`).**  Measuring the ancilla of the
Hadamard-controlled-`U` circuit and obtaining outcome `0` collapses the joint state to
`|0⟩ ⊗ postMeasPlus`: the ancilla flags `0` (indicating the eigenvalue `+1`) and the target
collapses to the normalised `+1` post-measurement state `P₊|ψ⟩ / ‖P₊|ψ⟩‖`, which is a genuine `+1`
eigenvector of `U` (`Observable.postMeasPlus_hasEigenstate`).  This is the exercise's "leaving a
post-measurement state which is the corresponding eigenvector", `+1` case. -/
theorem measureObservableCircuit_controlMeasurement_postMeasurement_zero (U : Evolution S)
    (hsa : IsSelfAdjoint U.op) (ψ : PureState S) (hne : (U.toObservable hsa).projPlus ψ.vec ≠ 0)
    (hp : (controlMeasurement S).bornProb
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0).tmul ψ)).toState 0 ≠ 0) :
    (controlMeasurement S).postMeasurement
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0).tmul ψ)).toState 0 hp
      = ((qubitBasis 0).tmul ((U.toObservable hsa).postMeasPlus ψ hne)).toState := by
  rw [controlMeasurement_postMeasurement_add_branch _
      ![(U.toObservable hsa).projPlus ψ.vec, (U.toObservable hsa).projMinus ψ.vec]
      (by rw [Evolution.evolvePure_vec, PureState.tmul_vec,
            measureObservableCircuit_op_qubitBasisZero_tmul_projMeas U hsa]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          rfl) 0
      (by simpa only [Matrix.cons_val_zero] using hne)]
  simp only [Matrix.cons_val_zero]
  rfl

/-- **The post-measurement state of `U`, outcome `1` (`−1`).**  Measuring the ancilla of the
Hadamard-controlled-`U` circuit and obtaining outcome `1` collapses the joint state to
`|1⟩ ⊗ postMeasMinus`: the ancilla flags `1` (indicating the eigenvalue `−1`) and the target
collapses to the normalised `−1` post-measurement state `P₋|ψ⟩ / ‖P₋|ψ⟩‖`, a genuine `−1`
eigenvector of `U` (`Observable.postMeasMinus_hasEigenstate`).  This is the exercise's "leaving a
post-measurement state which is the corresponding eigenvector", `−1` case. -/
theorem measureObservableCircuit_controlMeasurement_postMeasurement_one (U : Evolution S)
    (hsa : IsSelfAdjoint U.op) (ψ : PureState S) (hne : (U.toObservable hsa).projMinus ψ.vec ≠ 0)
    (hp : (controlMeasurement S).bornProb
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0).tmul ψ)).toState 1 ≠ 0) :
    (controlMeasurement S).postMeasurement
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0).tmul ψ)).toState 1 hp
      = ((qubitBasis 1).tmul ((U.toObservable hsa).postMeasMinus ψ hne)).toState := by
  rw [controlMeasurement_postMeasurement_add_branch _
      ![(U.toObservable hsa).projPlus ψ.vec, (U.toObservable hsa).projMinus ψ.vec]
      (by rw [Evolution.evolvePure_vec, PureState.tmul_vec,
            measureObservableCircuit_op_qubitBasisZero_tmul_projMeas U hsa]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          rfl) 1
      (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using hne)]
  simp only [Matrix.cons_val_one]
  rfl

end AxQM
