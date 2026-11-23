/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasureObservableAncilla

/-!
# Nielsen & Chuang, Exercise 4.34 (Measuring an operator)

*(N&C p. 188.)*

Show a Hadamard-controlled-U circuit implements measurement of observable U.

`U` is regarded both as a gate (`Evolution qubit`, fed to
`controlledUnitary`) and — being Hermitian — as an observable (`Evolution.toObservable`). The
circuit `measureObservableCircuit U = (H ⊗ 1) · C(U) · (H ⊗ 1)` is a closed-system evolution
(Postulate 5), and "measuring `U`" is realised by measuring the ancilla (`controlMeasurement`) in
the computational basis after the circuit, read `0 ↦ +1`, `1 ↦ −1`.  This ancilla
measurement reproduces the sign measurement `Observable.signMeasurement` of `U` (N&C §2.2.5).

## The formalisation

The exercise's claim — "the circuit implements a measurement of `U`" — is captured by the following
declarations. The general statements (in terms of `Evolution.op`, `⊗ₜ`, the eigenprojectors
`(I ± U)/2`, `Observable.signMeasurement`) are in `AxQM/Postulates/API/`; the readings for
eigenstate inputs are in this file.

*Circuit and its unitary action* — `AxQM/Postulates/API/MeasureObservable.lean`:
`measureObservableCircuit`, the action `measureObservableCircuit_op_qubitBasisZero_tmul`
(`|0⟩ ⊗ x ↦ |0⟩ ⊗ P₊x + |1⟩ ⊗ P₋x`) with the `…_projMeas` / `…_signMeasurement` corollaries tying
the branches to the sign-measurement operators, and `Evolution.toObservable` (the Hermitian gate as
an observable).

*The ancilla measurement itself* — `AxQM/Postulates/API/MeasureObservableAncilla.lean`:
measuring the ancilla `controlMeasurement` after the circuit
- reproduces the **outcome statistics** of the sign measurement of `U`
  (`measureObservableCircuit_controlMeasurement_bornProb`: the Born probability of ancilla outcome
  `i` equals `(signMeasurement U).bornProb ψ i`), and
- **collapses the target onto the corresponding eigenvector**
  (`measureObservableCircuit_controlMeasurement_postMeasurement_zero` / `…_one`: outcome `i` leaves
  `|i⟩ ⊗ postMeas±`, a `±1` eigenstate of `U` by `Observable.postMeasPlus_hasEigenstate` /
  `postMeasMinus_hasEigenstate`).
This is exactly the exercise's "a measurement result indicating one of the two eigenvalues, and
leaving a post-measurement state which is the corresponding eigenvector."

*This file* states the deterministic readings for eigenstate inputs, using
`Evolution.evolvePure`, `Evolution.HasEigenstate`, `PureState.tmul`, `Measurement.bornProb`:

* `measureObservableCircuit_evolvePure_ketZero_tmul_of_hasEigenstate_one` /
  `…_neg_one` — the deterministic *unitary* action on a `±1` eigenstate input: the circuit sends
  `|0⟩ ⊗ |ψ⟩` to `|0⟩ ⊗ |ψ⟩` (resp. `|1⟩ ⊗ |ψ⟩`), leaving the target in the eigenvector `|ψ⟩`.
* `measureObservableCircuit_controlMeasurement_bornProb_of_hasEigenstate_one` /
  `…_neg_one` — the deterministic *measurement* reading: on a `±1` eigenstate the ancilla
  measurement yields the outcome flagging the eigenvalue with probability `1` (certainty).

## Design notes

* **Faithfulness.** The `±1` eigenvalues, Hermiticity and unitarity of the textbook's
  `U` are honoured: `U : Evolution qubit` is a genuine unitary gate, `Evolution.toObservable` is the
  observable view (needing `IsSelfAdjoint U.op`), and the eigenvalue hypothesis is the grounded
  `Evolution.HasEigenstate U (±1)` predicate. The general theorems quantify over *every* input
  `|ψ⟩` (not just eigenstates); the statistics and collapse are full equalities of
  `Measurement.bornProb` / `Measurement.postMeasurement`, not up-to-phase or on-a-subspace
  surrogates.
* **The ancilla measurement is run.** Beyond the pre-measurement correlated state, whose branches
  are tied to `signMeasurement`, the ancilla measurement `controlMeasurement`
  is run as an explicit `Measurement`, and its Born statistics and post-measurement collapse are
  proved to coincide with the sign measurement of `U` (in the API file above).
* **General versus eigenstate statements.** The general statistics/collapse statements (in terms of
  `Observable.projPlus`, `signMeasurement`, `PureState.vec`) are in `AxQM/Postulates/API/`; the
  eigenstate readings are here.
-/

open scoped TensorProduct InnerProductSpace

noncomputable section

namespace AxQM

variable {ψ : PureState qubit}

/-- **Nielsen & Chuang, Exercise 4.34 (the `+1` eigenstate case).** If the target input `|ψ⟩` is a
`+1` eigenstate of `U` (`U|ψ⟩ = |ψ⟩`), the Hadamard-controlled-`U` measurement circuit sends
`|0⟩ ⊗ |ψ⟩` to `|0⟩ ⊗ |ψ⟩`: the ancilla is measured `0` — indicating the eigenvalue `+1` — with
certainty, and the target is left in the corresponding eigenvector `|ψ⟩`.  Deterministic reading of
the general circuit action `measureObservableCircuit_op_qubitBasisZero_tmul`. -/
theorem measureObservableCircuit_evolvePure_ketZero_tmul_of_hasEigenstate_one (U : Evolution qubit)
    (h : U.HasEigenstate 1 ψ) :
    (measureObservableCircuit U).evolvePure ((qubitBasis 0) ⊗ ψ) = (qubitBasis 0) ⊗ ψ := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec]
  rw [measureObservableCircuit_op_qubitBasisZero_tmul]
  have hev : U.op ψ.vec = (1 : ℂ) • ψ.vec := h
  rw [hev]
  simp only [TensorProduct.tmul_smul, one_smul, sub_self, smul_zero, ← two_smul ℂ, smul_smul,
    TensorProduct.tmul_zero, add_zero]
  norm_num
  rfl

/-- **Nielsen & Chuang, Exercise 4.34 (the `−1` eigenstate case).** If the target input `|ψ⟩` is a
`−1` eigenstate of `U` (`U|ψ⟩ = −|ψ⟩`), the Hadamard-controlled-`U` measurement circuit sends
`|0⟩ ⊗ |ψ⟩` to `|1⟩ ⊗ |ψ⟩`: the ancilla is measured `1` — indicating the eigenvalue `−1` — with
certainty, and the target is left in the corresponding eigenvector `|ψ⟩`.  Deterministic reading of
the general circuit action `measureObservableCircuit_op_qubitBasisZero_tmul`. -/
theorem measureObservableCircuit_evolvePure_ketZero_tmul_of_hasEigenstate_neg_one
    (U : Evolution qubit) (h : U.HasEigenstate (-1) ψ) :
    (measureObservableCircuit U).evolvePure ((qubitBasis 0) ⊗ ψ) = (qubitBasis 1) ⊗ ψ := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec]
  rw [measureObservableCircuit_op_qubitBasisZero_tmul]
  have hev : U.op ψ.vec = (-1 : ℂ) • ψ.vec := h
  rw [hev]
  simp only [TensorProduct.tmul_smul, neg_one_smul, add_neg_cancel, smul_zero, sub_neg_eq_add,
    ← two_smul ℂ, smul_smul, TensorProduct.tmul_zero, zero_add]
  norm_num
  rfl

/-- **Nielsen & Chuang, Exercise 4.34 (measurement certainty, `+1` case).** If `|ψ⟩` is a `+1`
eigenstate of `U`, then measuring the ancilla in the computational basis after the circuit
(`controlMeasurement`) yields outcome `0` — indicating the eigenvalue `+1` — with probability `1`:
the outcome is certain, exactly as a measurement of the `±1` observable `U` must be on one of its
eigenstates.  This is the *measurement* (rather than merely unitary) reading of
`…_of_hasEigenstate_one`, stated with `Measurement.bornProb`.  The
general, arbitrary-input outcome statistics are
`measureObservableCircuit_controlMeasurement_bornProb` in
`AxQM/Postulates/API/MeasureObservableAncilla.lean`. -/
theorem measureObservableCircuit_controlMeasurement_bornProb_of_hasEigenstate_one
    (U : Evolution qubit) (h : U.HasEigenstate 1 ψ) :
    (controlMeasurement qubit).bornProb
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0) ⊗ ψ)).toState 0 = 1 := by
  rw [measureObservableCircuit_evolvePure_ketZero_tmul_of_hasEigenstate_one U h,
    Measurement.bornProb_toState_eq_normSq, PureState.tmul_vec, controlMeasurement_op_tmul,
    InnerProductSpace.rankOne_apply, qubitBasis_inner_qubitBasis]
  simp only [↓reduceIte, one_smul]
  change ‖((qubitBasis 0).vec ⊗ₜ[ℂ] ψ.vec : qubit.space ⊗[ℂ] qubit.space)‖ ^ 2 = 1
  rw [TensorProduct.norm_tmul, (qubitBasis 0).normalized, ψ.normalized, mul_one, one_pow]

/-- **Nielsen & Chuang, Exercise 4.34 (measurement certainty, `−1` case).** If `|ψ⟩` is a `−1`
eigenstate of `U`, then measuring the ancilla after the circuit yields outcome `1` — indicating the
eigenvalue `−1` — with probability `1`: the outcome is certain.  The `−1` sibling of
`…_bornProb_of_hasEigenstate_one`; together they say the circuit reads off the eigenvalue of `U`
deterministically on an eigenstate. -/
theorem measureObservableCircuit_controlMeasurement_bornProb_of_hasEigenstate_neg_one
    (U : Evolution qubit) (h : U.HasEigenstate (-1) ψ) :
    (controlMeasurement qubit).bornProb
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0) ⊗ ψ)).toState 1 = 1 := by
  rw [measureObservableCircuit_evolvePure_ketZero_tmul_of_hasEigenstate_neg_one U h,
    Measurement.bornProb_toState_eq_normSq, PureState.tmul_vec, controlMeasurement_op_tmul,
    InnerProductSpace.rankOne_apply, qubitBasis_inner_qubitBasis]
  simp only [↓reduceIte, one_smul]
  change ‖((qubitBasis 1).vec ⊗ₜ[ℂ] ψ.vec : qubit.space ⊗[ℂ] qubit.space)‖ ^ 2 = 1
  rw [TensorProduct.norm_tmul, (qubitBasis 1).normalized, ψ.normalized, mul_one, one_pow]

end AxQM
