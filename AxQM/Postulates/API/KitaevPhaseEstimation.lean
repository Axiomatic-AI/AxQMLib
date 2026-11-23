/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasureObservable
import AxQM.Postulates.API.ControlMeasurementCommute

/-!
# AxQM.Postulates.API — Kitaev's phase-estimation circuit

The computation behind Nielsen & Chuang's **Problem 5.3 (Kitaev's algorithm)**: the
Hadamard-controlled-`U` circuit `(H ⊗ 1) · C(U) · (H ⊗ 1)` (`measureObservableCircuit`, generalised
to an arbitrary target register `S` in `MeasureObservable.lean`) run on `|0⟩ ⊗ |u⟩` with `|u⟩` an
eigenstate of `U`, and the Born-rule statistics of the ancilla (control) measurement.

```
|0⟩ ─── H ───•─── H ───⊙   (measure the control)
             │
|u⟩ ─/───────U──────────   |u⟩  (eigenstate, unaffected)
```

## What is formalised

* `Measurement.bornProb_toState_eq_normSq` — the **Born rule on a pure state** for *any*
  measurement: `p(i) = ‖Mᵢ|ψ⟩‖²` (from `Mᵢ ρ Mᵢ† = |Mᵢψ⟩⟨Mᵢψ|` and `tr|v⟩⟨v| = ‖v‖²`). General
  reusable infrastructure.
* `Evolution.HasEigenstate.pow` — an eigenstate of `U` (eigenvalue `μ`) is an eigenstate of `Uᵏ`
  (eigenvalue `μᵏ`); this is what allows iterating the circuit with `U → Uᵏ`.
* `measureObservableCircuit_op_qubitBasisZero_tmul_smul` — the **phase kickback**: on an eigenstate
  input `U|u⟩ = μ|u⟩` the circuit output *factorises* as `(½(1+μ) |0⟩ + ½(1−μ) |1⟩) ⊗ |u⟩`, the
  target register left in the intact `|u⟩` — the precise sense in which `|u⟩` is *unaffected and
  reusable*.
* `measureObservableCircuit_controlMeasurement_bornProb_zero_smul` — the **outcome-0 probability**
  `‖½(1+μ)‖²` of measuring the control in the computational basis after the circuit, on an
  eigenstate input. With `μ = e^{2πiφ}` this is `cos²(πφ)` (the pure-phase arithmetic is discharged
  in `AxQM/NC/Ch5/Problem5_3.lean`).

The Born-probability statements `p = cos²(πφ)` and its `Uᵏ` iteration are in
`AxQM/NC/Ch5/Problem5_3.lean`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The Born rule on a pure state (general) -/

/-- **Born rule on a pure state.** For any measurement `m`, the probability of outcome `i` on a pure
state `|ψ⟩` is the squared norm of the collapsed (unnormalised) vector: `p(i) = ‖Mᵢ|ψ⟩‖²`. Holds for
*every* measurement (no projectivity/self-adjointness needed): `Mᵢ ρ Mᵢ† = |Mᵢψ⟩⟨Mᵢψ|` for
`ρ = |ψ⟩⟨ψ|`, and `tr|v⟩⟨v| = ⟨v, v⟩ = ‖v‖²`. General reusable infrastructure. -/
theorem Measurement.bornProb_toState_eq_normSq {ι : Type*} [Fintype ι] (m : Measurement ι S)
    (ψ : PureState S) (i : ι) : m.bornProb ψ.toState i = ‖m.op i ψ.vec‖ ^ 2 := by
  rw [Measurement.bornProb_eq_re_trace_postOp]
  have hpost : ContinuousLinearMap.postOp m.op ψ.toState.op i
      = InnerProductSpace.rankOne ℂ (m.op i ψ.vec) (m.op i ψ.vec) := by
    simp only [ContinuousLinearMap.postOp, PureState.toState_op, InnerProductSpace.rankOne_comp,
      ContinuousLinearMap.adjoint_adjoint, InnerProductSpace.comp_rankOne]
  rw [hpost, InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq]

/-! ### Eigenstates of a gate power -/

/-- **An eigenstate of `U` is an eigenstate of `Uᵏ`.** If `U|ψ⟩ = μ|ψ⟩` then `Uᵏ|ψ⟩ = μᵏ|ψ⟩`, for
the gate monoid power `Uᵏ` (`Evolution` is a monoid under composition). The substance for iterating
Kitaev's circuit: replacing `U` by `Uᵏ` multiplies the eigenphase by `k`. -/
theorem Evolution.HasEigenstate.pow {U : Evolution S} {μ : ℂ} {ψ : PureState S}
    (h : U.HasEigenstate μ ψ) (k : ℕ) : (U ^ k).HasEigenstate (μ ^ k) ψ := by
  simp only [Evolution.HasEigenstate] at h ⊢
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, Evolution.one_def, Evolution.id_op, one_apply_eq_self,
      one_smul]
  | succ n ih =>
    rw [pow_succ, pow_succ, Evolution.mul_def, Evolution.comp_op, ContinuousLinearMap.comp_apply,
      h, map_smul, ih, smul_smul, mul_comm]

/-! ### The circuit on an eigenstate: phase kickback and factorisation -/

/-- **Phase kickback / eigenstate factorisation.** On an eigenstate input `U|u⟩ = μ|u⟩`, the
Hadamard-controlled-`U` circuit sends `|0⟩ ⊗ |u⟩` to the *product* state
`(½(1+μ) |0⟩ + ½(1−μ) |1⟩) ⊗ |u⟩`: the target register stays factored out and unchanged in `|u⟩`
(so it may be reused), while the eigenphase `μ` appears as a relative phase on the control.

Specialisation of the general circuit action `measureObservableCircuit_op_qubitBasisZero_tmul`
(`|0⟩ ⊗ x ↦ |0⟩ ⊗ ½(x+Ux) + |1⟩ ⊗ ½(x−Ux)`) at `Ux = μx`, collecting the two branches onto the
common right factor `x`. -/
theorem measureObservableCircuit_op_qubitBasisZero_tmul_smul (U : Evolution S) {x : S.space}
    {μ : ℂ} (hx : U.op x = μ • x) :
    (measureObservableCircuit U).op ((qubitBasis 0).vec ⊗ₜ[ℂ] x)
      = (((2⁻¹ : ℂ) * (1 + μ)) • (qubitBasis 0).vec
          + ((2⁻¹ : ℂ) * (1 - μ)) • (qubitBasis 1).vec) ⊗ₜ[ℂ] x := by
  rw [measureObservableCircuit_op_qubitBasisZero_tmul, hx, TensorProduct.add_tmul]
  congr 1 <;> (rw [← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul]; congr 1; module)

/-! ### Applying the control measurement to a product state -/

/-- The control-measurement operator `Mᵢ = |i⟩⟨i| ⊗ 1` acting on a product `a ⊗ b` gives
`(|i⟩⟨i| a) ⊗ b`: the projector `|i⟩⟨i|` hits the control factor, the target factor is untouched.
Restated at the raw tensor head (`change`, as in the sibling `controlledUnitary` lemmas) so
`TensorProduct.mapL_tmul` fires. -/
theorem controlMeasurement_op_tmul (i : Fin 2) (a : qubit.space) (b : S.space) :
    (controlMeasurement S).op i (a ⊗ₜ[ℂ] b)
      = (InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec) a ⊗ₜ[ℂ] b := by
  rw [controlMeasurement_op]
  change (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec)
      (1 : S.space →L[ℂ] S.space)) (a ⊗ₜ[ℂ] b) = _
  rw [TensorProduct.mapL_tmul, one_apply_eq_self]

/-! ### The control-measurement Born probability on an eigenstate -/

/-- **Outcome-`0` probability of the control measurement.** After the circuit, measuring the control
qubit in the computational basis yields `0` with probability `‖½(1+μ)‖²`, on an eigenstate input
`U|u⟩ = μ|u⟩`. Combines the phase-kickback factorisation
(`measureObservableCircuit_op_qubitBasisZero_tmul_smul`) — whose `|0⟩`-amplitude is `½(1+μ)` and
whose right factor `|u⟩` is normalised — with the pure-state Born rule
(`Measurement.bornProb_toState_eq_normSq`): the control projector `|0⟩⟨0| ⊗ 1` extracts the
`|0⟩`-amplitude, and `‖½(1+μ) • (|0⟩ ⊗ |u⟩)‖² = ‖½(1+μ)‖²`. -/
theorem measureObservableCircuit_controlMeasurement_bornProb_zero_smul (U : Evolution S)
    (u : PureState S) {μ : ℂ} (hu : U.op u.vec = μ • u.vec) :
    (controlMeasurement S).bornProb
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0).tmul u)).toState 0
      = ‖(2⁻¹ : ℂ) * (1 + μ)‖ ^ 2 := by
  rw [Measurement.bornProb_toState_eq_normSq, Evolution.evolvePure_vec, PureState.tmul_vec,
    measureObservableCircuit_op_qubitBasisZero_tmul_smul U hu, controlMeasurement_op_tmul]
  rw [map_add, map_smul, map_smul, InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply,
    qubitBasis_inner_qubitBasis, qubitBasis_inner_qubitBasis]
  simp only [Fin.isValue, ite_true, Fin.reduceEq, ite_false, one_smul, zero_smul, smul_zero,
    add_zero]
  -- View the product state at the raw tensor head `qubit.space ⊗[ℂ] S.space`, where
  -- `TensorProduct.norm_tmul` fires (cf. `PureState.tmul`'s normalisation in `Composite.lean`).
  change ‖(((2⁻¹ * (1 + μ)) • (qubitBasis 0).vec) ⊗ₜ[ℂ] u.vec : qubit.space ⊗[ℂ] S.space)‖ ^ 2
      = ‖(2⁻¹ : ℂ) * (1 + μ)‖ ^ 2
  rw [TensorProduct.norm_tmul, norm_smul, (qubitBasis 0).normalized, u.normalized, mul_one, mul_one]

end AxQM
