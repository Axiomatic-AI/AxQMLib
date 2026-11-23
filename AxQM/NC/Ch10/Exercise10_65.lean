/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.OneBitTeleportation
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.RelativePhaseToffoli

/-!
# Nielsen & Chuang, Exercise 10.65 (measured swap into `|0⟩`)

*(N&C p. 487.)*

Show two given CNOT+measurement+classically-controlled circuits accomplish qubit swap into |0>.

The "task" is to move the unknown `|ψ⟩` onto the second qubit
(preparing the first in the measured basis state).  The reference circuit is the two-`CNOT` swap
`swapViaCnots`, which sends `|ψ⟩ ⊗ |0⟩ ↦ |0⟩ ⊗ |ψ⟩` deterministically.  Each measured-swap circuit
uses a *single* `CNOT`, a Hadamard, a computational-basis measurement of the control (first) qubit,
and a classically-controlled single-qubit correction on the target (second) qubit; it accomplishes
the same task in the sense that — for *either* measurement outcome `m ∈ {0,1}`, each occurring with
probability `½` — the corrected output is `|m⟩ ⊗ |ψ⟩`, i.e. the unknown `|ψ⟩` has been moved onto
the second qubit exactly as the reference swap does.

## The formalisation

The circuits and their branch decompositions / the control-measurement collapse are defined in
`AxQM/Postulates/API/OneBitTeleportation.lean` (`measuredSwapCircuit1`, `measuredSwapCircuit2`,
`controlMeasurement`, `classicalControl`, and the branch / born-probability / post-measurement
lemmas).  The statements of the exercise, in terms of `Evolution.evolvePure` / `Evolution.evolve` /
`Measurement.bornProb` / `Measurement.postMeasurement`, are:

* `swapViaCnots` / `swapViaCnots_evolvePure_ketZero` — the **reference two-`CNOT` swap**
  `reversedCNOT · CNOT` and its action `|ψ⟩ ⊗ |0⟩ ↦ |0⟩ ⊗ |ψ⟩`.
* `measuredSwapCircuit1_control_bornProb` / `measuredSwapCircuit2_control_bornProb` — measuring the
  control qubit after either measured-swap circuit gives outcome `m` with **probability `½`**.
* `measuredSwapCircuit1_corrected` / `measuredSwapCircuit2_corrected` — the **task is done**:
  after the circuit, the control measurement (outcome `m`), and the classically-controlled `Z^m`
  (circuit 1) / `X^m` (circuit 2) correction on the target, the state is `|m⟩ ⊗ |ψ⟩` — the unknown
  `|ψ⟩` moved onto the second qubit, for both outcomes.

## Design notes

* **Fidelity.**  Every statement holds for an *arbitrary* pure input `|ψ⟩` (the
  unknown qubit), each of the *two* circuits of the exercise is formalised, and the measurement is a
  genuine projective measurement of the control qubit (`controlMeasurement`) with its Born
  statistics (`bornProb = ½`) and post-measurement collapse (`postMeasurement`), followed by the
  classically-controlled correction (`classicalControl`).  No dimension is specialised and no phase
  is dropped: the corrected state is the exact product `|m⟩ ⊗ |ψ⟩`.
* **The correction is genuinely `C^m`.**  On outcome `0` nothing is applied (`classicalControl _ 0 =
  1`) and the target already holds `|ψ⟩`; on outcome `1` the correction `C` (`Z` for circuit 1, `X`
  for circuit 2) is applied to the target, which holds `C|ψ⟩`, and `C² = 1`
  (`pauliZGate_comp_pauliZGate` / `pauliXGate_comp_pauliXGate`) returns it to `|ψ⟩`.
* **Proof route.**  Each circuit's pre-measurement state is the branch decomposition
  `(√2)⁻¹(|0⟩ ⊗ |ψ⟩ + |1⟩ ⊗ C|ψ⟩)` (the `Postulates/API` bridge lemmas); feeding it to the
  control-measurement engine gives `bornProb = ½` and `postMeasurement = |m⟩ ⊗ C^m|ψ⟩`, and applying
  the classical correction (`toState_evolvePure` + `Evolution.onRight_evolvePure` + the `C²=1`
  involution) yields `|m⟩ ⊗ |ψ⟩`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The reference two-`CNOT` swap -/

/-- **The reference two-`CNOT` swap** of N&C Exercise 10.65: `reversedCNOT · CNOT`, a `CNOT`
(control = qubit 1) then the reversed `CNOT` (control = qubit 2).  Applied to `|ψ⟩ ⊗ |0⟩` it swaps
unknown `|ψ⟩` onto the second qubit (`swapViaCnots_evolvePure_ketZero`) — the "task" the measured
circuits must reproduce. -/
def swapViaCnots : Evolution (qubit ⊗ qubit) :=
  reversedCnotGate.comp cnotGate

/-- **The reference two-`CNOT` swap accomplishes the task:** `reversedCNOT · CNOT · (|ψ⟩ ⊗ |0⟩) =
|0⟩ ⊗ |ψ⟩`.  `CNOT` copies `|ψ⟩ = a|0⟩ + b|1⟩` into `a|00⟩ + b|11⟩`; the reversed `CNOT` then
uncopies the control, leaving `a|00⟩ + b|01⟩ = |0⟩ ⊗ |ψ⟩`.  Verified by expanding `|ψ⟩` over the
computational basis and applying the two `CNOT` truth tables. -/
theorem swapViaCnots_evolvePure_ketZero (ψ : PureState qubit) :
    swapViaCnots.evolvePure (ψ.tmul (qubitBasis 0)) = (qubitBasis 0).tmul ψ := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, PureState.tmul_vec, PureState.tmul_vec]
  change reversedCnotGate.op (cnotGate.op (ψ.vec ⊗ₜ[ℂ] (qubitBasis 0).vec))
      = (qubitBasis 0).vec ⊗ₜ[ℂ] ψ.vec
  exact reversedCnotGate_op_cnotGate_op_qubitBasisVec_zero ψ.vec

/-! ### The two measured-swap circuits accomplish the same task -/

/-- **Circuit 1, measurement statistics:** measuring the control qubit after the first measured-swap
circuit `(H ⊗ 1) · CNOT` applied to `|ψ⟩ ⊗ |0⟩` yields each outcome `m ∈ {0,1}` with probability
`½`.  The Born rule on the branch state `(√2)⁻¹(|0⟩ ⊗ |ψ⟩ + |1⟩ ⊗ Z|ψ⟩)`. -/
theorem measuredSwapCircuit1_control_bornProb (ψ : PureState qubit) (m : Fin 2) :
    (controlMeasurement qubit).bornProb
        (measuredSwapCircuit1.evolvePure (ψ.tmul (qubitBasis 0))).toState m = 1 / 2 :=
  controlMeasurement_bornProb_invSqrt2_branch _ ![ψ, pauliZGate.evolvePure ψ]
    (by rw [measuredSwapCircuit1_evolvePure_ketZero_vec]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Evolution.evolvePure_vec]
        rfl) m

/-- **Circuit 1 accomplishes the task** (N&C Exercise 10.65, first circuit): after `(H ⊗ 1) · CNOT`,
measuring the control qubit to outcome `m`, and applying the classically-controlled `Z^m`
correction to the target, the state is `|m⟩ ⊗ |ψ⟩` — the unknown `|ψ⟩` moved onto the second qubit,
for either outcome.  The control-measurement collapse leaves the target in `Z^m|ψ⟩`, which the
classically-controlled `Z` undoes on the `|1⟩` branch (`Z² = 1`). -/
theorem measuredSwapCircuit1_corrected (ψ : PureState qubit) (m : Fin 2)
    (hp : (controlMeasurement qubit).bornProb
        (measuredSwapCircuit1.evolvePure (ψ.tmul (qubitBasis 0))).toState m ≠ 0) :
    (classicalControl pauliZGate m).evolve
        ((controlMeasurement qubit).postMeasurement
          (measuredSwapCircuit1.evolvePure (ψ.tmul (qubitBasis 0))).toState m hp)
      = ((qubitBasis m).tmul ψ).toState := by
  rw [controlMeasurement_postMeasurement_invSqrt2_branch _ ![ψ, pauliZGate.evolvePure ψ]
      (by rw [measuredSwapCircuit1_evolvePure_ketZero_vec]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Evolution.evolvePure_vec]
          rfl) m hp,
    ← toState_evolvePure]
  congr 1
  fin_cases m
  · simp only [Fin.mk_zero, Matrix.cons_val_zero, classicalControl_zero, Evolution.id_evolvePure]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, classicalControl_one]
    rw [Evolution.onRight_evolvePure, ← Evolution.evolvePure_comp, pauliZGate_comp_pauliZGate,
      Evolution.id_evolvePure]

/-- **Circuit 2, measurement statistics:** measuring the control qubit after the second
measured-swap circuit `reversedCNOT · (1 ⊗ H)` applied to `|ψ⟩ ⊗ |0⟩` yields each `m ∈ {0,1}` with
probability `½`.  The Born rule on the branch state `(√2)⁻¹(|0⟩ ⊗ |ψ⟩ + |1⟩ ⊗ X|ψ⟩)`. -/
theorem measuredSwapCircuit2_control_bornProb (ψ : PureState qubit) (m : Fin 2) :
    (controlMeasurement qubit).bornProb
        (measuredSwapCircuit2.evolvePure (ψ.tmul (qubitBasis 0))).toState m = 1 / 2 :=
  controlMeasurement_bornProb_invSqrt2_branch _ ![ψ, pauliXGate.evolvePure ψ]
    (by rw [measuredSwapCircuit2_evolvePure_ketZero_vec]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Evolution.evolvePure_vec]
        rfl) m

/-- **Circuit 2 accomplishes the task** (N&C Exercise 10.65, second circuit): after
`reversedCNOT · (1 ⊗ H)`, measuring the control qubit to outcome `m`, and applying the
classically-controlled `X^m` correction to the target, the state is `|m⟩ ⊗ |ψ⟩` — the unknown `|ψ⟩`
moved onto the second qubit, for either outcome.  The collapse leaves the target in `X^m|ψ⟩`, which
the classically-controlled `X` undoes on the `|1⟩` branch (`X² = 1`). -/
theorem measuredSwapCircuit2_corrected (ψ : PureState qubit) (m : Fin 2)
    (hp : (controlMeasurement qubit).bornProb
        (measuredSwapCircuit2.evolvePure (ψ.tmul (qubitBasis 0))).toState m ≠ 0) :
    (classicalControl pauliXGate m).evolve
        ((controlMeasurement qubit).postMeasurement
          (measuredSwapCircuit2.evolvePure (ψ.tmul (qubitBasis 0))).toState m hp)
      = ((qubitBasis m).tmul ψ).toState := by
  rw [controlMeasurement_postMeasurement_invSqrt2_branch _ ![ψ, pauliXGate.evolvePure ψ]
      (by rw [measuredSwapCircuit2_evolvePure_ketZero_vec]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Evolution.evolvePure_vec]
          rfl) m hp,
    ← toState_evolvePure]
  congr 1
  fin_cases m
  · simp only [Fin.mk_zero, Matrix.cons_val_zero, classicalControl_zero, Evolution.id_evolvePure]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, classicalControl_one]
    rw [Evolution.onRight_evolvePure, ← Evolution.evolvePure_comp, pauliXGate_comp_pauliXGate,
      Evolution.id_evolvePure]

end AxQM
