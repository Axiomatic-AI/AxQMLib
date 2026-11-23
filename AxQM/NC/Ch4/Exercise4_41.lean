/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RzThreeFifthsMeasurement

/-!
# Nielsen & Chuang, Exercise 4.41 (Fig 4.17 — a measurement-based `R_z(θ)`, `cos θ = 3/5`)

*(N&C p. 198.)*

Show the circuit of Fig 4.17 applies R_z(theta) with cos theta=3/5 on success.

The circuit `(H⊗H)·T·(1⊗1⊗S)·T·(H⊗H)` on `qubit ⊗ (qubit ⊗ qubit)`
(two ancilla controls, one target) is a genuine closed-system `Evolution` (Postulate 5); "applies
`R_z(θ)` / `Z` to the target" is a statement about the (unnormalised) Kraus operator on the target
conditioned on each two-ancilla measurement outcome, and the `5/8` / `1/8` weights are Born-rule
probabilities.

## What this file states, and where the rest is

This file states the **Born-rule reading** of the circuit, over `Measurement.bornProb`; compare
Exercise 4.34 and `AxQM/Postulates/API/MeasureObservableAncilla.lean`:

* `rzThreeFifthsCircuit_bothZero_bornProb` — **the probability of both ancilla outcomes being `0` is
  `5/8`, for every target `|ψ⟩`.** Running the explicit two-ancilla `Measurement`
  `rzTwoAncillaMeasurement` after the circuit on `|0,0,ψ⟩` gives outcome `(0,0)` with Born
  probability exactly `5/8` for an arbitrary (normalised) single-qubit target `|ψ⟩` — N&C's second
  explicit claim, input-independent, stated for measurements and evolutions
  (`Measurement.bornProb`, `Evolution.evolvePure`, `PureState.tmul`).
  `rzThreeFifthsCircuit_bothZero_bornProb_qubitBasis` is
  its specialization to the two computational basis targets.

The statements about `Evolution.op`, `PureState.vec` and the concrete gate matrices are:

* **The circuit and its sub-gates** (`AxQM/Postulates/API/RzThreeFifthsCircuit.lean`):
  `rzThreeFifthsCircuit`, the middle-gate diagonalisation
  `rzThreeFifthsMiddle_evolvePure_qubitBasis_vec` (`|a,b,t⟩ ↦ i^{(t + a·b mod 2)} |a,b,t⟩`), the
  four-branch action `rzThreeFifthsCircuit_evolvePure_ketZeroZero_qubitBasis`, and the amplitude
  table `rzThreeFifthsAmp_apply` (success column `(3+i)/4, (1+3i)/4`; failure columns `±(1-i)/4`).
* **Success `= R_z(θ)`, `cos θ = 3/5`** — `rzThreeFifthsCircuit_success_eq_rotZ`: the success
  (Kraus) operator `M₀₀` on the target equals `c · R_z(θ)` with `‖c‖² = 5/8` and `cos θ = 3/5`
  (`rzThreeFifthsAngle_cos`; `rzThreeFifthsAngle_exp_mul_I` gives `e^{iθ} = (3+4i)/5` for Ex 4.42).
  Because `R_z(θ)` is unitary, `‖c‖² = 5/8` is the *input-independent* Born probability of the `00`
  outcome, so the `5/8` here holds for every target `|ψ⟩`, not only the basis states.
* **Failure `= Z`, probability `1/8` each** — `rzThreeFifthsCircuit_failure_eq_pauliZ`: every other
  ancilla outcome gives a target operator `= c · Z` with `‖c‖² = 1/8`, the complementary `3 · 1/8`.
* **The two-ancilla measurement** (`AxQM/Postulates/API/RzThreeFifthsMeasurement.lean`):
  `rzTwoAncillaMeasurement` (the cascade of the two computational-basis control measurements, its
  `(a',b')` operator the projector `|a'⟩⟨a'| ⊗ |b'⟩⟨b'| ⊗ 1`), the projector-collapse
  `rzTwoAncillaMeasurement_op_zeroZero_qubitBasis`, and the success-branch reading
  `rzTwoAncillaMeasurement_op_rzThreeFifthsCircuit_qubitBasis` from which the probability below
  is derived.

## Faithfulness and scope

* **Fidelity.** `cos θ = 3/5` is proved exactly, the success probability is exactly `5/8`, and the
  failure operator is exactly `∝ Z`. The `5/8` reading is stated for an **arbitrary** target
  `|ψ⟩` (`rzThreeFifthsCircuit_bothZero_bornProb`) — the input-independence that is the physical
  content of N&C's "the probability … is `5/8`" — proved from the success operator identity
  `M₀₀ = c · R_z(θ)`, `‖c‖² = 5/8`, `R_z(θ)` unitary. Nothing is weakened.
* **Informal remark.** The closing "repeated use of this circuit and `Z = S²` gates may be
  used to apply `R_z(θ)` with probability approaching `1`" is an informal description of a
  repeat-until-success protocol (retry on failure, correcting the erroneous `Z` with a subsequent
  `S²`), not a single verifiable proposition, and is not formalised.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.41 — the success probability is `5/8`, for every target `|ψ⟩`.**
Measuring both ancilla qubits of the Figure 4.17 circuit in the computational basis
(`rzTwoAncillaMeasurement`) after the circuit acts on `|0,0,ψ⟩`, the outcome "both `0`" occurs with
Born probability exactly `5/8` — Nielsen & Chuang's value — for *any* (normalised) single-qubit
target `|ψ⟩`. Stated over `Measurement.bornProb`: the probability
is `‖M₀₀|ψ⟩‖² = ‖c‖² = 5/8` because the success operator is `M₀₀ = c · R_z(θ)` with `‖c‖² = 5/8`
and `R_z(θ)` unitary (`rzThreeFifthsCircuit_success_eq_rotZ`). Input-independence is exactly N&C's
claim ("the probability of both measurement outcomes being 0 is 5/8"). -/
theorem rzThreeFifthsCircuit_bothZero_bornProb (ψ : PureState qubit) :
    rzTwoAncillaMeasurement.bornProb
        (rzThreeFifthsCircuit.evolvePure ((qubitBasis 0).tmul ((qubitBasis 0).tmul ψ))).toState
        (0, 0)
      = 5 / 8 := by
  rw [Measurement.bornProb_toState_eq_normSq, rzTwoAncillaMeasurement_bornProb_normSq]

/-- **Exercise 4.41, computational basis specialization.** The success probability `5/8` at the two
computational basis targets `|0⟩`, `|1⟩` (the `R_z(θ)` eigenstates) — the specialization of the
arbitrary-input `rzThreeFifthsCircuit_bothZero_bornProb` to `ψ = |t⟩`. -/
theorem rzThreeFifthsCircuit_bothZero_bornProb_qubitBasis (t : Fin 2) :
    rzTwoAncillaMeasurement.bornProb
        (rzThreeFifthsCircuit.evolvePure
          ((qubitBasis 0).tmul ((qubitBasis 0).tmul (qubitBasis t)))).toState (0, 0)
      = 5 / 8 :=
  rzThreeFifthsCircuit_bothZero_bornProb (qubitBasis t)

end AxQM
