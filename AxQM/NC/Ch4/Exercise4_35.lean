/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DeferredMeasurement
import AxQM.Postulates.API.ControlMeasurementCommute

/-!
# Nielsen & Chuang, Exercise 4.35 (measurement commutes with controls)

*(N&C p. 188.)*

Prove measurement commutes with a gate when the measured qubit is the control.

## The formalisation

The two circuits either side of N&C's first equality act on `qubit ⊗ S` (control qubit on the left):

* **left circuit** — apply the controlled gate `C(U)` (`controlledUnitary U`), then measure the
  control qubit in the computational basis (`controlMeasurement S`, operators `Mᵢ = |i⟩⟨i| ⊗ 1`);
* **right circuit** — measure the control qubit, then apply the *classically-controlled* gate
  `Wᵢ = classicalControl U i` on the branch of outcome `i` (nothing on `|0⟩`, `1 ⊗ U` on `|1⟩`).

A measurement circuit is fixed by, for each outcome, its probability (Postulate 3) and its
post-measurement state (Postulate 4). The equality of the two circuits is therefore the pair of
theorems below, stated with `Measurement.bornProb` / `Measurement.postMeasurement` /
`Evolution.evolve`:

* `controlMeasurement_commute_bornProb` — **the outcome statistics agree**: the Born probability of
  outcome `i` is the same whether the control is measured before or after `C(U)`,
  `p(i ∣ C(U) ρ C(U)†) = p(i ∣ ρ)`.
* `controlMeasurement_commute_postMeasurement` — **the post-measurement states agree**: measuring
  the control after `C(U)` yields exactly the classically-controlled gate `Wᵢ` applied to the state
  obtained by measuring the control first, `postMeas(C(U) ρ C(U)†, i) = Wᵢ · postMeas(ρ, i)`.

## Design

The physical content is the *deferred-measurement engine* `Measurement.postOp_evolve_of_comm` and
its Born-rule / collapse corollaries (`AxQM/Postulates/API/DeferredMeasurement.lean`),
whose single hypothesis — the control projector commuting with the gate up to the branch unitary,
`Mᵢ · C(U) = Wᵢ · Mᵢ` — is the lemma `controlMeasurement_op_comp_controlledUnitary`.
The theorems below are the instantiation, at `m = controlMeasurement S`, `V = controlledUnitary U`,
`W = classicalControl U`. Both theorems are stated for an *arbitrary* target `S`, input `ρ`, gate
`U`, and outcome `i` — no dimension specialized, no hypothesis beyond the `p(i) ≠ 0` that
`postMeasurement` requires (and which transfers to the evolved state as the probabilities agree).
The finer *instrument* identity `Mᵢ (C(U) ρ C(U)†) Mᵢ† = Wᵢ (Mᵢ ρ Mᵢ†) Wᵢ†` and the commutation
are stated in terms of the measurement operators; the theorems here are the readings for states.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Exercise 4.35 (measurement statistics).** Measuring the control qubit commutes with the
controlled gate `C(U)` at the level of the Born probabilities: for every outcome `i`, the
probability of `i` when the control is measured *after* applying `C(U)` equals the probability when
it is measured on the input directly, `p(i ∣ C(U) ρ C(U)†) = p(i ∣ ρ)`. The instance at
`m = controlMeasurement S`, `V = controlledUnitary U`, `W = classicalControl U` of the
deferred-measurement Born-rule invariance `Measurement.bornProb_evolve_of_comm`, whose commutation
hypothesis is `controlMeasurement_op_comp_controlledUnitary`. -/
theorem controlMeasurement_commute_bornProb (U : Evolution S) (ρ : State (qubit ⊗ S)) (i : Fin 2) :
    (controlMeasurement S).bornProb ((controlledUnitary U).evolve ρ) i
      = (controlMeasurement S).bornProb ρ i :=
  Measurement.bornProb_evolve_of_comm (controlMeasurement S) (controlledUnitary U)
    (classicalControl U) (controlMeasurement_op_comp_controlledUnitary U) ρ i

/-- **Exercise 4.35 (post-measurement state, the first equality).** Measuring the control qubit
commutes with the controlled gate `C(U)` at the level of the collapsed state: for every outcome `i`
possible on `ρ`, the state after applying `C(U)` and *then* measuring the control equals the
classically-controlled gate `Wᵢ = classicalControl U i` applied to the state obtained by measuring
the control *first*,

  `postMeas(C(U) ρ C(U)†, i) = Wᵢ · postMeas(ρ, i)`.

This is N&C's first equality: the left circuit (gate then measure) equals the right circuit (measure
then classically-controlled gate). The outcome is equally possible after `C(U)` because the
probabilities agree (`controlMeasurement_commute_bornProb`). The instance of the
deferred-measurement collapse law `Measurement.postMeasurement_evolve_of_comm` at the control
measurement, `C(U)`, and the classical-control family. -/
theorem controlMeasurement_commute_postMeasurement (U : Evolution S) (ρ : State (qubit ⊗ S))
    (i : Fin 2) (hp : (controlMeasurement S).bornProb ρ i ≠ 0) :
    (controlMeasurement S).postMeasurement ((controlledUnitary U).evolve ρ) i
        (by rw [controlMeasurement_commute_bornProb]; exact hp)
      = (classicalControl U i).evolve ((controlMeasurement S).postMeasurement ρ i hp) :=
  Measurement.postMeasurement_evolve_of_comm (controlMeasurement S) (controlledUnitary U)
    (classicalControl U) (controlMeasurement_op_comp_controlledUnitary U) ρ i hp

end AxQM
