/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BellMeasurementCircuit

/-!
# Nielsen & Chuang, Exercise 4.33 — measurement in the Bell basis

N&C's circuit model measures only in the computational basis; to
measure in another basis one first **unitarily transforms that basis to the computational basis and
then measures**.  For the Bell basis the transforming circuit is a `CNOT` (control = first qubit,
target = second) followed by a Hadamard on the first qubit.  Exercise 4.33 asks to show this circuit
performs a measurement in the Bell basis, that its POVM elements are the four projectors onto the
Bell states, and what the corresponding measurement operators are.

## The formalisation

The formalisation is in `AxQM/Postulates/API/BellMeasurementCircuit.lean`.  Its central
declarations are the *measurement* answers: the measurement operators `bellMeasurement.op`, the
induced POVM `bellMeasurement.toPOVM`, and the rank-one projectors `InnerProductSpace.rankOne`.  The
circuit `def`s and the unitary rotation identities they build on are there too.

## The declarations (in `AxQM/Postulates/API/BellMeasurementCircuit.lean`, except the last)

* `bellPrepCircuit` = `CNOT ∘ (H ⊗ 1)` and `bellMeasurementCircuit` = `(H ⊗ 1) ∘ CNOT` — the
  Bell-state preparation circuit and its inverse, the exercise's measurement circuit.
* `bellPrepCircuit_evolvePure_qubitBasis` — `bellPrepCircuit |xy⟩ = |β_xy⟩` (`|β_xy⟩ = CNOT (H⊗1)
  |xy⟩`, N&C eqs. 1.24–1.25).
* `bellMeasurementCircuit_evolvePure_bellState` — `bellMeasurementCircuit |β_xy⟩ = |xy⟩`: the
  circuit rotates the Bell basis onto the computational basis, which is what makes measuring its
  output in the computational basis a measurement in the Bell basis.
* `bellMeasurementCircuit_op_adjoint_qubitBasis` — `U† |xy⟩ = |β_xy⟩` (the measurement circuit's
  adjoint carries the computational basis onto the Bell basis).
* `bellMeasurement_op_eq_bellMeasurementCircuit_conj` — **the measurement operators**: the induced
  measurement operator for outcome `(x, y)` is `U† |xy⟩⟨xy| U = |β_xy⟩⟨β_xy| = bellMeasurement.op
  (x, y)`, tying the CNOT+H circuit to the Bell-basis measurement `bellMeasurement`.
* `bellMeasurement_toPOVM_elements_eq_bellProjector` — **the POVM elements**:
  `bellMeasurement.toPOVM.elements (x, y) = |β_xy⟩⟨β_xy|`, the four projectors onto the Bell states.
  (This one is a basic property of `bellMeasurement` independent of the circuit; it is in
  `AxQM/Postulates/API/Teleportation.lean`.)
-/
