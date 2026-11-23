/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.UnitaryBlochRotation

/-!
# Nielsen & Chuang, Exercise 8.13 — unitary transformations are rotations of the Bloch sphere

*(N&C p. 375.)*

Show unitary transformations correspond to rotations of the Bloch sphere.

In the Bloch representation `ρ = ½(I + r·σ)` of a single-qubit state, a unitary `U` acts on the
state by conjugation `ρ ↦ U ρ U†`. The exercise asks to show that the induced transformation of the
Bloch vector `r` is a *rotation* — a proper orthogonal map `R ∈ SO(3)`. This is the `SU(2) → SO(3)`
homomorphism: the single-qubit unitaries (modulo the global phase, which cancels in the conjugation)
double-cover the rotation group of the Bloch ball.

## The formalisation

The exercise's statement — *for any `2 × 2` unitary `U` there is `R ∈ SO(3)` such that the
state conjugation sends `blochState r` to `blochState (R r)`* — involves the
argument `U : Matrix (Fin 2) (Fin 2) ℂ` and the rotation `R ∈ Matrix.specialOrthogonalGroup (Fin 3)
ℝ`. The content is *physics* (it is about `Evolution.evolve` on a `State`, not a bare matrix
identity), with building blocks `blochState` and `rotAxisGate`. It is formalised in two
parts: the `SU(2) → SO(3)` matrix core and the statement about states below. Compare Exercises 8.11
and 8.12 and Theorem 8.3.

* `AxQM/Postulates/API/UnitaryBlochRotation.lean` — **the statement about states**:
  * `AxQM.exists_mem_specialOrthogonalGroup_unitaryGate_evolve_blochState` — **Exercise
    8.13**: for any single-qubit unitary `U`, there is `R ∈ SO(3)` with `(unitaryGate hU).evolve
    (blochState r) = blochState (R r)` for every Bloch vector `r` — unitary evolution *is* a proper
    rotation of the Bloch sphere.
  * `AxQM.unitaryGate hU` — the single-qubit unitary gate of `U` as an `Evolution qubit`
    (`Matrix.toEuclideanCLM U`, unitarity transported from `hU`); the general single-qubit unitary.
  * `AxQM.unitaryGate_evolve_blochState` — the worked identity `(unitaryGate hU).evolve
    (blochState r) = blochState ((blochRotationOfUnitary U) r)`, the concrete witness behind the
    existential.

* `AxQM/Concrete/BlochUnitaryRotation.lean` — **the matrix core**:
  * `AxQM.Concrete.exists_mem_specialOrthogonalGroup_blochMatrix_conj_unitary` — the
    matrix-level statement `∃ R ∈ SO(3), ∀ r, U · blochMatrix r · U† = blochMatrix (R r)`.
  * `AxQM.Concrete.blochRotationOfUnitary` — the induced `3 × 3` rotation `R(U)` (the
    `SU(2) → SO(3)` image), with `blochRotationOfUnitary_mem_specialOrthogonalGroup` (`R(U) ∈
    SO(3)`, from uniform Pauli-trace identities), `blochMatrix_conj_unitary` (the conjugation
    identity), and `blochRotationOfUnitary_mulVec_sq_sum` (norm preservation, keeping `R(U) r` in
    the ball).

See the module docstrings of `AxQM/Postulates/API/UnitaryBlochRotation.lean` and
`AxQM/Concrete/BlochUnitaryRotation.lean` for the full argument, and `AxQM/NC/Ch4/Exercise4_6.lean`
for the axis-rotation companion (the same identity for the rotation gates `R_n̂(θ)`).
-/
