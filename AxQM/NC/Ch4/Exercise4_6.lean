/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BlochRotationGate

/-!
# Nielsen & Chuang, Exercise 4.6 — the rotation `R_n̂(θ)` rotates the Bloch vector

**Exercise 4.6 ("Bloch sphere interpretation of rotations").** N&C asks to show that the qubit
rotation `R_n̂(θ) = exp(−iθ n̂·σ/2)` (eq. 4.8) acting on a state with Bloch vector `⃗λ` rotates `⃗λ`
through the angle `θ` about the `n̂` axis.

## Where the formalisation lives

The statement of the exercise is

* `AxQM.rotAxisGate_evolve_blochState`
  (in `AxQM/Postulates/API/BlochRotationGate.lean`) —
  for a unit axis `n̂` and any Bloch vector `⃗λ` in the closed unit ball, evolving the Bloch state
  `blochState ⃗λ` — the qubit density operator `½(I + ⃗λ·σ)` — by the rotation gate
  `rotAxisGate n̂ θ` gives the Bloch state of the *rotated* vector:
  `(rotAxisGate n̂ θ).evolve (blochState ⃗λ) = blochState (Concrete.rot3D n̂ θ ⃗λ)`, where
  `Concrete.rot3D n̂ θ` is the Rodrigues rotation of a three-vector about `n̂` by `θ`. In words: the
  state channel `ρ ↦ R_n̂(θ) ρ R_n̂(θ)†` induced by the rotation gate rotates the Bloch vector by
  `θ` about `n̂`.

The rotated vector `rot3D n̂ θ ⃗λ` is again in the Bloch ball because a rotation preserves the
squared Bloch-vector length (`Concrete.rot3D_sq_sum`), so `blochState (rot3D n̂ θ ⃗λ)` is a bona
fide state; this is the well-definedness certificate the statement carries.

## Uses

The theorem is stated for the evolution `Evolution.evolve`, the Bloch state `blochState` and the
rotation `Concrete.rot3D`, beside the gate `rotAxisGate` (Nielsen & Chuang, eq. 4.8). It is used by
the general single-qubit `unitaryGate_evolve_blochState` (Exercise 8.13), the Problem 8.3 qubit
Pauli channel, and the `SU(2) → SO(3)` cover surjectivity
(`exists_evolution_evolve_blochState_of_mem_specialOrthogonalGroup`). Compare Exercises 8.11, 8.12,
8.13 and Theorem 8.3.

## Fidelity

The unit-axis hypothesis is genuine: N&C's `n̂` is a unit vector (the rotation *axis*), so the
hypothesis `n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1` is not a weakening but part of the setup — it is what
makes `R_n̂(θ)` a rotation (`(n̂·σ)² = I`) and keeps the rotated vector in the ball. The angle `θ`
and the Bloch vector `⃗λ` are fully general.
-/
