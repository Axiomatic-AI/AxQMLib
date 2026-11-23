/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SearchSimulationStep

/-!
# Nielsen & Chuang, Exercise 6.9 (verification of Equation 6.25)

*(N&C p. 259.)*

Verify Equation (6.25), the explicit form of U(dt)=exp(-i|psi><psi|dt)exp(-i|x><x|dt).

Equation (6.25) is the explicit form of the lowest-order quantum-search simulation step
`U(Δt) ≡ exp(−i|ψ⟩⟨ψ|Δt) exp(−i|x⟩⟨x|Δt)` — the product of the two projector-Hamiltonian propagators
of §6.2 (Exercise 6.7). Restricted to the effective search qubit `span{|x⟩,|y⟩}`, with
`|x⟩⟨x| = (I + ẑ·σ)/2` (`ẑ = (0,0,1)`) and `|ψ⟩⟨ψ| = (I + ⃗ψ·σ)/2`
(`⃗ψ = (2αβ, 0, α²−β²)` for `|ψ⟩ = α|x⟩ + β|y⟩`), N&C state that "up to an unimportant global phase
factor" (with `c = cos(Δt/2)`, `s = sin(Δt/2)`)

`U(Δt) = (c² − s² ⃗ψ·ẑ) I − 2is (c (⃗ψ+ẑ)/2 + s (⃗ψ×ẑ)/2)·σ`.   (6.25)

The hint points to Exercise 4.15: each factor `exp(−i (I + n·σ)/2 · Δt)` is, up to a global phase
`e^{−iΔt/2}`, the Bloch rotation `R_n̂(Δt) = cos(Δt/2) I − i sin(Δt/2)(n·σ)`, and the product of two
such rotations is the composition law `(a·σ)(b·σ) = (a·b) I + i (a×b)·σ` of Exercise 4.15 —
`U(Δt) = e^{−iΔt} R_⃗ψ(Δt) R_ẑ(Δt)`, whose closed form is exactly (6.25) with the global phase
`e^{−iΔt}` made explicit.

## The formalisation

Equation (6.25) is a statement about matrices: its right-hand side is an explicit `2 × 2`
Pauli/Bloch matrix. The declarations are:

* **`AxQM.searchSimulationStep_op`**
  (`AxQM/Postulates/API/SearchSimulationStep.lean`) — **Exercise 6.9 / Eq. 6.25, at the
  operator level.** For `|x⟩ = blochPureState 0 0` and `|ψ⟩ = blochPureState θ 0`, the composite
  `U(Δt) = (ψ-propagator).op * (x-propagator).op` (of the Exercise 6.7 projector-Hamiltonian
  propagators `projObservable.propagator`) equals `e^{−iΔt}` times
  `Matrix.toEuclideanCLM (Concrete.searchStepReduced Δt ⃗ψ ẑ)`, the eq.-6.25 reduced form.
* **`AxQM.blochPureState_projObservable_propagator_op`** (same file) — the supporting
  bridge: each projector-Hamiltonian propagator, as `Matrix.toEuclideanCLM` of the Bloch-form
  propagator matrix `Concrete.blochPropagatorMatrix`.
* **`AxQM.Concrete.searchStep_eq`** (`AxQM/Concrete/SearchSimulationStep.lean`) —
  the pure `2 × 2`-matrix core: `blochPropagatorMatrix Δt a * blochPropagatorMatrix Δt b =
  e^{−iΔt} · searchStepReduced Δt a b`, with the supporting
  `Concrete.blochPropagatorMatrix_eq_smul_rotAxis` (propagator = phase × rotation) and
  `Concrete.rotAxis_mul_rotAxis_eq_searchStepReduced` (the Exercise 4.15 composition law written in
  N&C's eq.-6.25 shape). `Concrete.searchStepReduced` is the explicit eq.-6.25 right-hand side.

The statement `searchSimulationStep_op` is about the pure states `blochPureState` and their
propagators `projObservable.propagator` (Exercise 6.7); the `Concrete` core re-uses the Exercise
4.15 rotation-composition development (`Concrete.rotAxis_mul_rotAxis`).
-/
