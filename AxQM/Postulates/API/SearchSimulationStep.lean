/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ProjectorHamiltonian
import AxQM.Postulates.API.BlochState
import AxQM.Concrete.SearchSimulationStep

/-!
# AxQM.Postulates.API — the search-simulation step `U(Δt)` (Nielsen & Chuang, Eq. 6.25)

The physics of **Nielsen & Chuang, Exercise 6.9**: the explicit form of the
lowest-order quantum-search simulation step

`U(Δt) ≡ exp(−i|ψ⟩⟨ψ|Δt) exp(−i|x⟩⟨x|Δt)`,

the product of the two projector-Hamiltonian propagators of Exercise 6.7
(`projObservable.propagator`), evaluated on the effective search qubit. Here `|x⟩ = |0⟩` (Bloch
vector `ẑ = (0,0,1)`, so
`|x⟩⟨x| = (I + Z)/2`) and `|ψ⟩ = cos(θ/2)|0⟩ + sin(θ/2)|1⟩ = α|x⟩ + β|y⟩` (Bloch vector
`⃗ψ = (sin θ, 0, cos θ) = (2αβ, 0, α²−β²)` with `α = cos(θ/2)`, `β = sin(θ/2)`, since
`sin θ = 2 sin(θ/2)cos(θ/2) = 2αβ` and `cos θ = cos²(θ/2) − sin²(θ/2) = α²−β²`) — both realised as
`§1.2` Bloch pure states `blochPureState θ 0` (Exercise 2.72(4)), with `x = blochPureState 0 0`.

## What is formalised

* `blochPureState_projObservable_propagator_op` — the propagator `exp(−i|ψ(θ,φ)⟩⟨ψ(θ,φ)|Δt)` of a
  `§1.2` Bloch pure state, as `Matrix.toEuclideanCLM` of the Bloch-form propagator matrix
  `1 + (e^{−iΔt} − 1) blochMatrix (blochSphereVector θ φ)`. The bridge from Exercise 6.7's
  `projObservable_propagator_op` (`= 1 + (e^{−iΔt}−1)|ψ⟩⟨ψ|`) to the concrete `2 × 2` matrix
  picture, via `blochPureState_toState_op` (`|ψ⟩⟨ψ| = Matrix.toEuclideanCLM (blochMatrix ⃗r)`) and
  the `⋆`-algebra homomorphism `Matrix.toEuclideanCLM` (`map_add`/`map_one`/`map_smul`).
* `searchSimulationStep_op` — **Exercise 6.9, Eq. 6.25 at the operator level.** The composite
  `U(Δt) = exp(−i|ψ⟩⟨ψ|Δt) ∘ exp(−i|x⟩⟨x|Δt)` (operator product, `ψ`-propagator applied second)
  equals the global phase `e^{−iΔt}` times
  `Matrix.toEuclideanCLM (Concrete.searchStepReduced Δt ⃗ψ ẑ)`, the N&C eq.-6.25 reduced form
  `(c² − s² ⃗ψ·ẑ) I − 2is (c (⃗ψ+ẑ)/2 + s (⃗ψ×ẑ)/2)·σ` (`c = cos(Δt/2)`, `s = sin(Δt/2)`). Proof:
  each factor is `Matrix.toEuclideanCLM` of a propagator matrix
  (`blochPureState_projObservable_propagator_op`), their product transports through
  `Matrix.toEuclideanCLM` (`map_mul`), and the matrix identity is
  `Concrete.searchStep_eq`.

## Relation to other items

This builds on `projObservable.propagator` (Exercise 6.7) and `blochPureState` (Exercise 2.72). The
statement of Exercise 6.9 — the explicit Bloch/Pauli matrix form of eq. 6.25 — is in
`AxQM/NC/Ch6/Exercise6_9.lean`, which refers to this file and to `Concrete.searchStep_eq`.
-/

open scoped InnerProductSpace
open Matrix Complex ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The projector-Hamiltonian propagator of a §1.2 Bloch pure state, in Bloch-matrix form.** The
propagator `exp(−i|ψ(θ,φ)⟩⟨ψ(θ,φ)|Δt)` (`(blochPureState θ φ).projObservable.propagator 1 0 Δt`,
Exercise 6.7) equals `Matrix.toEuclideanCLM` of the propagator matrix
`Concrete.blochPropagatorMatrix Δt (blochSphereVector θ φ) = 1 + (e^{−iΔt} − 1) blochMatrix (…)`.
From Exercise 6.7's closed form `projObservable_propagator_op` (`.op = 1 + (e^{−iΔt}−1)|ψ⟩⟨ψ|`),
rewriting the rank-one projector as `Matrix.toEuclideanCLM (blochMatrix (blochSphereVector θ φ))`
(`blochPureState_toState_op`, Exercise 2.72(4)) and pushing `Matrix.toEuclideanCLM` through the sum,
`1`, and scalar multiple (`map_add`/`map_one`/`map_smul`; the closing `rfl` bridges the defeq
`qubit.space ≟ EuclideanSpace ℂ (Fin 2)`). -/
theorem blochPureState_projObservable_propagator_op (θ φ Δt : ℝ) :
    ((blochPureState θ φ).projObservable.propagator 1 0 Δt).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ)
          (Concrete.blochPropagatorMatrix Δt (Concrete.blochSphereVector θ φ)) := by
  rw [PureState.projObservable_propagator_op, ← PureState.toState_op, blochPureState_toState_op,
    Concrete.blochPropagatorMatrix]
  simp only [map_add, map_one, map_smul]
  rfl

/-- **Nielsen & Chuang, Exercise 6.9 — verification of Eq. 6.25 (operator level).** The
lowest-order quantum-search simulation step `U(Δt) = exp(−i|ψ⟩⟨ψ|Δt) exp(−i|x⟩⟨x|Δt)` — the operator
product of the two projector-Hamiltonian propagators (Exercise 6.7), the `|ψ⟩`-factor applied second
— for `|x⟩ = |0⟩ = blochPureState 0 0` (Bloch vector `ẑ`) and
`|ψ⟩ = cos(θ/2)|0⟩ + sin(θ/2)|1⟩ = blochPureState θ 0` (Bloch vector `⃗ψ = (sin θ, 0, cos θ)`)
equals

`U(Δt) = e^{−iΔt} · [(c² − s² ⃗ψ·ẑ) I − 2is (c (⃗ψ+ẑ)/2 + s (⃗ψ×ẑ)/2)·σ]`

(`c = cos(Δt/2)`, `s = sin(Δt/2)`), i.e. `e^{−iΔt}` times
`Matrix.toEuclideanCLM (Concrete.searchStepReduced Δt ⃗ψ ẑ)`. The unimportant global phase
`e^{−iΔt}` of N&C's "up to a global phase factor" is here made explicit. Proof: each propagator is
`Matrix.toEuclideanCLM` of a Bloch-form propagator matrix
(`blochPureState_projObservable_propagator_op`); their product transports through the `⋆`-algebra
homomorphism `Matrix.toEuclideanCLM` (`map_mul`), and the underlying `2 × 2` matrix identity is the
`Concrete` core `Concrete.searchStep_eq` (both Bloch vectors are unit, `blochSphereVector_normSq`).
-/
theorem searchSimulationStep_op (θ Δt : ℝ) :
    ((blochPureState θ 0).projObservable.propagator 1 0 Δt).op
        * ((blochPureState 0 0).projObservable.propagator 1 0 Δt).op
      = Complex.exp (-(Complex.I * (Δt : ℂ)))
          • Matrix.toEuclideanCLM (𝕜 := ℂ)
              (Concrete.searchStepReduced Δt (Concrete.blochSphereVector θ 0)
                (Concrete.blochSphereVector 0 0)) := by
  rw [blochPureState_projObservable_propagator_op, blochPureState_projObservable_propagator_op]
  -- Re-elaborate the operator product `*` at `EuclideanSpace ℂ (Fin 2)` (defeq to the ambient
  -- `qubit.space`), so `map_mul` for `Matrix.toEuclideanCLM` applies.
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
          (Concrete.blochPropagatorMatrix Δt (Concrete.blochSphereVector θ 0))
        * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
          (Concrete.blochPropagatorMatrix Δt (Concrete.blochSphereVector 0 0))
      = Complex.exp (-(Complex.I * (Δt : ℂ)))
          • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
              (Concrete.searchStepReduced Δt (Concrete.blochSphereVector θ 0)
                (Concrete.blochSphereVector 0 0))
  rw [← map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)),
    Concrete.searchStep_eq (Concrete.blochSphereVector_normSq θ 0)
      (Concrete.blochSphereVector_normSq 0 0),
    map_smul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))]

end AxQM
