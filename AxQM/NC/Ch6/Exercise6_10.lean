/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SearchSimulationLanding
import AxQM.Concrete.SearchSimulationTiming

/-!
# Nielsen & Chuang, Exercise 6.10 (probability-one search by a tuned simulation step)

*(N&C p. 260.)*

Show a suitable dt gives O(sqrt N) query search with final state exactly |x> (prob 1).

## The setup (N&C §6.2, eqs. 6.25–6.28)

The quantum-search-as-simulation algorithm iterates the lowest-order simulation step
`U(Δt) = exp(−i|ψ⟩⟨ψ|Δt) exp(−i|x⟩⟨x|Δt)` (Exercise 6.9, eq. 6.25). Restricted to the effective
search qubit `span{|x⟩, |y⟩}`, `U(Δt)` is — up to a global phase — a Bloch-sphere rotation about a
tilted axis `⃗r` through an angle `θ` with `cos(θ/2) = 1 − (2/N) sin²(Δt/2)` (eq. 6.28), and `|ψ⟩`,
`|x⟩` lie on a common circle of revolution about `⃗r`. The `Δt = π` special case reproduces the
Grover iteration and reaches `|x⟩` only approximately (small failure probability).

**The exercise.** Rather than maximising the angle (`Δt = π`), *tune* `Δt` so that after an integer
number `j` of steps `|ψ⟩` lands **exactly** on `|x⟩`. Geometrically the azimuthal separation of
`|ψ⟩` and `|x⟩` about `⃗r` is `π − θ/2`, so exact landing needs `jθ = π − θ/2`, i.e.
`(2j+1)θ = 2π`; and the exact-landing angle `θ = 2π/(2j+1)` is achievable within the reachable range
as soon as `2j+1 ≥ (π/2)√N`. Taking the minimal such `j = ⌈(π/4)√N⌉ = O(√N)` gives an `O(√N)`-query
search that ends on `|x⟩` with probability `1`.

## What is formalised, and where

The physical claim is `searchStepEvolution_exactSearch` in this file; it rests on a lift to states
in `AxQM/Postulates/API/SearchSimulationLanding.lean` and on the pure Bloch geometry in
`AxQM/Concrete/SearchSimulationStep.lean`, `AxQM/Concrete/SearchSimulationLanding.lean` and
`AxQM/Concrete/SearchSimulationTiming.lean`.

* **Statement (`searchStepEvolution_exactSearch`, this file).** For a search space of size `N ≥ 2`
  with effective search qubit `|ψ⟩ = blochPureState θ 0` (`cos θ = ⃗ψ·ẑ = α² − β² = 2/N − 1`, the
  uniform search state) and target `|x⟩ = blochPureState 0 0 = |0⟩`, there are a step count `j` and
  a simulation time-step `Δt ∈ (0, π]` such that:
  - `j ≤ (π/4 + 1)·√N` — `O(√N)` applications of the search step `U(Δt)`, hence `O(√N)` oracle calls
    (each `U(Δt)` is `O(1)` oracle calls, Figures 6.4/6.5, Exercise 6.7); and
  - `((U(Δt))^j |ψ⟩).toState = |x⟩.toState` — evolving `|ψ⟩` under the `j`-th power of the search
    step yields the solution state `|x⟩` **exactly** (the density operators coincide, so the state
    is `|x⟩⟨x|`, i.e. a computational-basis measurement returns `x` with probability `1`).

  The statement uses `searchStepEvolution` (the search step as an `Evolution`), `Evolution` powers,
  `Evolution.evolvePure`, `PureState.toState` and `blochPureState`.
* **The lift (`AxQM/Postulates/API/SearchSimulationLanding.lean`).** `searchStepEvolution θ Δt` is
  the step `U(Δt)` as an `Evolution` (composition of the Exercise 6.7 projector-Hamiltonian
  propagators), and `searchStepEvolution_pow_evolvePure_toState` lifts the `Concrete` Bloch-matrix
  landing to the `PureState`/`State` equality above (the global phase `e^{−iΔt}` of `U(Δt)` cancels
  in the density picture).
* **Bloch geometry (the `SearchSimulation*` files of `AxQM/Concrete/`).** The reduced step as one
  Bloch rotation (`searchStepReduced_eq_rotAxis`), the exact-landing conjugation
  `U(Δt)^j |ψ⟩⟨ψ| (U(Δt)^j)† = |x⟩⟨x|` under `(2j+1)θ = 2π`
  (`searchStepReduced_pow_conj_blochMatrix_land`), and the tuning of `Δt` with the `O(√N)`
  step count (`searchStepReduced_pow_conj_blochMatrix_exactSearch`).

## Design decisions

* **Density-operator equality, not a weaker "overlap ≈ 1".** "The final state is `|x⟩` exactly,
  probability `1`" is formalised as the exact equality of the evolved state's density operator with
  `|x⟩⟨x|` (`.toState = (blochPureState 0 0).toState`) — the phase-invariant, exact reading of the
  claim, with no small-error slack.
* **Effective qubit + the physical relation `cos θ = 2/N − 1`.** N&C's own analysis reduces the
  `N`-item search to the effective qubit `span{|x⟩, |ψ⟩}`; `blochPureState θ 0` is that qubit and
  `cos θ = 2/N − 1` is exactly the uniform search state's polar angle (`α² = 1/N`). This is the
  faithful setup, matching the effective-qubit reductions of the neighbouring search exercises.
* **`O(√N)` queries via the step count `j`.** Each `U(Δt)` costs `O(1)` oracle calls, so the number
  of queries is `Θ(j)`; the explicit bound `j ≤ (π/4 + 1)√N` inside the existential is the `O(√N)`
  claim, as N&C phrase it ("the number of oracle calls … is `O(√N)`").
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 6.10 — a tuned `O(√N)`-query search that lands on `|x⟩` exactly
(probability `1`).** For a search space of size `N ≥ 2`, with effective search qubit
`|ψ⟩ = blochPureState θ 0` whose polar angle satisfies `cos θ = 2/N − 1` (the uniform search state
`α|x⟩ + β|y⟩`, `α² = 1/N`, `cos θ = α² − β²`) and target `|x⟩ = blochPureState 0 0 = |0⟩`, there are
a step count `j` and a simulation time-step `Δt ∈ (0, π]` with:

* `1 ≤ j ≤ (π/4 + 1)·√N` — `O(√N)` applications of the search step
  `U(Δt) = searchStepEvolution θ Δt` (hence `O(√N)` oracle calls, each step being `O(1)` calls,
  Figures 6.4/6.5); and
* `((U(Δt))^j |ψ⟩).toState = |x⟩.toState` — the state obtained by evolving `|ψ⟩` under the `j`-th
  power of the search step is `|x⟩` **exactly** (the density operators coincide), so the algorithm
  succeeds with probability `1`, improving on the small-failure-probability `Δt = π` special case.

Proof: the `Concrete` tuning `searchStepReduced_pow_conj_blochMatrix_exactSearch` supplies
`j = ⌈(π/4)√N⌉` and the tuned `Δt`, together with the Bloch-matrix exact-landing
`U(Δt)^j |ψ⟩⟨ψ| (U(Δt)^j)† = |x⟩⟨x|`; rewriting `ẑ = ![0,0,1] = blochSphereVector 0 0` feeds it into
the lift `searchStepEvolution_pow_evolvePure_toState`, which transports the landing
to the `PureState`/`State` equality. -/
theorem searchStepEvolution_exactSearch (N : ℕ) (hN : 2 ≤ N) (θ : ℝ)
    (hθcos : Real.cos θ = 2 / (N : ℝ) - 1) :
    ∃ (j : ℕ) (Δt : ℝ), 0 < Δt ∧ Δt ≤ Real.pi ∧ 1 ≤ j ∧
      (j : ℝ) ≤ (Real.pi / 4 + 1) * Real.sqrt N ∧
      ((searchStepEvolution θ Δt ^ j).evolvePure (blochPureState θ 0)).toState
        = (blochPureState 0 0).toState := by
  obtain ⟨j, Δt, hΔt0, hΔtπ, hj1, hjb, hland⟩ :=
    Concrete.searchStepReduced_pow_conj_blochMatrix_exactSearch N hN θ hθcos
  refine ⟨j, Δt, hΔt0, hΔtπ, hj1, hjb, ?_⟩
  -- The `Concrete` landing is stated with `ẑ = ![0,0,1]`; rewrite it as `blochSphereVector 0 0` to
  -- match the target `|x⟩ = blochPureState 0 0`, then apply the lift.
  have hz : Concrete.blochSphereVector 0 0 = ![0, 0, 1] := by
    simp [Concrete.blochSphereVector]
  rw [← hz] at hland
  exact searchStepEvolution_pow_evolvePure_toState θ Δt j hland

end AxQM
