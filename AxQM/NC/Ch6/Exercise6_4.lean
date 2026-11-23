/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GroverSearchMeasurement

/-!
# Nielsen & Chuang, Exercise 6.4 (the quantum search algorithm for multiple solutions)

*(N&C p. 254.)*

Give explicit steps for the quantum search algorithm for multiple solutions (1<M<N/2).

The boxed "Algorithm: Quantum search" of §6.1.4 is stated for a single solution (`M = 1`); this
exercise asks for the general `M`-solution version. Its four steps are unchanged — (1) prepare the
`n`-qubit register in `|0⟩⊗ⁿ`, (2) Hadamard it into the equal superposition `|ψ⟩`, (3) apply the
Grover iteration `G` a chosen number of times `R`, (4) measure in the computational basis — and the
*only* substance distinguishing the general case from `M = 1` is the iteration count `R` and the
guarantee that after `R` iterations a measurement returns a solution with probability at least `½`,
using only `R = O(√(N/M))` oracle calls. That guarantee is what we formalise.

## Where the content lives

The whole analysis takes place, following N&C §6.1.3–6.1.4, in the two-dimensional plane
`span{|α⟩, |β⟩}` — `|α⟩` the uniform superposition of the non-solutions, `|β⟩` that of the
solutions — in which the Grover iteration is a rotation (Exercise 6.3). It has two parts:

* **Analytic backbone** (`AxQM/Concrete/GroverSearchIterations.lean`, matrices over `ℂ²`
  and real trigonometry):
  * `Concrete.groverIteration_pow_mulVec_groverState` — **N&C Eq. 6.12**: `k` iterations rotate the
    starting state to `cos((2k+1)θ/2)|α⟩ + sin((2k+1)θ/2)|β⟩`;
  * `Concrete.grover_multipleSolutions_success` — **N&C Eqs. 6.15–6.17**: there is an `R` with
    `sin²((2R+1)θ/2) ≥ ½` and `R ≤ (π/4)√(N/M)`.

* **Physical (measurement) grounding** (`AxQM/Postulates/API/GroverSearchMeasurement.lean`):
  * `groverFinalState θ R` — the state `Gᴿ|ψ⟩` after `R` iterations, as a genuine `PureState`;
  * `groverSolutionMeasurement` — the projective `Measurement` of the reduced qubit in the
    `{|α⟩, |β⟩}` basis (outcome `1 = |β⟩` = "a solution was found");
  * `bornProb_groverSolutionMeasurement_solution` — the Born rule (Postulate 3) applied to the final
    state: `p(solution) = sin²((2R+1)θ/2)`.

## The formalisation (this file)

`grover_multipleSolutions_bornProb_solution_ge_half` states, in terms of `Measurement.bornProb`,
`groverFinalState` and `groverSolutionMeasurement`, that for an `M`-solution problem
(`1 ≤ M ≤ N/2`), there is a number of Grover iterations `R` such that **measuring** `Gᴿ|ψ⟩` in the
computational basis yields a solution with **Born probability at least `½`**, and `R ≤ (π/4)√(N/M)`
— the `O(√(N/M))` quantum search of Exercise 6.4. It combines the analytic success bound with the
Born-rule identity above.
-/

open scoped InnerProductSpace

namespace AxQM

/-- **Nielsen & Chuang, Exercise 6.4 — the multiple-solution quantum search succeeds with
probability `≥ ½` in `O(√(N/M))` steps.** For an `M`-solution search problem with Grover rotation
angle `θ` given by `sin(θ/2) = √(M/N)` (N&C Eq. 6.10) and `1 ≤ M ≤ N/2` (encoded as `0 < M`,
`2M ≤ N`, and `0 < θ ≤ π/2`), there is a number of Grover iterations `R` such that:

* **success** — measuring the state `Gᴿ|ψ⟩` (the register after `R` Grover iterations, prepared as
  in steps 1–3 of the algorithm) in the computational basis returns a *solution* (the `|β⟩`
  outcome) with Born probability at least one half; and
* **cost** — only `R ≤ (π/4)√(N/M) = O(√(N/M))` iterations, hence oracle calls, are used — the
  quadratic speedup over the `O(N/M)` classical cost.

This is the physical (Born-rule) content of the search algorithm's measurement step (step 4),
the success probability is a genuine `Measurement.bornProb`
of a genuine `PureState`, `sin²((2R+1)θ/2)` by N&C Eq. 6.12, which the analytic bound
`Concrete.grover_multipleSolutions_success` drives above `½`. -/
theorem grover_multipleSolutions_bornProb_solution_ge_half
    (N M θ : ℝ) (hM : 0 < M) (hMN : 2 * M ≤ N)
    (hθ0 : 0 < θ) (hθ2 : θ ≤ Real.pi / 2)
    (hsin : Real.sin (θ / 2) = Real.sqrt (M / N)) :
    ∃ R : ℕ, (1 : ℝ) / 2 ≤ groverSolutionMeasurement.bornProb (groverFinalState θ R).toState 1
      ∧ (R : ℝ) ≤ Real.pi / 4 * Real.sqrt (N / M) := by
  obtain ⟨R, hsucc, hcount⟩ :=
    Concrete.grover_multipleSolutions_success N M θ hM hMN hθ0 hθ2 hsin
  refine ⟨R, ?_, hcount⟩
  rw [bornProb_groverSolutionMeasurement_solution]
  exact hsucc

end AxQM
