/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic

/-!
# Concrete: oracle-call count of the alternative-Hamiltonian simulation (N&C Exercise 6.12(2))

Nielsen & Chuang, Exercise 6.12 (p. 261): the **alternative** search Hamiltonian
`H = |x⟩⟨ψ| + |ψ⟩⟨x|` (eq. 6.29) rotates the uniform superposition `|ψ⟩` onto the solution `|x⟩` in
**constant** time `t = π/2`, *independent of the search-space size `N`* (part (1); the physics is
`AxQM.alternativeSearchHamiltonian_rotates_uniform_to_solution`). This file addresses
the second half of part (2) — *"determine the number of oracle calls your simulation technique
requires to obtain the solution with high probability"* — the same asymptotic-count register as the
sibling Exercise 6.8 (`Concrete/SearchSimulationScaling.lean`).

For H=|x><psi|+|psi><x|: (1) show O(1) time to rotate |psi> to |x>; (2) simulate H and count
oracle calls.

## What is proved vs. what is a signed modelling assumption

The count below is a **signed cost model**, *not* a library-derived theorem. It is honest to flag
this explicitly, because part (2) has two components of different formal status:

* **Proved.** The overlap `α = ⟨x,ψ⟩ = 1/√N`
  (`AxQM.uniformSuperposition_inner_quditBasis`); the `O(1)` evolution time `t = π/2`
  (part (1)); the simulation *construction* — symmetric-Trotter composition of the three
  projector-Hamiltonian propagators of `H = |x+ψ⟩⟨x+ψ| − |x⟩⟨x| − |ψ⟩⟨ψ|`
  (`AxQM.alternativeSearchHamiltonianSimulation`); and its *accuracy*, the eq.-4.107 error
  bound `E(U_Δtᵐ, exp(−2imHΔt)) ≤ m·α·Δt³`
  (`AxQM.alternativeSearchHamiltonian_simulation_gateError_pow_le`).

* **The signed modelling assumption (this file).** The *literal count of oracle calls* is an
  analysis-level resource estimate, exactly as in N&C's prose. The library has an elementary-gate /
  oracle budget apparatus (`AxQM.CircuitBudget`), but it counts the gates of a *concrete*
  qubit circuit; turning this count into a `CircuitBudget` theorem would require building the
  concrete oracle circuit for the coupling-projector reflection about `|x+ψ⟩` — i.e. an amplitude
  amplification, which is itself a full quantum-search development (and would essentially re-derive
  Grover). That is beyond the analysis-level scope of the exercise, so — matching the accepted
  sibling Exercise 6.8 — the count is recorded here as a **signed cost model** over raw `ℝ`/`ℕ`,
  with its two modelling inputs named exactly:

  * **(A1) per-step coupling cost.** Each Trotter step must reflect about the coupled state
    `|x+ψ⟩ ∝ |x⟩ + |ψ⟩`, which carries a `Θ(1)` amplitude on the **unknown** solution `|x⟩`.
    Preparing such a state from the accessible `|ψ⟩` — whose amplitude on `|x⟩` is only
    `α = 1/√N` — is amplitude amplification; by the standard amplitude-amplification cost this is
    taken to be `Θ(1/α)` oracle calls per step.
  * **(A2) step count.** The `O(1)`-time evolution of part (1) is simulated to the constant accuracy
    needed for high success probability by `O(1)` Trotter steps.

  Under (A1)+(A2) the total count is `(steps) × (cost per step) = Θ(1) × Θ(1/α) = Θ(1/α) = Θ(√N)`.
  The free constant `b : ℝ` below absorbs both `O(1)` factors. The theorems are the *internal
  consequences* of this model.

## Why the count is `Θ(√N)`, and why Exercise 6.8's mechanism does **not** transfer

This is the physical point of the exercise, and it is the reason (A1) — not the step count — carries
the `√N`. For the §6.2 *projector* Hamiltonian `|x⟩⟨x| + |ψ⟩⟨ψ|`, the rotation frequency is the
overlap `α = 1/√N`, so the evolution time is `t = Θ(√N)` (slow); there the count `t/Δt = Θ(√N)`
comes from the *number of steps*, each `O(1)` oracle calls (`Concrete.searchSimOracleCalls`).
Transplanting that accounting to the alternative Hamiltonian would give `O(1)`: its evolution
time is `t = π/2 = Θ(1)` (part (1)), so an `O(1)`-time evolution needs only `O(1)` Trotter steps
— which is (A2). An `O(1)`-oracle-call quantum search is impossible (it would violate the `Ω(√N)`
search lower bound), so the `√N` **cannot** come from the step count and must enter *per step* —
assumption (A1),
the amplitude-amplification cost of coupling to the unknown solution. Hence the `Θ(√N)` total is the
*same* asymptotic cost as the original quantum search (and its `Ω(√N)` lower bound): **the `O(1)`
evolution time of part (1) buys nothing once the simulation is counted**
(`altSearchSimOracleCalls_atTop`: the count is unbounded in `N`, though the evolution time
`altSearchEvolutionTime = π/2` is a fixed constant). This is N&C's own conclusion for the exercise.

## Scope

Everything here is `ℕ`/`ℝ` asymptotics of real-valued cost functions of the search-space size `N`.
Compare `AxQM/Concrete/SearchSimulationScaling.lean` (N&C Exercise 6.8). The statement of
Exercise 6.12 in `AxQM/NC/Ch6/Exercise6_12.lean` cites these declarations in its Part (2), where
the modelling assumption (A1)+(A2) is signed against the proved results listed above.
-/

namespace AxQM.Concrete

open Filter Asymptotics
open scoped Topology

/-- The overlap `α = ⟨x, ψ⟩ = 1/√N` of the solution `|x⟩` with the uniform superposition `|ψ⟩` for a
search space of size `N` (N&C §6.2). This is a **proved** physics quantity — the number
`AxQM.uniformSuperposition_inner_quditBasis` establishes — recorded over raw `ℝ` so the
cost model can refer to it. It is the amplitude of the *unknown* solution in the accessible starting
state, the small number whose inverse sets the per-step oracle cost of coupling to `|x⟩`
(modelling assumption (A1) in the module docstring). -/
noncomputable def altSearchOverlap (N : ℕ) : ℝ := (Real.sqrt N)⁻¹

/-- The evolution time of the alternative search Hamiltonian `H = |x⟩⟨ψ| + |ψ⟩⟨x|`: the **constant**
`t = π/2`, *independent of the search-space size `N`*. This is a **proved** physics quantity — it is
the observation time of part (1) (`alternativeSearchHamiltonian_rotates_uniform_to_solution`)
— recorded here over raw `ℝ` to contrast with the unboundedly growing oracle count
`altSearchSimOracleCalls`. -/
noncomputable def altSearchEvolutionTime : ℝ := Real.pi / 2

/-- **The oracle-call count of the alternative-Hamiltonian simulation — a signed cost model** (N&C
Exercise 6.12(2)). This `def` is *not* derived from the simulation `Evolution`; it is the modelling
estimate `(number of Trotter steps) × (oracle calls per step) = b · (1/α) = b·√N`, under the two
assumptions named in the module docstring: **(A2)** the `O(1)`-time evolution is simulated by `O(1)`
Trotter steps, and **(A1)** each step reflects about the coupled state `|x+ψ⟩` — carrying a `Θ(1)`
amplitude on the unknown `|x⟩` — at the amplitude-amplification cost `Θ(1/α)` oracle calls. Here
`b > 0` is the single free `O(1)` constant absorbing the step count and the amplitude-amplification
constant, and `1/α = √N` is the (proved) inverse overlap `altSearchOverlap`. The correspondence to
the true oracle count is the signed assumption (A1)+(A2); the theorems below are its internal
consequences. -/
noncomputable def altSearchSimOracleCalls (b : ℝ) (N : ℕ) : ℝ := b / altSearchOverlap N

/-- **The model's count in closed form.** Under the cost model, the oracle-call count of the
alternative-Hamiltonian simulation is `b · √N` — the inverse overlap `1/α = √N` (the assumed
amplitude-amplification cost of coupling to the unknown solution, (A1)) times the `O(1)` constant
`b` (absorbing the step count, (A2)). This just unfolds `altSearchSimOracleCalls`. -/
theorem altSearchSimOracleCalls_eq (b : ℝ) (N : ℕ) :
    altSearchSimOracleCalls b N = b * Real.sqrt N := by
  unfold altSearchSimOracleCalls altSearchOverlap
  rw [div_eq_mul_inv, inv_inv]

/-- `√N → ∞` as the search-space size `N → ∞`: the Mathlib fact `Real.tendsto_sqrt_atTop`
precomposed with the `ℕ → ℝ` cast. -/
theorem sqrt_natCast_atTop : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

/-- **Exercise 6.12(2), asymptotic form (a consequence of the cost model).** Under the signed cost
model, the number of oracle calls used to simulate the alternative search Hamiltonian `H` to obtain
the solution with high probability scales as `Θ(√N)`: the modelled count is `b · √N`
(`altSearchSimOracleCalls_eq`), a nonzero constant multiple of `√N`, so it is `Θ` of `√N`. This is
the *same* asymptotic cost as the original quantum search (whose `Ω(√N)` lower bound `√N` also is) —
a *tight* version of the exercise's answer. -/
theorem altSearchSimOracleCalls_isTheta {b : ℝ} (hb : 0 < b) :
    (fun N : ℕ => altSearchSimOracleCalls b N) =Θ[atTop] fun N : ℕ => Real.sqrt N := by
  simp only [altSearchSimOracleCalls_eq]
  exact (isTheta_refl _ _).const_mul_left hb.ne'

/-- **Exercise 6.12(2)'s point: the `O(1)` evolution time buys nothing (a consequence of the cost
model).** Under the signed cost model, the oracle-call count of the alternative-Hamiltonian
simulation is *unbounded* in the search-space size `N` (it grows as `Θ(√N)`,
`altSearchSimOracleCalls_isTheta`) — even though the evolution time `altSearchEvolutionTime = π/2`
is a fixed constant independent of `N` (part (1), proved). So the constant-time rotation of part (1)
provides no asymptotic saving in oracle calls: the simulation still costs `Θ(√N)`, matching the
`Ω(√N)` search lower bound. -/
theorem altSearchSimOracleCalls_atTop {b : ℝ} (hb : 0 < b) :
    Tendsto (fun N : ℕ => altSearchSimOracleCalls b N) atTop atTop := by
  simp only [altSearchSimOracleCalls_eq]
  exact sqrt_natCast_atTop.const_mul_atTop hb

end AxQM.Concrete
