/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CouplingHamiltonian
import AxQM.Postulates.API.SubsetUniformSuperposition

/-!
# Nielsen & Chuang, Exercise 6.12 (alternative Hamiltonian for quantum search)

*(N&C p. 261.)*

For H=|x><psi|+|psi><x|: (1) show O(1) time to rotate |psi> to |x>; (2) simulate H and count oracle
calls.

Here `|x⟩ = quditBasis x` is the (unique) search solution — a computational-basis state of the
register `qudit d` (`N = d` items) — and `|ψ⟩ = uniformSuperposition d = N⁻¹ᐟ² ∑_k |k⟩` the uniform
superposition, exactly as in the §6.2 continuous-time search. The overlap is
`α = ⟨x, ψ⟩ = 1/√N`.

## Part (1) — the `O(1)`-time rotation *(formalised)*

The alternative Hamiltonian is the **off-diagonal coupling** `H = |x⟩⟨ψ| + |ψ⟩⟨x|`, in contrast to
the §6.2 *projector* Hamiltonian `|x⟩⟨x| + |ψ⟩⟨ψ|`. Its eigenvectors are still `x ± ψ`, but with
eigenvalues `1 + α` and `α − 1` (versus `1 ± α`); decomposing `ψ = ½(x + ψ) − ½(x − ψ)` and
evolving gives (`PureState.couplingHamiltonian_propagator_op_apply`)

`exp(−iHt)|ψ⟩ = e^{−iαt}(cos t · |ψ⟩ − i sin t · |x⟩)`.

The rotation frequency is `1` — **not** `α = 1/√N` — so `|ψ⟩` reaches `|x⟩` (up to a global phase)
at the **constant** time `t = π/2`, *independent of `N`*: this is the `O(1)`-time rotation. (Compare
the §6.2 projector Hamiltonian, whose frequency is `α`, giving the observation time `π/(2α) = π√N/2
= O(√N)`; the alternative Hamiltonian's coupling makes the *evolution* itself fast.)

* `alternativeSearchHamiltonian x` — the Hamiltonian `H = |x⟩⟨ψ| + |ψ⟩⟨x|` (eq. 6.29) as an
  `Observable`.
* `alternativeSearchHamiltonian_rotates_uniform_to_solution` — evolving `|ψ⟩` under `H` for the
  constant time `t = π/2` produces the solution state `|x⟩` (up to a global phase): the state
  coincides with `|x⟩`.
* `alternativeSearchHamiltonian_measure_yields_solution` — a computational-basis measurement of the
  rotated state returns the solution `x` with probability `1`.

## Part (2) — the simulation *(proved)* and its oracle cost *(a signed cost model)*

Part (2) has two parts of different formal status, and it is honest to separate them.

*How the simulation is performed — **proved**.* `H` is the real-linear combination of three
projector Hamiltonians (`PureState.couplingHamiltonian_op_eq_projector_combination`, in
`AxQM/Postulates/API/CouplingHamiltonian.lean`):

`H = |x+ψ⟩⟨x+ψ| − |x⟩⟨x| − |ψ⟩⟨ψ|`.

Each summand is a projector Hamiltonian `exp(−i|·⟩⟨·|Δt)` that Exercise 6.7 simulates by an explicit
oracle circuit (Figures 6.4/6.5), so `exp(−iHt)` is simulated by *symmetric (Strang) Trotter
composition* (N&C §4.7, eq. 4.106) of those circuits. This is formalised, not merely described:

* `alternativeSearchHamiltonianSimulation x Δt` — the concrete symmetric-Trotter simulation step
  `U_Δt` of `H`, the palindromic product of the three projector-Hamiltonian propagators
  (`PureState.couplingSymmTrotterStep`).
* `alternativeSearchHamiltonian_simulation_gateError_pow_le` — its **accuracy**, N&C Exercise 4.50
  eq. 4.107 in Box 4.1's error notation: `E(U_Δtᵐ, exp(−2imH·Δt)) ≤ m·α·Δt³` for some `α ≥ 0` and
  every `Δt ∈ [0, 1]`. Running the step `m` times drifts from the exact evolution by at most `m`
  times the (third-order) per-step error — the quantitative content of "how the simulation is
  performed".

*The oracle count `O(√N)` — **a signed modelling assumption**, not a library-derived theorem.* The
literal **number of oracle calls** is an analysis-level resource estimate (exactly as in N&C's
prose). The library has an elementary-gate / oracle budget apparatus (`Core.CircuitBudget`), but it
counts the gates of a *concrete* qubit circuit; turning this count into a `CircuitBudget` theorem
would require building the concrete oracle circuit for the coupling-projector reflection about
`|x+ψ⟩` — an amplitude amplification, itself a full quantum-search development that would
essentially re-derive Grover — beyond the analysis-level scope of this exercise. So, matching the
accepted sibling Exercise 6.8, the count is recorded as a **signed cost model** over raw `ℝ`/`ℕ` in
`AxQM/Concrete/AlternativeSearchSimulationScaling.lean`, with its two modelling inputs named
exactly:

* **(A1) per-step coupling cost.** Each Trotter step must reflect about the coupled state
  `|x+ψ⟩ ∝ |x⟩ + |ψ⟩`, whose `Θ(1)` amplitude on the **unknown** solution `|x⟩` must be prepared
  from the accessible `|ψ⟩` — amplitude `α = ⟨x,ψ⟩ = 1/√N`, the *proved* overlap
  `uniformSuperposition_inner_quditBasis` — by amplitude amplification, taken to cost `Θ(1/α)`
  oracle calls per step.
* **(A2) step count.** The `O(1)`-time evolution of part (1) is simulated to the constant accuracy
  needed for high success probability by `O(1)` Trotter steps.

Under (A1)+(A2) the modelled count is `(steps) × (cost per step) = Θ(1) × Θ(1/α) = Θ(√N)`:

* `Concrete.altSearchSimOracleCalls b N = b·√N` (`b > 0` absorbing both `O(1)` factors), and
  `altSearchSimOracleCalls_isTheta` — it scales as `Θ(√N)`, the same asymptotic cost as the original
  quantum search (and its `Ω(√N)` lower bound).
* `Concrete.altSearchSimOracleCalls_atTop` — the modelled count is *unbounded* in `N`, while the
  (proved) evolution time `altSearchEvolutionTime = π/2` is a fixed constant: N&C's point that the
  `O(1)` evolution time of part (1) **buys nothing** once the simulation is counted.

*Why the `√N` is per-step (A1), and why Exercise 6.8's mechanism does not transfer.* For the §6.2
*projector* Hamiltonian the `√N` is the slow total evolution time `t = Θ(√N)`
(`Concrete.searchSimTime`), and the count is that many `O(1)`-cost steps. That accounting gives
`O(1)` here — the alternative Hamiltonian's evolution time is `Θ(1)` (part (1)), needing only `O(1)`
steps (A2) — which is impossible (it would beat the `Ω(√N)` search bound). So the `√N` cannot come
from the step count and must enter *per step*: it is assumption (A1), the amplitude-amplification
cost of coupling to the unknown solution. This is the modelling rationale for (A1); the `Concrete`
file's docstring signs the full chain.

## Supporting results

The coupling Hamiltonian `PureState.couplingHamiltonian`, the Trotter step
`PureState.couplingSymmTrotterStep` and their evolution / error theorems are in
`AxQM/Postulates/API/CouplingHamiltonian.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {d : ℕ}

/-- **The alternative search Hamiltonian** `H = |x⟩⟨ψ| + |ψ⟩⟨x|` (Nielsen & Chuang, Exercise 6.12,
eq. 6.29), for a search space `qudit d` (`N = d` items) with the (unique) solution `x`:
`|x⟩ = quditBasis x` is the solution computational-basis state and `|ψ⟩ = uniformSuperposition d`
the uniform superposition. It is the off-diagonal coupling of `|x⟩` and `|ψ⟩` — the abstract
`PureState.couplingHamiltonian` of `AxQM/Postulates/API/CouplingHamiltonian.lean` instantiated at
`a := |x⟩`, `ψ := |ψ⟩` — in contrast to the §6.2 projector Hamiltonian `|x⟩⟨x| + |ψ⟩⟨ψ|`. -/
def alternativeSearchHamiltonian [NeZero d] (x : Fin d) : Observable (qudit d) :=
  (quditBasis x).couplingHamiltonian (uniformSuperposition d)

/-- **Part (1): the alternative search Hamiltonian rotates `|ψ⟩` onto the solution in `O(1)` time.**
Evolving the uniform superposition `|ψ⟩` under `H = |x⟩⟨ψ| + |ψ⟩⟨x|` for the **constant** time
`t = π/2` produces the solution state `|x⟩` (up to a global phase): the density operators coincide,
`(exp(−iH(π/2))|ψ⟩ as a state) = |x⟩`. The observation time `π/2` is *independent of the register
size `N = d`* — this is the `O(1)`-time rotation of Nielsen & Chuang, Exercise 6.12(1). Proved by
instantiating the abstract engine `PureState.couplingHamiltonian_reaches_target` at `a := |x⟩`,
`ψ := |ψ⟩`, with the real overlap `⟨x, ψ⟩ = 1/√N` (`uniformSuperposition_inner_quditBasis`). -/
theorem alternativeSearchHamiltonian_rotates_uniform_to_solution [NeZero d] (x : Fin d) :
    (((alternativeSearchHamiltonian x).propagator 1 0 (Real.pi / 2)).evolvePure
        (uniformSuperposition d)).toState
      = (quditBasis x).toState := by
  have hoverlap : inner ℂ (quditBasis x).vec (uniformSuperposition d).vec
      = (((Real.sqrt d)⁻¹ : ℝ) : ℂ) := by
    rw [uniformSuperposition_inner_quditBasis, Complex.ofReal_inv]
  exact (quditBasis x).couplingHamiltonian_reaches_target (uniformSuperposition d) hoverlap

/-- **Part (1), completed: measuring the rotated state returns the solution with probability one.**
After evolving `|ψ⟩` under `H = |x⟩⟨ψ| + |ψ⟩⟨x|` for `t = π/2`, a computational-basis measurement
returns the solution `x` with probability `1`: the alternative-Hamiltonian evolution *solves* the
search problem. Because the rotated state is `|x⟩` up to a global phase (invisible to the Born rule;
`alternativeSearchHamiltonian_rotates_uniform_to_solution`) and `⟨x, x⟩ = 1`, the Born probability
is `‖⟨x, x⟩‖² = 1`. -/
theorem alternativeSearchHamiltonian_measure_yields_solution [NeZero d] (x : Fin d) :
    (quditMeasurement d).bornProb
        ((((alternativeSearchHamiltonian x).propagator 1 0 (Real.pi / 2)).evolvePure
          (uniformSuperposition d)).toState) x = 1 := by
  rw [alternativeSearchHamiltonian_rotates_uniform_to_solution,
    bornProb_quditMeasurement_toState, quditBasis_inner, ite_eq_left rfl, norm_one, one_pow]

/-- **Part (2): the alternative search Hamiltonian is simulated by a symmetric Trotter product**
(Nielsen & Chuang, Exercise 6.12(2), "explain how a quantum simulation of `H` may be performed").
The concrete quantum simulation of `H = |x⟩⟨ψ| + |ψ⟩⟨x|`: the symmetric (Strang) Trotter step `U_Δt`
(N&C eq. 4.106) of the propagators of the three projector Hamiltonians of the decomposition
`H = |x+ψ⟩⟨x+ψ| − |x⟩⟨x| − |ψ⟩⟨ψ|`, each simulated by an explicit Exercise 6.7 oracle circuit
(Figures 6.4/6.5). It is the abstract engine `PureState.couplingSymmTrotterStep` at `a := |x⟩`,
`ψ := |ψ⟩`. Its accuracy is `alternativeSearchHamiltonian_simulation_gateError_pow_le`. -/
def alternativeSearchHamiltonianSimulation [NeZero d] (x : Fin d) (Δt : ℝ) : Evolution (qudit d) :=
  (quditBasis x).couplingSymmTrotterStep (uniformSuperposition d) Δt

/-- **Part (2): accuracy of the alternative-Hamiltonian simulation** (Nielsen & Chuang,
Exercise 6.12(2), via Exercise 4.50 eq. 4.107). Running the symmetric-Trotter simulation
`alternativeSearchHamiltonianSimulation x` for `m` steps approximates the exact evolution
`exp(−2imH·Δt)` under the alternative search Hamiltonian with an error growing at most linearly in
the step count: `E(U_Δtᵐ, exp(−2imH·Δt)) ≤ m·α·Δt³` for some `α ≥ 0` and every `Δt ∈ [0, 1]`, in
Box 4.1's gate-error notation `E(U,V) = ‖U − V‖`. This is the *accuracy* half of "explain how a
quantum simulation of `H` may be performed, and determine the number of oracle calls" — the
*count* half is the `Θ(√N)` **signed cost model** `Concrete.altSearchSimOracleCalls_isTheta` (module
docstring). Proved by instantiating `PureState.couplingSymmTrotterStep_gateError_pow_le` at
`a := |x⟩`, `ψ := |ψ⟩`. -/
theorem alternativeSearchHamiltonian_simulation_gateError_pow_le [NeZero d] (x : Fin d) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ (m : ℕ) (Δt : ℝ), 0 ≤ Δt → Δt ≤ 1 →
      (alternativeSearchHamiltonianSimulation x Δt ^ m).gateError
          ((alternativeSearchHamiltonian x).propagator 1 0 (2 * (m : ℝ) * Δt))
        ≤ (m : ℝ) * α * Δt ^ 3 :=
  (quditBasis x).couplingSymmTrotterStep_gateError_pow_le (uniformSuperposition d)

end AxQM
