/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SearchSimulationScaling

/-!
# Nielsen & Chuang, Exercise 6.8 (oracle-call scaling of the search-Hamiltonian simulation)

*(N&C p. 258.)*

For accuracy O(dt^r) show oracle calls to simulate H scale as O(N^{r/2(r-1)}).

Quantum search is presented in §6.2 as the simulation of the Hamiltonian `H = |x⟩⟨x| + |ψ⟩⟨ψ|`
(Eq. 6.18): evolving under `H` rotates `|ψ⟩` to `|x⟩` in time `t = π√N/2 = Θ(√N)`, and one simulates
`H` by alternately simulating `H₁ = |x⟩⟨x|` and `H₂ = |ψ⟩⟨ψ|` for short increments `Δt` (Figures
6.4/6.5). Exercise 6.8 is the resource estimate for that simulation: an `O(Δtʳ)`-accurate step,
run over `t/Δt` steps, accumulates error `O(t·Δtʳ⁻¹)`; holding this to a constant ("reasonable
accuracy") forces `Δt = Θ(N^{−1/2(r−1)})`, giving `t/Δt = Θ(N^{r/2(r−1)})` oracle calls.

The exercise's content is a purely asymptotic (complexity) statement about real-valued cost
functions — the step size `Δt`, the accumulated error, and the oracle count as functions of the
search-space size `N`. There is no quantum object in the proposition, only the scaling of these
real quantities. Compare Problem 5.4 (the improved factoring cost) and Exercise 4.29 (the `O(n²)`
gate count of `Cⁿ(X)`).

## The formalisation

`AxQM/Concrete/SearchSimulationScaling.lean` (namespace `AxQM.Concrete`), for a
search space of size `N`, a simulation-accuracy order `r > 1`, and a positive `O(1)` budget constant
`b` (absorbing the error budget, the per-step-error coefficient, and the total-time constant):

* `searchSimTime`, `searchSimStepSize`, `searchSimOracleCalls`, `searchSimCumulativeError`,
  `searchSimExponent` — the objects of the estimate: the total time `t = √N`, the balanced step
  `Δt = b·N^{−1/2(r−1)}`, the oracle count `t/Δt`, the accumulated error `t·Δtʳ⁻¹`, and the
  exponent `r/2(r−1)`.
* `searchSimCumulativeError_eq` — the balanced step holds the cumulative error to the constant
  `b^{r−1}`, independent of `N` (the "reasonable accuracy" condition).
* `searchSimOracleCalls_eq` — **the exact count**:
  `searchSimOracleCalls b r N = b⁻¹ · N^{r/2(r−1)}`.
* `searchSimOracleCalls_isTheta` / `searchSimOracleCalls_isBigO` — **Exercise 6.8**: the oracle
  count is `Θ(N^{r/2(r−1)})`, in particular the `O(N^{r/2(r−1)})` the exercise asks for.
* `searchSimExponent_eq` (`r/2(r−1) = 1/2 + 1/2(r−1)`) and `searchSimExponent_tendsto_half`
  (`r/2(r−1) → 1/2` as `r → ∞`) — the exercise's closing note.
-/
