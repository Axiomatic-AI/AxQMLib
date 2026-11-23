/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic

/-!
# Concrete: oracle-call scaling of the search-Hamiltonian simulation (N&C Exercise 6.8)

Nielsen & Chuang, Exercise 6.8 (p. 258): quantum search viewed as the simulation of the Hamiltonian
`H = |x⟩⟨x| + |ψ⟩⟨ψ|` (Eq. 6.18) by alternately simulating `H₁ = |x⟩⟨x|` and `H₂ = |ψ⟩⟨ψ|` in short
increments `Δt`.

For accuracy O(dt^r) show oracle calls to simulate H scale as O(N^{r/2(r-1)}).

## The scaling argument (N&C p. 258)

The book fixes the pieces of the estimate as follows and this file formalises exactly that chain:

* **Total time `t = Θ(√N)`.** Evolving under `H` rotates `|ψ⟩` to `|x⟩` in time `t = π√N/2`
  (the paragraph before Eq. 6.24); the leading constant is immaterial to the `O(·)` claim, so we
  take the representative `t = √N` (`searchSimTime`).
* **Number of steps `= t/Δt`.** Each simulation step advances the evolution by `Δt`, so a run of
  total time `t` uses `t/Δt = Θ(√N/Δt)` steps — and, since each step costs `O(1)` oracle calls
  (Figures 6.4/6.5, Exercise 6.7), that many oracle calls (`searchSimOracleCalls`).
* **Cumulative error `= t·Δtʳ⁻¹`.** A step accurate to `O(Δtʳ)` accumulates, over the `t/Δt` steps,
  a total error `O(Δtʳ · t/Δt) = O(t·Δtʳ⁻¹)` (`searchSimCumulativeError`).
* **Balancing the error to a constant.** "Reasonable accuracy" means the cumulative error is
  `O(1)`; holding it to a fixed positive budget forces `Δt = Θ(N^{−1/2(r−1)})`. We write this
  balanced step as `searchSimStepSize b r`, with `b > 0` the single free `O(1)` constant absorbing
  the error budget, the per-step-error coefficient, and the total-time constant. With this choice
  the cumulative error is exactly the constant `b^{r−1}`, independent of `N`
  (`searchSimCumulativeError_eq`).
* **The count.** Substituting the balanced `Δt` into `t/Δt` gives the oracle-call count
  `b⁻¹ · N^{r/2(r−1)}` exactly (`searchSimOracleCalls_eq`), hence `Θ(N^{r/2(r−1)})` — in
  particular the `O(N^{r/2(r−1)})` of the exercise (`searchSimOracleCalls_isBigO`). The exponent
  `searchSimExponent r = r/2(r−1) = 1/2 + 1/2(r−1)` (`searchSimExponent_eq`) decreases to `1/2` as
  `r → ∞` (`searchSimExponent_tendsto_half`), the book's closing note.

Everything here is `ℕ`/`ℝ` asymptotics of real-valued cost functions (there is no quantum object
in the statement, only the step size, the oracle count, and the accumulated error as functions of
the search-space size `N`). Compare `AxQM/Concrete/FactoringOpCountAsymptotics.lean`
(N&C Problem 5.4) and `AxQM/Concrete/MultiControlledNotAsymptotics.lean`. The statement of
Exercise 6.8 is in `AxQM/NC/Ch6/Exercise6_8.lean`.
-/

namespace AxQM.Concrete

open Filter Asymptotics
open scoped Topology

/-- The total simulation time to rotate `|ψ⟩` to `|x⟩` under the search Hamiltonian `H` (N&C
Eq. 6.18): `t = π√N/2 = Θ(√N)` for a search space of size `N`. We take the representative `t = √N`;
the leading constant is an `O(1)` factor that does not affect the `O(·)` scaling of Exercise 6.8. -/
noncomputable def searchSimTime (N : ℕ) : ℝ := Real.sqrt N

/-- The simulation step size `Δt` that balances the cumulative error of an `O(Δtʳ)`-accurate
simulation of the search Hamiltonian to a fixed (`O(1)`) budget: `Δt = b · N^{−1/2(r−1)}` (N&C
p. 258, `Δt = Θ(N^{−1/2(r−1)})`). The positive constant `b` is the single free `O(1)` knob absorbing
the error budget, the per-step-error coefficient, and the total-time constant. -/
noncomputable def searchSimStepSize (b r : ℝ) (N : ℕ) : ℝ :=
  b * (N : ℝ) ^ (-(1 / (2 * (r - 1))))

/-- The number of oracle calls used to simulate the search Hamiltonian `H` with the balanced step
`searchSimStepSize b r`: the number of simulation steps `t/Δt` (N&C p. 258), each of which costs
`O(1)` oracle calls (Figures 6.4/6.5). -/
noncomputable def searchSimOracleCalls (b r : ℝ) (N : ℕ) : ℝ :=
  searchSimTime N / searchSimStepSize b r N

/-- The cumulative error of simulating the search Hamiltonian for total time `t = searchSimTime N`
using `t/Δt` steps, each accurate to `O(Δtʳ)`: `error = (t/Δt) · Δtʳ = t · Δtʳ⁻¹` (N&C p. 258). -/
noncomputable def searchSimCumulativeError (b r : ℝ) (N : ℕ) : ℝ :=
  searchSimTime N * (searchSimStepSize b r N) ^ (r - 1)

/-- The exponent of `N` in the Exercise 6.8 oracle-call count: `r/2(r−1)`, as a function of the
simulation-accuracy order `r`. -/
noncomputable def searchSimExponent (r : ℝ) : ℝ := r / (2 * (r - 1))

/-- The balanced simulation step size is positive (for a positive budget constant `b` and a
nonempty search space `N ≥ 1`), so it may be divided by. -/
theorem searchSimStepSize_pos {b r : ℝ} (hb : 0 < b) {N : ℕ} (hN : 1 ≤ N) :
    0 < searchSimStepSize b r N := by
  have hpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  unfold searchSimStepSize
  positivity

/-- **The exponent decomposition.** `r/2(r−1) = 1/2 + 1/2(r−1)`: the Exercise 6.8 exponent is `1/2`
plus a positive correction that vanishes as the simulation-accuracy order `r → ∞`. -/
theorem searchSimExponent_eq {r : ℝ} (hr : 1 < r) :
    searchSimExponent r = 1 / 2 + 1 / (2 * (r - 1)) := by
  have hr1 : r - 1 ≠ 0 := by linarith
  unfold searchSimExponent
  field_simp
  ring

/-- **The cumulative error is held to a constant.** With the balanced step
`searchSimStepSize b r`, the cumulative error of the `O(Δtʳ)`-accurate simulation is exactly the
constant `b^{r−1}`, independent of the search-space size `N` (N&C p. 258: the step is chosen so the
error is `O(1)`). This certifies that the balanced step really does deliver the "reasonable
accuracy" of the exercise. -/
theorem searchSimCumulativeError_eq {b r : ℝ} (hb : 0 < b) (hr : 1 < r) {N : ℕ} (hN : 1 ≤ N) :
    searchSimCumulativeError b r N = b ^ (r - 1) := by
  have hpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hr1 : r - 1 ≠ 0 := by linarith
  unfold searchSimCumulativeError searchSimStepSize searchSimTime
  rw [Real.mul_rpow hb.le (Real.rpow_nonneg hpos.le _), ← Real.rpow_mul hpos.le,
    show -(1 / (2 * (r - 1))) * (r - 1) = -(1 / 2) by field_simp,
    Real.sqrt_eq_rpow, mul_left_comm, ← Real.rpow_add hpos]
  norm_num

/-- **Exercise 6.8, the exact count.** With the balanced step `searchSimStepSize b r`, the number of
oracle calls used to simulate the search Hamiltonian `H` to reasonable accuracy is exactly
`b⁻¹ · N^{r/2(r−1)}` — the number of steps `t/Δt` after substituting `t = √N` and
`Δt = b · N^{−1/2(r−1)}`. -/
theorem searchSimOracleCalls_eq {b r : ℝ} (hb : 0 < b) (hr : 1 < r) {N : ℕ} (hN : 1 ≤ N) :
    searchSimOracleCalls b r N = b⁻¹ * (N : ℝ) ^ searchSimExponent r := by
  have hpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hr1 : r - 1 ≠ 0 := by linarith
  unfold searchSimOracleCalls searchSimStepSize searchSimTime searchSimExponent
  rw [Real.sqrt_eq_rpow,
    show r / (2 * (r - 1)) = (1 / 2 : ℝ) - (-(1 / (2 * (r - 1)))) by field_simp; ring,
    Real.rpow_sub hpos]
  field_simp

/-- **Exercise 6.8, asymptotic form.** The number of oracle calls used to simulate the search
Hamiltonian `H` to reasonable accuracy scales as `Θ(N^{r/2(r−1)})`: the count is `b⁻¹` times
`N^{r/2(r−1)}` (`searchSimOracleCalls_eq`), a nonzero constant multiple, so it is `Θ` of the pure
power — a *tight* version of the exercise's `O(N^{r/2(r−1)})`. -/
theorem searchSimOracleCalls_isTheta {b r : ℝ} (hb : 0 < b) (hr : 1 < r) :
    (fun N : ℕ => searchSimOracleCalls b r N) =Θ[atTop]
      fun N : ℕ => (N : ℝ) ^ searchSimExponent r := by
  have hev : (fun N : ℕ => searchSimOracleCalls b r N) =ᶠ[atTop]
      fun N : ℕ => b⁻¹ * (N : ℝ) ^ searchSimExponent r := by
    filter_upwards [eventually_ge_atTop 1] with N hN using searchSimOracleCalls_eq hb hr hN
  refine hev.trans_isTheta ?_
  exact (isTheta_refl _ _).const_mul_left (by positivity : b⁻¹ ≠ 0)

/-- **Exercise 6.8, verbatim.** The number of oracle calls required to simulate the search
Hamiltonian `H` to reasonable accuracy is `O(N^{r/2(r−1)})` — the exercise's statement, obtained
from the tight `Θ` bound `searchSimOracleCalls_isTheta`. -/
theorem searchSimOracleCalls_isBigO {b r : ℝ} (hb : 0 < b) (hr : 1 < r) :
    (fun N : ℕ => searchSimOracleCalls b r N) =O[atTop]
      fun N : ℕ => (N : ℝ) ^ searchSimExponent r :=
  (searchSimOracleCalls_isTheta hb hr).isBigO

/-- **Exercise 6.8's closing note.** As the simulation-accuracy order `r` becomes large, the
exponent of `N` in the oracle-call count approaches `1/2`: `searchSimExponent r = r/2(r−1) → 1/2` as
`r → ∞`, recovering the `O(√N)` scaling of the optimal quantum search. -/
theorem searchSimExponent_tendsto_half :
    Tendsto searchSimExponent atTop (𝓝 (1 / 2)) := by
  have h : searchSimExponent =ᶠ[atTop] fun r : ℝ => 1 / 2 + 1 / (2 * (r - 1)) := by
    filter_upwards [eventually_gt_atTop 1] with r hr using searchSimExponent_eq hr
  rw [tendsto_congr' h]
  have hden : Tendsto (fun r : ℝ => 2 * (r - 1)) atTop atTop := by
    have h1 : Tendsto (fun r : ℝ => r - 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-1) tendsto_id
    simpa using h1.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hz : Tendsto (fun r : ℝ => 1 / (2 * (r - 1))) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hden
  simpa using tendsto_const_nhds.add hz

end AxQM.Concrete
