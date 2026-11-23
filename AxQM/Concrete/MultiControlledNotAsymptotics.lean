/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledNotCircuit
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-!
# Concrete: the `Cⁿ(X)` gate count is `O(n²)` (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for an `O(n²)`-gate no-work-qubit circuit
implementing the `n`-controlled `NOT` `Cⁿ(X)`. `Concrete/MultiControlledNotCircuit.lean`
builds that circuit (`exists_mcNotCircuit`) with its length bounded by the explicit recurrence
`mcNotGateBound`, satisfying `T(k) = 1` for `k ≤ 2` and `T(k) = 2 T(⌈k/2⌉) + 2 T(⌊k/2⌋+1)` for
`k ≥ 3`. This file proves the `O(n²)` reading of that bound: `mcNotGateBound n =O[atTop] n²`
(`mcNotGateBound_isBigO_sq`), the asymptotic content of the exercise's gate count.

## The corrected-bound induction

The recurrence is the *critical* case of the master theorem (`a = 4`, `b = 2`,
`log_b a = 2`), so `mcNotGateBound n = Θ(n²)` but **no bound of the form `T(k) ≤ C·k²` closes under
naive strong induction**: for even `k = 2j` the step gives
`2 T(j) + 2 T(j+1) ≤ 2·C j² + 2·C (j+1)² = C·k² + C·(2k + 2) > C·k²`, and scaling `C` cannot absorb
the linear excess (it cancels off the leading term). The slack that makes the bound true lives in
the small base cases (`T(2) = 1 ≪ 2²`).

We therefore carry a linear correction: `mcNotGateBound_add_four_mul_le` proves the *additive* bound
`T(k) + 4k ≤ 2 k²` for `k ≥ 3`. Now the step closes with room to spare — even
`2 T(j) + 2 T(j+1) + 8j ≤ (4j² - 8j) + (4j² - 4) + 8j = 8j² - 4 ≤ 8j²`, odd similarly — but the
correction `2k² - 4k` is *violated* below `k = 3` (`T(2) = 1 > 2·2² - 4·2 = 0`), so the two
smallest recursive arguments `k = 3, 4` (whose halves reach `2`) are discharged as explicit base
cases and the inductive step runs only for `k ≥ 5`, where both halves are `≥ 3` and the induction
hypothesis applies. `mcNotGateBound_le` then reads off `T(k) ≤ 2 k²`, cast to `ℝ` for the `IsBigO`.

Everything here is `ℕ`/`ℝ` asymptotics (no quantum object at all — only the gate-count function
`mcNotGateBound`).
-/

namespace AxQM.Concrete

open Filter Asymptotics

/-- **The corrected `O(n²)` bound on the gate-count recurrence**, in additive form to avoid `ℕ`
subtraction: `mcNotGateBound k + 4 k ≤ 2 k²` for every `k ≥ 3`. The linear `+4k` correction is what
lets the halving step `T(k) = 2 T(⌈k/2⌉) + 2 T(⌊k/2⌋+1)` close under strong induction — a bare
`T(k) ≤ C k²` cannot, as the master theorem is at its critical case here. The correction fails
below `k = 3`, so the two smallest recursive cases `k = 3, 4` are explicit base cases and the step
runs for `k ≥ 5` (both halves `≥ 3`). -/
theorem mcNotGateBound_add_four_mul_le :
    ∀ k, 3 ≤ k → mcNotGateBound k + 4 * k ≤ 2 * k ^ 2 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro hk
    rcases Nat.lt_or_ge k 5 with h5 | h5
    · -- Base cases `k = 3, 4`: the halving of `k` reaches `2`, where the correction is violated,
      -- so we evaluate `mcNotGateBound` directly.
      have h2 : mcNotGateBound 2 = 1 := mcNotGateBound_of_le (by norm_num)
      have h3 : mcNotGateBound 3 = 4 := by
        rw [mcNotGateBound_of_ge (by norm_num)]; norm_num [h2]
      have h4 : mcNotGateBound 4 = 10 := by
        rw [mcNotGateBound_of_ge (by norm_num)]; norm_num [h2, h3]
      interval_cases k
      · rw [h3]; norm_num
      · rw [h4]; norm_num
    · -- Inductive step `k ≥ 5`: both halves are `≥ 3`, so the induction hypothesis applies to each.
      rw [mcNotGateBound_of_ge (by omega)]
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · -- `k = j + j` even: halves are `j` and `j + 1`.
        have hk1 : (k + 1) / 2 = j := by omega
        have hk2 : k / 2 + 1 = j + 1 := by omega
        have h1 := IH j (by omega) (by omega)
        have h2 := IH (j + 1) (by omega) (by omega)
        rw [hk1, hk2]
        subst hj
        nlinarith [h1, h2]
      · -- `k = 2 j + 1` odd: both halves equal `j + 1`.
        have hk1 : (k + 1) / 2 = j + 1 := by omega
        have hk2 : k / 2 + 1 = j + 1 := by omega
        have h2 := IH (j + 1) (by omega) (by omega)
        rw [hk1, hk2]
        subst hj
        nlinarith [h2]

/-- The gate-count recurrence is bounded by `2 k²`: `mcNotGateBound k ≤ 2 k²` for `k ≥ 3`. This is
the `ℕ` inequality underlying the `O(n²)` statement, read off from the corrected additive bound
`mcNotGateBound_add_four_mul_le`. -/
theorem mcNotGateBound_le {k : ℕ} (hk : 3 ≤ k) : mcNotGateBound k ≤ 2 * k ^ 2 := by
  have := mcNotGateBound_add_four_mul_le k hk
  omega

/-- **N&C Exercise 4.29, the `O(n²)` gate count.** The gate-count recurrence `mcNotGateBound` of the
recursive no-work-qubit `Cⁿ(X)` circuit is `O(n²)`: `mcNotGateBound n =O[atTop] n²`. Together with
`exists_mcNotCircuit` (a circuit of length `≤ mcNotGateBound |S|`), this is the exercise's claim
that `Cⁿ(X)` is implementable with `O(n²)` `Toffoli`/`CNOT`/single-qubit gates. -/
theorem mcNotGateBound_isBigO_sq :
    (fun n : ℕ => (mcNotGateBound n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ 2 := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact_mod_cast mcNotGateBound_le hn

/-- **N&C Exercise 4.29, the `O(n²)` total gate count of the tight-register `Cⁿ(X)` circuit.** The
two elementary-gate counts of the Barenco no-work-qubit unfolding of `Cⁿ(X)` on exactly `n + 1`
wires (`AxQM.cnx_circuitBudget`, `n = k + 1`) — at most `8k(k+1)+2` `≤ 2`-control gates
(`Toffoli`/`CNOT`/`NOT`) and at most `2k+3` single-qubit gates — sum to `(8k(k+1)+2) + (2k+3)`, a
quadratic in the control count, so their total is `O(n²)`:

`(fun k => (8k(k+1)+2)+(2k+3)) =O[atTop] (fun k => k²)`.

This is the pure `ℕ→ℝ` asymptotic reading Exercise 4.29 asks for (no quantum object — only the
gate-count polynomial; compare `mcNotGateBound_isBigO_sq`). The bound `8k²+10k+5 ≤ 23 k²` for
`k ≥ 1` closes it directly. -/
theorem barencoGateBudget_isBigO_sq :
    (fun k : ℕ => (((8 * k * (k + 1) + 2) + (2 * k + 3) : ℕ) : ℝ)) =O[atTop]
      fun k : ℕ => (k : ℝ) ^ 2 := by
  refine IsBigO.of_bound 23 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  push_cast
  have hsq : (0 : ℝ) ≤ ((n : ℝ) - 1) * (n : ℝ) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [hn', hsq]

end AxQM.Concrete
