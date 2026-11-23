/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Concrete: the quantum-Fourier-transform gate count `n(n-1)/2 = Θ(n²)` (N&C Exercise 5.6)

The `n`-qubit quantum Fourier transform circuit (Nielsen & Chuang, Figure 5.1) applies, to qubit
`j` (counting `1 … n`), one Hadamard followed by controlled-`R₂ … R_{n-j+1}` phase rotations, i.e.
`n - j` controlled-`Rₖ` gates. The controlled-`Rₖ` gates are the only ones carrying a continuous
phase parameter, hence the only gates that must be implemented to finite **precision**; their total
number is

`∑_{j=1}^{n} (n - j) = (n-1) + (n-2) + ⋯ + 0 = n(n-1)/2`.

This file provides that count as `qftControlledRkCount` and proves it grows quadratically,
`qftControlledRkCount n = Θ(n²)` (`qftControlledRkCount_isTheta_sq`) — the `Θ(n²)` factor of
Exercise 5.6's error scaling `Θ(n²/p(n))`. The companion `qftApproxErrorBound_isTheta` divides the
count by an arbitrary precision denominator `p` to give the full `Θ(n²/p(n))` scaling of the
guaranteed error bound.

Everything here is `ℕ`/`ℝ` arithmetic and asymptotics (there is no quantum object at all, only the
gate-count function), mirroring `AxQM/Concrete/MultiControlledNotAsymptotics.lean` (the `Cⁿ(X)`
`O(n²)` count). The physics
consequence — that this many gates, each to precision `Δ = 1/p(n)`, approximates the QFT unitary to
error `≤ qftControlledRkCount n · Δ` — is `AxQM/NC/Ch5/Exercise5_6.lean`, built on the Box
4.1 chaining bound `Evolution.gateError_prod_le`.
-/

namespace AxQM.Concrete

open Filter Asymptotics

/-- **The controlled-`Rₖ` gate count of the `n`-qubit QFT circuit** (Nielsen & Chuang, Figure 5.1):
`qftControlledRkCount n = n(n-1)/2`. Qubit `j` receives `n - j` controlled phase rotations, and
`∑_{j=1}^{n} (n - j) = n(n-1)/2`; these are the circuit's only gates carrying a continuous phase
parameter (the Hadamards and swaps are exact), hence the only ones implemented to finite precision
in Exercise 5.6. -/
def qftControlledRkCount (n : ℕ) : ℕ := n * (n - 1) / 2

/-- The QFT gate count is the Gauss sum `∑_{j < n} j` — the `∑_{j=1}^{n} (n - j)` of Figure 5.1
reindexed — establishing `qftControlledRkCount n = n(n-1)/2` is the count of controlled rotations,
not an arbitrary closed form (`Finset.sum_range_id`). -/
theorem qftControlledRkCount_eq_sum (n : ℕ) :
    qftControlledRkCount n = ∑ j ∈ Finset.range n, j :=
  (Finset.sum_range_id n).symm

/-- The doubled gate count `2 · qftControlledRkCount n = n(n-1)`; the exact (division-free) form of
`n(n-1)/2`, used for the quadratic lower bound. Since `n(n-1)` is even the halving is exact. -/
theorem two_mul_qftControlledRkCount (n : ℕ) :
    2 * qftControlledRkCount n = n * (n - 1) := by
  have := Finset.sum_range_id_mul_two n
  rw [Finset.sum_range_id] at this
  unfold qftControlledRkCount
  omega

/-- Quadratic upper bound on the gate count: `qftControlledRkCount n ≤ n²`. -/
theorem qftControlledRkCount_le_sq (n : ℕ) : qftControlledRkCount n ≤ n ^ 2 := by
  unfold qftControlledRkCount
  calc n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ _
    _ ≤ n * n := by apply Nat.mul_le_mul_left; omega
    _ = n ^ 2 := by ring

/-- Quadratic lower bound on the gate count: `n² ≤ 4 · qftControlledRkCount n` for `n ≥ 2`. With the
upper bound `qftControlledRkCount_le_sq` this pins the count to `Θ(n²)`. -/
theorem sq_le_four_mul_qftControlledRkCount {n : ℕ} (hn : 2 ≤ n) :
    n ^ 2 ≤ 4 * qftControlledRkCount n := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  have h := two_mul_qftControlledRkCount (d + 1)
  simp only [Nat.add_sub_cancel] at h
  nlinarith [h, hn]

/-- **The QFT gate count grows quadratically:** `qftControlledRkCount n = Θ(n²)` (as `n → ∞`). This
is the `Θ(n²)` factor of Exercise 5.6's error scaling `Θ(n²/p(n))`: the number of imprecise
controlled-`Rₖ` gates in the QFT circuit is quadratic in the number of qubits. The `O(n²)` half is
`qftControlledRkCount_le_sq` (bound `1`), the `Ω(n²)` half `sq_le_four_mul_qftControlledRkCount`
(bound `4`, eventually). -/
theorem qftControlledRkCount_isTheta_sq :
    (fun n : ℕ => (qftControlledRkCount n : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 2) := by
  constructor
  · refine IsBigO.of_bound 1 ?_
    filter_upwards with n
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
    exact_mod_cast qftControlledRkCount_le_sq n
  · refine IsBigO.of_bound 4 ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact_mod_cast sq_le_four_mul_qftControlledRkCount hn

/-- **The approximate-QFT error bound scales as `Θ(n²/p(n))`** (Nielsen & Chuang, Exercise 5.6). For
any precision denominator `p : ℕ → ℝ` (`Δ = 1/p(n)`), the guaranteed error bound `n(n-1)/(2·p(n)) =
qftControlledRkCount n / p n` — the imprecise-gate count times the per-gate precision — grows as
`Θ(n²/p(n))`, since the gate count is `Θ(n²)` (`qftControlledRkCount_isTheta_sq`) and `p n` is a
common factor. This is the scaling of the error *bound*; the physics statement that the actual QFT
approximation error `E(U,V)` is dominated by this bound (hence `O(n²/p(n))`) is
`AxQM.qftApprox_gateError_le_div`. -/
theorem qftApproxErrorBound_isTheta (p : ℕ → ℝ) :
    (fun n : ℕ => (qftControlledRkCount n : ℝ) / p n)
      =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 2 / p n) := by
  have := qftControlledRkCount_isTheta_sq.mul (isTheta_refl (fun n : ℕ => (p n)⁻¹) atTop)
  simpa only [div_eq_mul_inv] using this

end AxQM.Concrete
