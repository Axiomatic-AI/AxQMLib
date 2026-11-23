/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.Normed.Algebra.LieTrotter

/-!
# Small-parameter Taylor estimates for exponential splittings

Let `𝔸` be a Banach algebra (a complete normed `ℝ`-algebra with `‖1‖ = 1`) and `x y : 𝔸`. This
file records the low-order `t → 0` (Taylor) error estimates for splitting the exponential of a sum
into a product of exponentials, phrased with `Asymptotics.IsBigO`: the statement
`f =O[𝓝 0] (fun t => tⁿ)` is exactly "`f t = O(tⁿ)` as `t → 0`", i.e. a constant `C` and a
neighbourhood of `0` on which `‖f t‖ ≤ C·|t|ⁿ`. The filter is the two-sided `𝓝 0`, so these are the
full-strength claims, not weakenings to `t ≥ 0`.

These are the operator content of Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 4.49, equations (4.103)–(4.105). N&C write them with an imaginary unit and Hermitian
generators, e.g. `e^{i(A+B)Δt} = e^{iAΔt} e^{iBΔt} + O(Δt²)`; that is the instance `x = i·A`,
`y = i·B` of the general statements here (the `i` and Hermiticity are absorbed into the arbitrary
algebra elements `x`, `y`), exactly as for the Lie–Trotter formula in
`ToMathlib/Analysis/Normed/Algebra/LieTrotter.lean`.

## Main results

First order (N&C (4.103)):

* `NormedSpace.isBigO_exp_smul_sub_one_sub_smul`: the first-order Taylor remainder
  `exp(t•x) - 1 - t•x =O[𝓝 0] (fun t => t²)`, the `IsBigO` form of the Banach-algebra remainder
  bound `NormedSpace.norm_exp_sub_one_sub_id_le`.
* `NormedSpace.isBigO_exp_smul_add_sub_exp_smul_mul_exp_smul`: the **first-order Lie–Trotter
  splitting error** `exp(t•(x+y)) - exp(t•x) exp(t•y) =O[𝓝 0] (fun t => t²)`, i.e. N&C (4.103).

Second order (N&C (4.105)):

* `NormedSpace.isBigO_exp_smul_sub_taylor2`: the second-order Taylor remainder
  `exp(t•x) - (1 + t•x + ½t²•x²) =O[𝓝 0] (fun t => t³)`, the `IsBigO` form of the third-order
  remainder bound `NormedSpace.norm_exp_sub_one_sub_id_sub_half_sq_le` (in the imported Lie–Trotter
  development).
* `NormedSpace.isBigO_exp_smul_mul_exp_smul_sub_taylor2`: the second-order expansion of a product of
  two exponentials.
* `NormedSpace.isBigO_exp_smul_add_sub_exp_smul_mul_exp_smul_mul_exp_lie`: the **second-order
  Baker–Campbell–Hausdorff formula** `exp(t•(x+y)) - exp(t•x) exp(t•y) exp(-½t²•⁅x, y⁆) =O[𝓝 0]
  (fun t => t³)`, i.e. N&C (4.105).

Symmetric (Strang) splitting (N&C (4.104)):

* `NormedSpace.isBigO_exp_smul_mul_exp_smul_mul_exp_smul_sub_taylor2`: the second-order expansion
  of a product of *three* exponentials, the three-factor analogue of
  `isBigO_exp_smul_mul_exp_smul_sub_taylor2`.
* `NormedSpace.isBigO_exp_smul_add_sub_exp_half_smul_mul_exp_smul_mul_exp_half_smul`: the
  **symmetric (Strang) splitting**
  `exp(t•(x+y)) - exp((t/2)•x) exp(t•y) exp((t/2)•x) =O[𝓝 0] (fun t => t³)`, i.e. N&C (4.104). The
  symmetric half-step arrangement makes the second-order term collapse to `½(x+y)²` directly, so —
  unlike the ordered form (4.105) — no commutator-correction factor is needed.
-/

@[expose] public section

open Asymptotics Filter Topology

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- On a neighbourhood of `0`, the real parameter satisfies `|t| ≤ 1`. A convenience wrapper around
`Metric.ball_mem_nhds` used to trim the exponential factors in the Taylor bounds below. -/
private theorem eventually_abs_le_one : ∀ᶠ t : ℝ in 𝓝 0, |t| ≤ 1 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  exact ht.le

/-- **First-order Taylor remainder of the exponential.** In a Banach algebra, as `t → 0`,
`exp(t•x) - 1 - t•x = O(t²)`.

This is the `Asymptotics.IsBigO` reading of the norm bound `NormedSpace.norm_exp_sub_one_sub_id_le`:
with `z = t•x` the latter gives `‖exp(t•x) - 1 - t•x‖ ≤ (|t|·‖x‖)²·Real.exp (|t|·‖x‖)`, and on the
neighbourhood `|t| ≤ 1` of `0` the exponential factor is at most the constant `Real.exp ‖x‖`, so the
remainder is bounded by `(‖x‖²·Real.exp ‖x‖)·|t|²`. -/
theorem isBigO_exp_smul_sub_one_sub_smul (x : 𝔸) :
    (fun t : ℝ => exp (t • x) - 1 - t • x) =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
  rw [isBigO_iff]
  refine ⟨‖x‖ ^ 2 * Real.exp ‖x‖, ?_⟩
  filter_upwards [eventually_abs_le_one] with t ht
  have hz : ‖t • x‖ = |t| * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs]
  calc ‖exp (t • x) - 1 - t • x‖
      ≤ ‖t • x‖ ^ 2 * Real.exp ‖t • x‖ := norm_exp_sub_one_sub_id_le _
    _ = (|t| * ‖x‖) ^ 2 * Real.exp (|t| * ‖x‖) := by rw [hz]
    _ ≤ (|t| * ‖x‖) ^ 2 * Real.exp ‖x‖ := by
          gcongr; exact mul_le_of_le_one_left (norm_nonneg x) ht
    _ = ‖x‖ ^ 2 * Real.exp ‖x‖ * ‖(t : ℝ) ^ 2‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t), mul_pow, sq_abs]; ring

/-- The exponential factor `exp(t•x)` is bounded near `0`, i.e. `O(1)`: on `|t| ≤ 1`,
`‖exp(t•x)‖ ≤ Real.exp ‖t•x‖ ≤ Real.exp ‖x‖`. -/
private theorem isBigO_exp_smul_one (x : 𝔸) :
    (fun t : ℝ => exp (t • x)) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨Real.exp ‖x‖, ?_⟩
  filter_upwards [eventually_abs_le_one] with t ht
  calc ‖exp (t • x)‖ ≤ Real.exp ‖t • x‖ := norm_exp_le _
    _ ≤ Real.exp ‖x‖ := Real.exp_le_exp.mpr (by
          rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg x) ht)
    _ = Real.exp ‖x‖ * ‖(1 : ℝ)‖ := by rw [norm_one, mul_one]

/-- **First-order error of the Lie–Trotter splitting of two exponentials.** In a Banach algebra, as
`t → 0`,
`exp(t•(x+y)) - exp(t•x) exp(t•y) = O(t²)`,
so replacing `exp(t•(x+y))` by the ordered product `exp(t•x) exp(t•y)` incurs only a second-order
error, even when `x` and `y` do **not** commute.

This is Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.49, equation
(4.103): with `x = i·A`, `y = i·B` it reads `e^{i(A+B)Δt} = e^{iAΔt} e^{iBΔt} + O(Δt²)`.

The proof rests on the exact identity
`exp(t•(x+y)) - exp(t•x) exp(t•y)
  = (exp(t•(x+y)) - 1 - t•(x+y)) - (t•x)(t•y)
    - (1 + t•x)·(exp(t•y) - 1 - t•y) - (exp(t•x) - 1 - t•x)·exp(t•y)`,
each of whose four summands is `O(t²)`: the first is `isBigO_exp_smul_sub_one_sub_smul (x + y)`, the
cross term `(t•x)(t•y)` is a product of two `O(t)` factors, and the two remainders are scaled by the
factors `1 + t•x` and `exp(t•y)`, each bounded near `0`. -/
theorem isBigO_exp_smul_add_sub_exp_smul_mul_exp_smul (x y : 𝔸) :
    (fun t : ℝ => exp (t • (x + y)) - exp (t • x) * exp (t • y)) =O[𝓝 0]
      (fun t : ℝ => t ^ 2) := by
  -- the two scaling factors `1 + t•x` and `exp(t•y)` are bounded near `0`, i.e. `O(1)`
  have hone : (fun t : ℝ => (1 : 𝔸) + t • x) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    ((continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 1
      (by simp)).isBigO_one ℝ
  have hexp := isBigO_exp_smul_one y
  -- the cross term `(t•x)(t•y)` is a product of two `O(t)` factors, hence `O(t²)`
  have hcross : (fun t : ℝ => (t • x) * (t • y)) =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
    rw [isBigO_iff]
    refine ⟨‖x‖ * ‖y‖, Eventually.of_forall fun t => ?_⟩
    calc ‖(t • x) * (t • y)‖
        ≤ ‖t • x‖ * ‖t • y‖ := norm_mul_le _ _
      _ = ‖x‖ * ‖y‖ * ‖(t : ℝ) ^ 2‖ := by
          simp only [norm_smul, Real.norm_eq_abs, abs_pow]; ring
  have hrem := isBigO_exp_smul_sub_one_sub_smul (x + y)
  have hb : (fun t : ℝ => (1 + t • x) * (exp (t • y) - 1 - t • y)) =O[𝓝 0]
      (fun t : ℝ => t ^ 2) := by
    simpa using hone.mul (isBigO_exp_smul_sub_one_sub_smul y)
  have ha : (fun t : ℝ => (exp (t • x) - 1 - t • x) * exp (t • y)) =O[𝓝 0]
      (fun t : ℝ => t ^ 2) := by
    simpa using (isBigO_exp_smul_sub_one_sub_smul x).mul hexp
  have hid : ∀ t : ℝ, exp (t • (x + y)) - exp (t • x) * exp (t • y)
      = (exp (t • (x + y)) - 1 - t • (x + y)) - (t • x) * (t • y)
        - (1 + t • x) * (exp (t • y) - 1 - t • y)
        - (exp (t • x) - 1 - t • x) * exp (t • y) := by
    intro t; simp only [smul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul]; abel
  exact (((hrem.sub hcross).sub hb).sub ha).congr'
    (Eventually.of_forall fun t => (hid t).symm) (Eventually.of_forall fun _ => rfl)

/-! ### Second-order expansions and the Baker–Campbell–Hausdorff formula, N&C (4.105) -/

/-- **Second-order Taylor remainder of the exponential.** In a Banach algebra, as `t → 0`,
`exp(t•x) - (1 + t•x + ½t²•x²) = O(t³)`. This is the `Asymptotics.IsBigO` form of
`norm_exp_sub_one_sub_id_sub_half_sq_le` (with `z = t•x`), the second-order analogue of
`isBigO_exp_smul_sub_one_sub_smul`. It is the single-factor building block from which the product
expansions below are assembled. -/
theorem isBigO_exp_smul_sub_taylor2 (x : 𝔸) :
    (fun t : ℝ => exp (t • x) - (1 + t • x + (2⁻¹ * t ^ 2) • x ^ 2)) =O[𝓝 0]
      (fun t : ℝ => t ^ 3) := by
  rw [isBigO_iff]
  refine ⟨‖x‖ ^ 3 * Real.exp ‖x‖, ?_⟩
  filter_upwards [eventually_abs_le_one] with t ht
  have hz : ‖t • x‖ = |t| * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs]
  -- rewrite the second-order coefficient `(½t²)•x²` as `½•(t•x)²` so the remainder bound applies
  have hpe : (1 : 𝔸) + t • x + (2⁻¹ * t ^ 2) • x ^ 2
      = 1 + t • x + (2⁻¹ : ℝ) • (t • x) ^ 2 := by
    have h1 : (t • x) ^ 2 = t ^ 2 • x ^ 2 := by simp only [pow_two, smul_mul_smul_comm]
    rw [h1, smul_smul]
  rw [hpe]
  calc ‖exp (t • x) - (1 + t • x + (2⁻¹ : ℝ) • (t • x) ^ 2)‖
      = ‖exp (t • x) - 1 - t • x - (2⁻¹ : ℝ) • (t • x) ^ 2‖ := by congr 1; abel
    _ ≤ ‖t • x‖ ^ 3 * Real.exp ‖t • x‖ := norm_exp_sub_one_sub_id_sub_half_sq_le _
    _ = (|t| * ‖x‖) ^ 3 * Real.exp (|t| * ‖x‖) := by rw [hz]
    _ ≤ (|t| * ‖x‖) ^ 3 * Real.exp ‖x‖ := by
          gcongr; exact mul_le_of_le_one_left (norm_nonneg x) ht
    _ = ‖x‖ ^ 3 * Real.exp ‖x‖ * ‖(t : ℝ) ^ 3‖ := by
          rw [Real.norm_eq_abs, abs_pow, mul_pow]; ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- A monomial `t^k • a` with `k ≥ 3` is `O(t³)` as `t → 0`: on the unit ball `|t| ≤ 1`,
`‖t^k • a‖ = |t|^k ‖a‖ ≤ |t|³ ‖a‖`. Used to discard the degree-`≥ 3` remainder of a truncated
polynomial. -/
private theorem isBigO_pow_smul {k : ℕ} (hk : 3 ≤ k) (a : 𝔸) :
    (fun t : ℝ => t ^ k • a) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  rw [isBigO_iff]
  refine ⟨‖a‖, ?_⟩
  filter_upwards [eventually_abs_le_one] with t ht
  rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow]
  calc |t| ^ k * ‖a‖ ≤ |t| ^ 3 * ‖a‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg t) ht hk) (norm_nonneg a)
    _ = ‖a‖ * |t| ^ 3 := mul_comm _ _

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- The second-order Taylor polynomial `1 + t•x + ½t²•x²` is bounded near `0`, i.e. `O(1)`. -/
private theorem isBigO_taylor2_poly (x : 𝔸) :
    (fun t : ℝ => (1 : 𝔸) + t • x + (2⁻¹ * t ^ 2) • x ^ 2) =O[𝓝 0]
      (fun _ : ℝ => (1 : ℝ)) :=
  (Continuous.tendsto' (by fun_prop) 0 1 (by simp)).isBigO_one ℝ

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- The first-order polynomial `1 + t²•w` (with a `t²`-scale coefficient) is bounded near `0`. -/
private theorem isBigO_one_add_sq_smul (w : 𝔸) :
    (fun t : ℝ => (1 : 𝔸) + t ^ 2 • w) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
  (Continuous.tendsto' (by fun_prop) 0 1 (by simp)).isBigO_one ℝ

omit [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
/-- **Product rule for second-order approximations.** If `f` is `O(1)`, `G` is `O(1)`,
`f - F = O(r)` and `g - G = O(r)` near `0`, then `f·g - F·G = O(r)`, via
`f·g - F·G = f·(g - G) + (f - F)·G`. This lets a product of exponentials inherit the approximation
error of its factors. -/
private theorem isBigO_mul_sub {f g F G : ℝ → 𝔸} {r : ℝ → ℝ}
    (hfO : f =O[𝓝 0] (fun _ : ℝ => (1 : ℝ))) (hg : (fun t => g t - G t) =O[𝓝 0] r)
    (hFsub : (fun t => f t - F t) =O[𝓝 0] r) (hGO : G =O[𝓝 0] (fun _ : ℝ => (1 : ℝ))) :
    (fun t => f t * g t - F t * G t) =O[𝓝 0] r := by
  have e1 : (fun t => f t * (g t - G t)) =O[𝓝 0] r := by simpa using hfO.mul hg
  have e2 : (fun t => (f t - F t) * G t) =O[𝓝 0] r := by simpa using hFsub.mul hGO
  refine (e1.add e2).congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun _ => rfl)
  simp only [mul_sub, sub_mul]; abel

/-- The `t²`-scale first-order remainder `exp(t²•w) - (1 + t²•w) = O(t³)` near `0`. Because the
argument is quadratic in `t`, the first-order remainder bound `norm_exp_sub_one_sub_id_le` gives an
`O(t⁴)` estimate, which is in particular `O(t³)`. Used for the commutator factor of the
Baker–Campbell–Hausdorff formula. -/
private theorem isBigO_exp_sq_smul_sub_one_sub (w : 𝔸) :
    (fun t : ℝ => exp (t ^ 2 • w) - (1 + t ^ 2 • w)) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  rw [isBigO_iff]
  refine ⟨‖w‖ ^ 2 * Real.exp ‖w‖, ?_⟩
  filter_upwards [eventually_abs_le_one] with t ht
  have ht2 : t ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg t) ht
  have hz : ‖t ^ 2 • w‖ = t ^ 2 * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
  have h4 : t ^ 4 ≤ |t| ^ 3 := by
    calc t ^ 4 = |t| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 4)]
      _ ≤ |t| ^ 3 := pow_le_pow_of_le_one (abs_nonneg t) ht (by norm_num)
  have hrw : exp (t ^ 2 • w) - (1 + t ^ 2 • w) = exp (t ^ 2 • w) - 1 - t ^ 2 • w := by abel
  rw [hrw]
  calc ‖exp (t ^ 2 • w) - 1 - t ^ 2 • w‖
      ≤ ‖t ^ 2 • w‖ ^ 2 * Real.exp ‖t ^ 2 • w‖ := norm_exp_sub_one_sub_id_le _
    _ = (t ^ 2 * ‖w‖) ^ 2 * Real.exp (t ^ 2 * ‖w‖) := by rw [hz]
    _ ≤ (t ^ 2 * ‖w‖) ^ 2 * Real.exp ‖w‖ := by
          gcongr; exact mul_le_of_le_one_left (norm_nonneg w) ht2
    _ = t ^ 4 * (‖w‖ ^ 2 * Real.exp ‖w‖) := by ring
    _ ≤ |t| ^ 3 * (‖w‖ ^ 2 * Real.exp ‖w‖) := by
          gcongr
    _ = ‖w‖ ^ 2 * Real.exp ‖w‖ * ‖(t : ℝ) ^ 3‖ := by rw [Real.norm_eq_abs, abs_pow]; ring

/-- **Second-order expansion of a product of two exponentials.** In a Banach algebra, as `t → 0`,
`exp(t•x) exp(t•y) - (1 + t•(x+y) + ½t²•(x² + 2xy + y²)) = O(t³)`.
Expanding each factor to second order and multiplying, the degree-`≤ 2` part is
`1 + t•(x+y) + ½t²•(x² + 2xy + y²)` (note `x² + 2xy + y² ≠ (x+y)²` when `x`, `y` do not commute) and
the degree-`≥ 3` part is `O(t³)`.

This is the two-factor building block for the second-order splitting formulas; N&C (4.105) is
obtained from it by multiplying in the commutator factor. -/
theorem isBigO_exp_smul_mul_exp_smul_sub_taylor2 (x y : 𝔸) :
    (fun t : ℝ => exp (t • x) * exp (t • y)
        - (1 + t • (x + y) + (2⁻¹ * t ^ 2) • (x ^ 2 + 2 • (x * y) + y ^ 2))) =O[𝓝 0]
      (fun t : ℝ => t ^ 3) := by
  -- `exp(t•x) exp(t•y)` is close to the product `Qₓ · Q_y` of the two Taylor polynomials
  have hprod : (fun t : ℝ => exp (t • x) * exp (t • y)
      - (1 + t • x + (2⁻¹ * t ^ 2) • x ^ 2) * (1 + t • y + (2⁻¹ * t ^ 2) • y ^ 2)) =O[𝓝 0]
        (fun t : ℝ => t ^ 3) :=
    isBigO_mul_sub (isBigO_exp_smul_one x) (isBigO_exp_smul_sub_taylor2 y)
      (isBigO_exp_smul_sub_taylor2 x) (isBigO_taylor2_poly y)
  -- `Qₓ · Q_y` differs from its degree-`≤ 2` truncation by explicit `t³` and `t⁴` monomials
  have hpoly : (fun t : ℝ =>
      (1 + t • x + (2⁻¹ * t ^ 2) • x ^ 2) * (1 + t • y + (2⁻¹ * t ^ 2) • y ^ 2)
        - (1 + t • (x + y) + (2⁻¹ * t ^ 2) • (x ^ 2 + 2 • (x * y) + y ^ 2))) =O[𝓝 0]
        (fun t : ℝ => t ^ 3) := by
    have hid : ∀ t : ℝ,
        (1 + t • x + (2⁻¹ * t ^ 2) • x ^ 2) * (1 + t • y + (2⁻¹ * t ^ 2) • y ^ 2)
          - (1 + t • (x + y) + (2⁻¹ * t ^ 2) • (x ^ 2 + 2 • (x * y) + y ^ 2))
          = t ^ 3 • ((2⁻¹ : ℝ) • (x * y ^ 2 + x ^ 2 * y))
            + t ^ 4 • ((4⁻¹ : ℝ) • (x ^ 2 * y ^ 2)) := by
      intro t
      simp only [pow_two, mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm]
      match_scalars <;> ring
    refine ((isBigO_pow_smul (k := 3) (le_refl 3) ((2⁻¹ : ℝ) • (x * y ^ 2 + x ^ 2 * y))).add
      (isBigO_pow_smul (k := 4) (by norm_num) ((4⁻¹ : ℝ) • (x ^ 2 * y ^ 2)))).congr'
      (Eventually.of_forall fun t => (hid t).symm) (Eventually.of_forall fun _ => rfl)
  refine (hprod.add hpoly).congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun _ =>
    rfl)
  abel_nf

/-- **The second-order Baker–Campbell–Hausdorff formula.** In a Banach algebra, as `t → 0`,
`exp(t•(x+y)) - exp(t•x) exp(t•y) exp(-½t²•⁅x, y⁆) = O(t³)`,
where `⁅x, y⁆ = xy - yx` is the commutator. So the symmetric second-order correction that turns the
naive splitting `exp(t•x) exp(t•y)` into an `O(t³)` approximation of `exp(t•(x+y))` is exactly
`exp(-½t²•⁅x, y⁆)`.

This is Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.49, equation
(4.105): `e^{(A+B)Δt} = e^{AΔt} e^{BΔt} e^{-½[A,B]Δt²} + O(Δt³)` (N&C state it without an imaginary
unit, directly for general `A = x`, `B = y`). The exponent `t²•(-½•⁅x, y⁆)` of the third factor is
`-½[x, y]Δt²`.

The proof combines three second-order expansions: `exp(t•x) exp(t•y)` expands as
`1 + t•(x+y) + ½t²•(x² + 2xy + y²) + O(t³)` (`isBigO_exp_smul_mul_exp_smul_sub_taylor2`), the
commutator factor as `1 - ½t²•⁅x, y⁆ + O(t³)` (`isBigO_exp_sq_smul_sub_one_sub`), and their
product's degree-`≤ 2` part collapses to `1 + t•(x+y) + ½t²•(x+y)²` via the key cancellation
`x² + 2xy + y² - ⁅x, y⁆ = (x+y)²`; this matches the expansion of `exp(t•(x+y))`
(`isBigO_exp_smul_sub_taylor2`). -/
theorem isBigO_exp_smul_add_sub_exp_smul_mul_exp_smul_mul_exp_lie (x y : 𝔸) :
    (fun t : ℝ => exp (t • (x + y))
        - exp (t • x) * exp (t • y) * exp (t ^ 2 • ((-2⁻¹ : ℝ) • ⁅x, y⁆))) =O[𝓝 0]
      (fun t : ℝ => t ^ 3) := by
  set c : 𝔸 := (-2⁻¹ : ℝ) • ⁅x, y⁆ with hc
  -- `exp(t•x) exp(t•y)` is bounded near `0`, and expands to second order
  have hABO : (fun t : ℝ => exp (t • x) * exp (t • y)) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) := by
    simpa using (isBigO_exp_smul_one x).mul (isBigO_exp_smul_one y)
  have hAB := isBigO_exp_smul_mul_exp_smul_sub_taylor2 x y
  -- the commutator factor expands to first order (`O(t³)`), and `1 + t²•c` is bounded
  have hCfac := isBigO_exp_sq_smul_sub_one_sub c
  -- the triple product is close to `Qxy2 · (1 + t²•c)`
  have hprod := isBigO_mul_sub hABO hCfac hAB (isBigO_one_add_sq_smul c)
  -- `Qxy2 · (1 + t²•c)` differs from `exp(t•(x+y))`'s Taylor polynomial by `O(t³)` monomials
  have hpoly : (fun t : ℝ =>
      (1 + t • (x + y) + (2⁻¹ * t ^ 2) • (x ^ 2 + 2 • (x * y) + y ^ 2)) * (1 + t ^ 2 • c)
        - (1 + t • (x + y) + (2⁻¹ * t ^ 2) • (x + y) ^ 2)) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
    have hid : ∀ t : ℝ,
        (1 + t • (x + y) + (2⁻¹ * t ^ 2) • (x ^ 2 + 2 • (x * y) + y ^ 2)) * (1 + t ^ 2 • c)
          - (1 + t • (x + y) + (2⁻¹ * t ^ 2) • (x + y) ^ 2)
          = t ^ 3 • ((x + y) * c)
            + t ^ 4 • ((2⁻¹ : ℝ) • ((x ^ 2 + 2 • (x * y) + y ^ 2) * c)) := by
      intro t
      rw [hc, Ring.lie_def]
      simp only [pow_two, mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm,
        smul_sub, smul_add, mul_sub]
      match_scalars <;> ring
    refine ((isBigO_pow_smul (k := 3) (le_refl 3) ((x + y) * c)).add
      (isBigO_pow_smul (k := 4) (by norm_num)
        ((2⁻¹ : ℝ) • ((x ^ 2 + 2 • (x * y) + y ^ 2) * c)))).congr'
      (Eventually.of_forall fun t => (hid t).symm) (Eventually.of_forall fun _ => rfl)
  -- `exp(t•(x+y))` expands to the same second-order polynomial
  have hSum := isBigO_exp_smul_sub_taylor2 (x + y)
  refine ((hSum.sub hprod).sub hpoly).congr' (Eventually.of_forall fun t => ?_)
    (Eventually.of_forall fun _ => rfl)
  abel_nf

/-! ### The symmetric (Strang) splitting, N&C (4.104) -/

/-- **Second-order expansion of a product of three exponentials.** In a Banach algebra, as `t → 0`,
`exp(t•a) exp(t•b) exp(t•c) - (1 + t•(a+b+c) + ½t²•(a² + b² + c² + 2ab + 2ac + 2bc)) = O(t³)`.
The three-factor analogue of `isBigO_exp_smul_mul_exp_smul_sub_taylor2`: the degree-`≤ 2` part
of the product of the three Taylor polynomials is `1 + t•(a+b+c) + ½t²•(a²+b²+c² + 2ab+2ac+2bc)`
(with all six ordered cross terms), and the degree-`≥ 3` part is `O(t³)`.

The proof folds the third factor into the two-factor expansion via the product rule
`isBigO_mul_sub`: `exp(t•a) exp(t•b)` is `O(1)` and expands to second order
(`isBigO_exp_smul_mul_exp_smul_sub_taylor2`), and multiplying by `exp(t•c)` — itself `O(1)` and
second-order (`isBigO_exp_smul_sub_taylor2`) — the degree-`≤ 2` truncation of the resulting
polynomial product matches the claimed polynomial, the difference being explicit `t³` and `t⁴`
monomials. -/
theorem isBigO_exp_smul_mul_exp_smul_mul_exp_smul_sub_taylor2 (a b c : 𝔸) :
    (fun t : ℝ => exp (t • a) * exp (t • b) * exp (t • c)
        - (1 + t • (a + b + c) + (2⁻¹ * t ^ 2) • (a ^ 2 + b ^ 2 + c ^ 2
            + 2 • (a * b) + 2 • (a * c) + 2 • (b * c)))) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  have hABO : (fun t : ℝ => exp (t • a) * exp (t • b)) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) := by
    simpa using (isBigO_exp_smul_one a).mul (isBigO_exp_smul_one b)
  have hAB := isBigO_exp_smul_mul_exp_smul_sub_taylor2 a b
  have hprod := isBigO_mul_sub hABO (isBigO_exp_smul_sub_taylor2 c) hAB (isBigO_taylor2_poly c)
  have hpoly : (fun t : ℝ =>
      (1 + t • (a + b) + (2⁻¹ * t ^ 2) • (a ^ 2 + 2 • (a * b) + b ^ 2))
          * (1 + t • c + (2⁻¹ * t ^ 2) • c ^ 2)
        - (1 + t • (a + b + c) + (2⁻¹ * t ^ 2) • (a ^ 2 + b ^ 2 + c ^ 2
            + 2 • (a * b) + 2 • (a * c) + 2 • (b * c)))) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
    have hid : ∀ t : ℝ,
        (1 + t • (a + b) + (2⁻¹ * t ^ 2) • (a ^ 2 + 2 • (a * b) + b ^ 2))
            * (1 + t • c + (2⁻¹ * t ^ 2) • c ^ 2)
          - (1 + t • (a + b + c) + (2⁻¹ * t ^ 2) • (a ^ 2 + b ^ 2 + c ^ 2
              + 2 • (a * b) + 2 • (a * c) + 2 • (b * c)))
          = t ^ 3 • ((2⁻¹ : ℝ) • ((a + b) * c ^ 2 + (a ^ 2 + 2 • (a * b) + b ^ 2) * c))
            + t ^ 4 • ((4⁻¹ : ℝ) • ((a ^ 2 + 2 • (a * b) + b ^ 2) * c ^ 2)) := by
      intro t
      simp only [pow_two, mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm]
      match_scalars <;> ring
    refine ((isBigO_pow_smul (k := 3) (le_refl 3)
        ((2⁻¹ : ℝ) • ((a + b) * c ^ 2 + (a ^ 2 + 2 • (a * b) + b ^ 2) * c))).add
      (isBigO_pow_smul (k := 4) (by norm_num)
        ((4⁻¹ : ℝ) • ((a ^ 2 + 2 • (a * b) + b ^ 2) * c ^ 2)))).congr'
      (Eventually.of_forall fun t => (hid t).symm) (Eventually.of_forall fun _ => rfl)
  refine (hprod.add hpoly).congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun _ =>
    rfl)
  abel_nf

/-- **The symmetric (Strang) splitting.** In a Banach algebra, as `t → 0`,
`exp(t•(x+y)) - exp((t/2)•x) exp(t•y) exp((t/2)•x) = O(t³)`.

This is Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.49, equation
(4.104): with `x = i·A`, `y = i·B` it reads
`e^{i(A+B)Δt} = e^{iAΔt/2} e^{iBΔt} e^{iAΔt/2} + O(Δt³)`. Unlike the naive splitting
`exp(t•x) exp(t•y)` (only `O(t²)`, N&C (4.103)), the *symmetric* half-step arrangement is accurate
to `O(t³)` with **no** commutator-correction factor — the counterpart of the explicit
`exp(-½t²•⁅x, y⁆)` needed in the ordered form (4.105).

The proof applies the three-factor expansion `isBigO_exp_smul_mul_exp_smul_mul_exp_smul_sub_taylor2`
with `a = c = ½x`, `b = y`: the second-order coefficient of `exp(½t•x) exp(t•y) exp(½t•x)` is
`(½x)² + y² + (½x)² + 2(½x)y + 2(½x)(½x) + 2y(½x)`, which — because the arrangement is symmetric
in the two half-steps — collapses to `½(x+y)²`, exactly the second-order polynomial of
`exp(t•(x+y))` (`isBigO_exp_smul_sub_taylor2`). No commutator term survives. -/
theorem isBigO_exp_smul_add_sub_exp_half_smul_mul_exp_smul_mul_exp_half_smul (x y : 𝔸) :
    (fun t : ℝ => exp (t • (x + y))
        - exp ((t / 2) • x) * exp (t • y) * exp ((t / 2) • x)) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  have hhalf : ∀ t : ℝ, exp ((t / 2) • x) = exp (t • ((2⁻¹ : ℝ) • x)) := by
    intro t; rw [div_eq_mul_inv, mul_smul]
  have htri := isBigO_exp_smul_mul_exp_smul_mul_exp_smul_sub_taylor2 ((2⁻¹ : ℝ) • x) y
    ((2⁻¹ : ℝ) • x)
  have hcollapse : ∀ t : ℝ,
      (1 + t • ((2⁻¹ : ℝ) • x + y + (2⁻¹ : ℝ) • x)
          + (2⁻¹ * t ^ 2) • (((2⁻¹ : ℝ) • x) ^ 2 + y ^ 2 + ((2⁻¹ : ℝ) • x) ^ 2
              + 2 • (((2⁻¹ : ℝ) • x) * y) + 2 • (((2⁻¹ : ℝ) • x) * ((2⁻¹ : ℝ) • x))
              + 2 • (y * ((2⁻¹ : ℝ) • x))))
        = 1 + t • (x + y) + (2⁻¹ * t ^ 2) • (x + y) ^ 2 := by
    intro t
    simp only [pow_two, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
    match_scalars <;> ring
  have hSum := isBigO_exp_smul_sub_taylor2 (x + y)
  refine (hSum.sub htri).congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun _ =>
    rfl)
  simp only [hcollapse t, hhalf t]
  abel

end NormedSpace
