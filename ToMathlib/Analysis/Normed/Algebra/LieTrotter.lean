/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import ToMathlib.Analysis.Normed.Ring.ProductTelescope
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# The Lie–Trotter product formula

Let `𝔸` be a Banach algebra (a complete normed `ℝ`-algebra with `‖1‖ = 1`) and `x y : 𝔸`. This file
proves the **Lie product formula**, also known as the **Trotter product formula**:

`Tendsto (fun n : ℕ => (exp (n⁻¹ • x) * exp (n⁻¹ • y)) ^ n) atTop (𝓝 (exp (x + y)))`,

i.e. `lim (exp(x/n) exp(y/n))ⁿ = exp(x + y)`, valid even when `x` and `y` do **not** commute. This
is Nielsen & Chuang, *Quantum Computation and Quantum Information*, Theorem 4.3, which states it for
Hermitian operators `A, B` and real `t` as `lim (e^{iAt/n} e^{iBt/n})ⁿ = e^{i(A+B)t}` — the special
case obtained here by taking `x = i·t·A`, `y = i·t·B` (any operator, Hermitian or not, is an element
of the algebra, so the general statement below subsumes it).

The proof is the classical one. Writing `aₙ = exp(x/n) exp(y/n)` and `bₙ = exp((x+y)/n)`, one has
`bₙⁿ = exp(x + y)` exactly (`exp_nsmul`), while `‖aₙ - bₙ‖ = O(1/n²)` (a second-order Taylor
estimate: both factors agree with `1 + (x+y)/n` to first order). A telescoping bound on
`‖aₙⁿ - bₙⁿ‖` (with `‖aₙ‖, ‖bₙ‖ ≤ exp((‖x‖+‖y‖)/n)`, whose `n`-th power is the constant
`exp(‖x‖+‖y‖)`) then gives `‖aₙⁿ - exp(x+y)‖ ≤ C·n · (1/n²) = O(1/n) → 0`.

## Main results

* `norm_pow_sub_pow_le`: the noncommutative telescoping bound `‖xⁿ - yⁿ‖ ≤ n·Mⁿ·‖x - y‖` when
  `‖x‖, ‖y‖ ≤ M` and `1 ≤ M`.
* `norm_prod_one_add_sub_one_sub_sum_le`: the product-linearization bound
  `‖(∏ᵢ (1 + aᵢ)) - 1 - ∑ᵢ aᵢ‖ ≤ (∏ᵢ (1 + ‖aᵢ‖)) - 1 - ∑ᵢ ‖aᵢ‖`, and its closed form
  `NormedSpace.norm_prod_one_add_sub_one_sub_sum_le_exp`,
  `‖(∏ᵢ (1 + aᵢ)) - 1 - ∑ᵢ aᵢ‖ ≤ (∑ᵢ ‖aᵢ‖)² · Real.exp (∑ᵢ ‖aᵢ‖)` — the second-order deviation of a
  finite product of `1 + aᵢ` factors from its linearization, proved elementarily (no series or
  noncommutative expansion).
* `NormedSpace.norm_exp_le`: `‖exp z‖ ≤ Real.exp ‖z‖` in a Banach algebra (the general-algebra form
  of `Complex.norm_exp_le_exp_norm`).
* `NormedSpace.norm_exp_sub_sum_le`: the order-`k` Taylor remainder bound
  `‖exp z - ∑ i < k, (i!)⁻¹ • zⁱ‖ ≤ ‖z‖ᵏ · Real.exp ‖z‖`, with the second- and third-order
  remainders `norm_exp_sub_one_sub_id_le` and `norm_exp_sub_one_sub_id_sub_half_sq_le` as its
  `k = 2`, `k = 3` instances.
* `NormedSpace.tendsto_pow_exp_smul_mul_exp_smul`: the Lie–Trotter product formula.
* `NormedSpace.exists_norm_exp_smul_mul_exp_two_smul_mul_exp_smul_sub_le`: the *symmetric* (Strang)
  second-order splitting error, `‖exp(t•x) exp((2t)•y) exp(t•x) - exp((2t)•(x+y))‖ ≤ K·t³` — one
  order better than the unsymmetric splitting, the base case of Nielsen & Chuang Exercise 4.50(a).
* `NormedSpace.exists_norm_prod_exp_smul_sub_exp_smul_sum_le`: the first-order (`O(t²)`) error of
  splitting `exp(t • ∑ gᵢ)` into the ordered product `∏ exp(t•gᵢ)` of a finite list of factors.
* `NormedSpace.norm_prod_exp_smul_le`: `‖∏ exp(s•gᵢ)‖ ≤ Real.exp(s • ∑ ‖gᵢ‖)` for `s ≥ 0`.
* `NormedSpace.exists_norm_prod_exp_inv_smul_pow_sub_exp_sum_le`: the accumulated `O(k⁻¹)` error of
  the `k`-fold splitting `(∏ exp(k⁻¹•gᵢ))^k` of `exp(∑ gᵢ)`.
* `NormedSpace.norm_prod_exp_inv_smul_pow_sub_exp_sum_le_sq`: the same `k`-fold error with an
  **explicit numerical** constant and **polynomial** `Λ`-dependence, `≤ (2e + e²·eᵉ)·Λ²·k⁻¹`
  (`Λ = ∑‖gᵢ‖`), under the *contraction* hypothesis `‖exp(s•gᵢ)‖ ≤ 1` (e.g. skew-adjoint `gᵢ`) that
  makes the telescoping run with `M = 1`; the sharpening behind Nielsen & Chuang Problem 4.3(6)'s
  literal `O(n·16ⁿ/ε)` gate count.
* `NormedSpace.exists_norm_symmProd_exp_smul_sub_exp_two_smul_sum_le`: the symmetric (Strang)
  `O(t³)` error of the *palindromic* splitting `(∏ exp(t•gᵢ)) · (∏ exp(t•gᵢ) reversed)` of
  `exp(2t • ∑ gᵢ)` over a finite list — the list form of Nielsen & Chuang Exercise 4.50(a), one
  order better than the unsymmetric `exists_norm_prod_exp_smul_sub_exp_smul_sum_le`.
-/

@[expose] public section

open Filter Topology

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]

/-- **Noncommutative telescoping bound.** If `‖x‖ ≤ M`, `‖y‖ ≤ M` and `1 ≤ M` in a normed ring,
then `‖xⁿ - yⁿ‖ ≤ n · Mⁿ · ‖x - y‖`. This is the norm estimate behind the identity
`xⁿ - yⁿ = ∑ᵢ xⁱ (x - y) y^(n-1-i)`, proved directly by induction (the factors need not commute, so
the `Commute.*` geometric-sum lemmas do not apply). -/
theorem norm_pow_sub_pow_le {x y : 𝔸} {M : ℝ} (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hM : 1 ≤ M) :
    ∀ n : ℕ, ‖x ^ n - y ^ n‖ ≤ n * M ^ n * ‖x - y‖ := by
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hyn : ‖y ^ n‖ ≤ M ^ n := le_trans (norm_pow_le y n) (pow_le_pow_left₀ (norm_nonneg y) hy n)
    have key : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by
      rw [mul_sub, sub_mul, pow_succ' x n, pow_succ' y n]; abel
    calc ‖x ^ (n + 1) - y ^ (n + 1)‖
        = ‖x * (x ^ n - y ^ n) + (x - y) * y ^ n‖ := by rw [key]
      _ ≤ ‖x * (x ^ n - y ^ n)‖ + ‖(x - y) * y ^ n‖ := norm_add_le _ _
      _ ≤ ‖x‖ * ‖x ^ n - y ^ n‖ + ‖x - y‖ * ‖y ^ n‖ :=
            add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ M * (↑n * M ^ n * ‖x - y‖) + ‖x - y‖ * M ^ n := by gcongr
      _ = ↑n * M ^ (n + 1) * ‖x - y‖ + M ^ n * ‖x - y‖ := by ring
      _ ≤ ↑n * M ^ (n + 1) * ‖x - y‖ + M ^ (n + 1) * ‖x - y‖ := by
            have hstep : M ^ n ≤ M ^ (n + 1) := pow_le_pow_right₀ hM (Nat.le_succ n)
            nlinarith [hstep, norm_nonneg (x - y)]
      _ = ↑(n + 1) * M ^ (n + 1) * ‖x - y‖ := by push_cast; ring

/-- **Product-of-`1 + ·` deviation bound.** In a normed ring, the product `∏ᵢ (1 + aᵢ)` over a
finite list deviates from `1` by at most the corresponding scalar deviation:
`‖(∏ᵢ (1 + aᵢ)) - 1‖ ≤ (∏ᵢ (1 + ‖aᵢ‖)) - 1`.
Proved by induction on the list: the cons step rewrites `(1 + b)·P - 1 = (1 + b)·(P - 1) + b` and
bounds each piece submultiplicatively (`‖1 + b‖ ≤ 1 + ‖b‖`, `norm_mul_le`). This is the base lemma
for the product-linearization bound `norm_prod_one_add_sub_one_sub_sum_le`. -/
theorem norm_prod_one_add_sub_one_le (c : List 𝔸) :
    ‖(c.map fun a => 1 + a).prod - 1‖ ≤ (c.map fun a => 1 + ‖a‖).prod - 1 := by
  induction c with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.prod_cons]
    have h1 : ‖(1 : 𝔸) + b‖ ≤ 1 + ‖b‖ := by refine (norm_add_le _ _).trans ?_; rw [norm_one]
    have key : (1 + b) * (l.map fun a => 1 + a).prod - 1
        = (1 + b) * ((l.map fun a => 1 + a).prod - 1) + b := by noncomm_ring
    rw [key]
    have hbound : ‖(1 + b) * ((l.map fun a => 1 + a).prod - 1)‖
        ≤ (1 + ‖b‖) * ((l.map fun a => 1 + ‖a‖).prod - 1) :=
      (norm_mul_le _ _).trans (mul_le_mul h1 ih (norm_nonneg _) (by positivity))
    calc ‖(1 + b) * ((l.map fun a => 1 + a).prod - 1) + b‖
        ≤ ‖(1 + b) * ((l.map fun a => 1 + a).prod - 1)‖ + ‖b‖ := norm_add_le _ _
      _ ≤ (1 + ‖b‖) * ((l.map fun a => 1 + ‖a‖).prod - 1) + ‖b‖ := by linarith
      _ = (1 + ‖b‖) * (l.map fun a => 1 + ‖a‖).prod - 1 := by ring

/-- **Product-linearization bound.** In a normed ring, the product `∏ᵢ (1 + aᵢ)` over a finite list
agrees with its first-order (linear) approximation `1 + ∑ᵢ aᵢ` up to the corresponding scalar
remainder:
`‖(∏ᵢ (1 + aᵢ)) - 1 - ∑ᵢ aᵢ‖ ≤ (∏ᵢ (1 + ‖aᵢ‖)) - 1 - ∑ᵢ ‖aᵢ‖`.
The right-hand side is the second-order (cross) part of the product `∏ (1 + ‖aᵢ‖)`; in particular
it vanishes when at most one factor is nonzero. Proved by induction using
`norm_prod_one_add_sub_one_le` for the tail product — no series or noncommutative multinomial
expansion is needed. Its closed form is `NormedSpace.norm_prod_one_add_sub_one_sub_sum_le_exp`. -/
theorem norm_prod_one_add_sub_one_sub_sum_le (c : List 𝔸) :
    ‖(c.map fun a => 1 + a).prod - 1 - c.sum‖
      ≤ (c.map fun a => 1 + ‖a‖).prod - 1 - (c.map fun a => ‖a‖).sum := by
  induction c with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have hA := norm_prod_one_add_sub_one_le l
    have key : (1 + b) * (l.map fun a => 1 + a).prod - 1 - (b + l.sum)
        = ((l.map fun a => 1 + a).prod - 1 - l.sum) + b * ((l.map fun a => 1 + a).prod - 1) := by
      noncomm_ring
    rw [key]
    have hbound : ‖b * ((l.map fun a => 1 + a).prod - 1)‖
        ≤ ‖b‖ * ((l.map fun a => 1 + ‖a‖).prod - 1) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
    calc ‖((l.map fun a => 1 + a).prod - 1 - l.sum) + b * ((l.map fun a => 1 + a).prod - 1)‖
        ≤ ‖(l.map fun a => 1 + a).prod - 1 - l.sum‖ + ‖b * ((l.map fun a => 1 + a).prod - 1)‖ :=
          norm_add_le _ _
      _ ≤ ((l.map fun a => 1 + ‖a‖).prod - 1 - (l.map fun a => ‖a‖).sum)
            + ‖b‖ * ((l.map fun a => 1 + ‖a‖).prod - 1) := by linarith
      _ = (1 + ‖b‖) * (l.map fun a => 1 + ‖a‖).prod - 1 - (‖b‖ + (l.map fun a => ‖a‖).sum) := by
        ring

omit [NormOneClass 𝔸] in
/-- In a normed ring, `∏ᵢ (1 + ‖aᵢ‖) ≤ Real.exp (∑ᵢ ‖aᵢ‖)`, from the scalar inequality
`1 + t ≤ Real.exp t` (`Real.add_one_le_exp`) applied factorwise together with `Real.exp_add`. -/
theorem prod_one_add_norm_le_exp (c : List 𝔸) :
    (c.map fun a => 1 + ‖a‖).prod ≤ Real.exp ((c.map fun a => ‖a‖).sum) := by
  induction c with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Real.exp_add]
    have hcnn : 0 ≤ (l.map fun a => 1 + ‖a‖).prod :=
      List.prod_nonneg fun x hx => by
        rw [List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; positivity
    refine mul_le_mul ?_ ih hcnn (Real.exp_pos _).le
    rw [add_comm]; exact Real.add_one_le_exp _

namespace NormedSpace

variable [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **The norm of the exponential is bounded by the exponential of the norm.** In a Banach algebra,
`‖exp z‖ ≤ Real.exp ‖z‖`. This is the general-algebra analogue of `Complex.norm_exp_le_exp_norm`,
obtained by comparing the exponential series `∑ (n!)⁻¹ • zⁿ` termwise with the real series for
`Real.exp ‖z‖`. -/
theorem norm_exp_le (z : 𝔸) : ‖exp z‖ ≤ Real.exp ‖z‖ := by
  have hsum : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ • z ^ n) (exp z) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) z
  have hnorm_summable : Summable (fun n : ℕ => ‖(n.factorial : ℝ)⁻¹ • z ^ n‖) :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) z
  have hreal_summable : Summable (fun n : ℕ => (n.factorial : ℝ)⁻¹ * ‖z‖ ^ n) := by
    have := Real.summable_pow_div_factorial ‖z‖
    simpa [div_eq_mul_inv, mul_comm] using this
  calc ‖exp z‖ = ‖∑' n : ℕ, (n.factorial : ℝ)⁻¹ • z ^ n‖ := by rw [hsum.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖(n.factorial : ℝ)⁻¹ • z ^ n‖ := norm_tsum_le_tsum_norm hnorm_summable
    _ ≤ ∑' n : ℕ, (n.factorial : ℝ)⁻¹ * ‖z‖ ^ n := by
          refine Summable.tsum_le_tsum (fun n => ?_) hnorm_summable hreal_summable
          rw [norm_smul]
          have hc : ‖(n.factorial : ℝ)⁻¹‖ = (n.factorial : ℝ)⁻¹ := by
            rw [Real.norm_eq_abs, abs_inv, Nat.abs_cast]
          rw [hc]
          gcongr
          exact norm_pow_le z n
    _ = Real.exp ‖z‖ := by
          rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
          congr 1
          ext n
          rw [div_eq_mul_inv, mul_comm]

/-- **Taylor remainder bound for the exponential.** In a Banach algebra, `exp z` differs from its
order-`k` Taylor partial sum `∑ i < k, (i!)⁻¹ • zⁱ` by at most `‖z‖ᵏ · Real.exp ‖z‖`:
`‖exp z - ∑ i ∈ Finset.range k, (i.factorial : ℝ)⁻¹ • z ^ i‖ ≤ ‖z‖ ^ k · Real.exp ‖z‖`.
The exponential series with its first `k` terms removed is `∑ₙ ((n+k)!)⁻¹ • z^(n+k)`, whose norm is
bounded termwise (using `((n+k)!)⁻¹ ≤ (n!)⁻¹`) by `‖z‖ᵏ · ∑ₙ (n!)⁻¹ ‖z‖ⁿ = ‖z‖ᵏ · Real.exp ‖z‖`.
This is the Banach-algebra analogue of `Complex.norm_exp_sub_sum_le_exp_norm_sub_sum`; the low-order
remainder bounds `norm_exp_sub_one_sub_id_le` (`k = 2`) and `norm_exp_sub_one_sub_id_sub_half_sq_le`
(`k = 3`) are its instances. -/
theorem norm_exp_sub_sum_le (z : 𝔸) (k : ℕ) :
    ‖exp z - ∑ i ∈ Finset.range k, (i.factorial : ℝ)⁻¹ • z ^ i‖ ≤ ‖z‖ ^ k * Real.exp ‖z‖ := by
  set f : ℕ → 𝔸 := fun n => (n.factorial : ℝ)⁻¹ • z ^ n with hf
  have hsum : HasSum f (exp z) := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) z
  have hns : Summable f := hsum.summable
  have hnorm_summable : Summable (fun n : ℕ => ‖f n‖) :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) z
  have hreal_summable : Summable (fun n : ℕ => (n.factorial : ℝ)⁻¹ * ‖z‖ ^ n) := by
    have := Real.summable_pow_div_factorial ‖z‖
    simpa [div_eq_mul_inv, mul_comm] using this
  have hexp_eq : (∑' n : ℕ, (n.factorial : ℝ)⁻¹ * ‖z‖ ^ n) = Real.exp ‖z‖ := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]; congr 1; ext n
    rw [div_eq_mul_inv, mul_comm]
  have hpeel : (∑ i ∈ Finset.range k, f i) + ∑' n : ℕ, f (n + k) = exp z := by
    rw [Summable.sum_add_tsum_nat_add k hns, hsum.tsum_eq]
  have hrem : exp z - ∑ i ∈ Finset.range k, (i.factorial : ℝ)⁻¹ • z ^ i = ∑' n : ℕ, f (n + k) := by
    have hfsum : (∑ i ∈ Finset.range k, f i)
        = ∑ i ∈ Finset.range k, (i.factorial : ℝ)⁻¹ • z ^ i := rfl
    rw [← hpeel, hfsum]; abel
  rw [hrem]
  have hshift : Summable (fun n : ℕ => ‖f (n + k)‖) := (summable_nat_add_iff k).mpr hnorm_summable
  calc ‖∑' n : ℕ, f (n + k)‖
      ≤ ∑' n : ℕ, ‖f (n + k)‖ := norm_tsum_le_tsum_norm hshift
    _ ≤ ∑' n : ℕ, ‖z‖ ^ k * ((n.factorial : ℝ)⁻¹ * ‖z‖ ^ n) := by
          refine Summable.tsum_le_tsum (fun n => ?_) hshift (hreal_summable.mul_left _)
          have hfac : (n.factorial : ℝ) ≤ ((n + k).factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le (Nat.le_add_right n k)
          have hnf : ‖f (n + k)‖ = ((n + k).factorial : ℝ)⁻¹ * ‖z ^ (n + k)‖ := by
            simp only [hf, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
          rw [hnf]
          calc ((n + k).factorial : ℝ)⁻¹ * ‖z ^ (n + k)‖
              ≤ ((n + k).factorial : ℝ)⁻¹ * ‖z‖ ^ (n + k) := by gcongr; exact norm_pow_le z (n + k)
            _ ≤ (n.factorial : ℝ)⁻¹ * ‖z‖ ^ (n + k) := by gcongr
            _ = ‖z‖ ^ k * ((n.factorial : ℝ)⁻¹ * ‖z‖ ^ n) := by rw [pow_add]; ring
    _ = ‖z‖ ^ k * Real.exp ‖z‖ := by rw [tsum_mul_left, hexp_eq]

/-- **First-order remainder bound for the exponential.** In a Banach algebra,
`‖exp z - 1‖ ≤ ‖z‖ · Real.exp ‖z‖`. The `k = 1` instance of `norm_exp_sub_sum_le`: the order-1
Taylor partial sum is `1`. It is the first-order sibling of `norm_exp_sub_one_sub_id_le` (`k = 2`)
and `norm_exp_sub_one_sub_id_sub_half_sq_le` (`k = 3`); it controls each factor `exp(s•gᵢ) - 1` of a
Trotter slice `∏ᵢ exp(s•gᵢ)` written as `∏ᵢ (1 + (exp(s•gᵢ) - 1))`. -/
theorem norm_exp_sub_one_le (z : 𝔸) : ‖exp z - 1‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
  simpa [Finset.sum_range_one] using norm_exp_sub_sum_le z 1

/-- **Second-order remainder bound for the exponential.** In a Banach algebra,
`‖exp z - 1 - z‖ ≤ ‖z‖² · Real.exp ‖z‖`. The `k = 2` instance of `norm_exp_sub_sum_le`: the order-2
Taylor partial sum is `1 + z`. -/
theorem norm_exp_sub_one_sub_id_le (z : 𝔸) :
    ‖exp z - 1 - z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
  simpa [Finset.sum_range_succ, sub_sub] using norm_exp_sub_sum_le z 2

/-- **Third-order remainder bound for the exponential.** In a Banach algebra,
`‖exp z - 1 - z - z²/2‖ ≤ ‖z‖³ · Real.exp ‖z‖`. The `k = 3` instance of `norm_exp_sub_sum_le`: the
order-3 Taylor partial sum is `1 + z + z²/2`. This one-order-higher remainder is what powers the
*symmetric* (second-order) splitting estimate
`exists_norm_exp_smul_mul_exp_two_smul_mul_exp_smul_sub_le`. -/
theorem norm_exp_sub_one_sub_id_sub_half_sq_le (z : 𝔸) :
    ‖exp z - 1 - z - (2 : ℝ)⁻¹ • z ^ 2‖ ≤ ‖z‖ ^ 3 * Real.exp ‖z‖ := by
  simpa [Finset.sum_range_succ, sub_sub] using norm_exp_sub_sum_le z 3

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
/-- **Product-linearization bound with an exponential remainder.** In a normed ring, the product
`∏ᵢ (1 + aᵢ)` over a finite list agrees with its linearization `1 + ∑ᵢ aᵢ` up to a remainder
controlled by the total norm `S = ∑ᵢ ‖aᵢ‖`:
`‖(∏ᵢ (1 + aᵢ)) - 1 - ∑ᵢ aᵢ‖ ≤ S² · Real.exp S`.
This is the closed form of `norm_prod_one_add_sub_one_sub_sum_le`: the scalar right-hand side
`(∏ᵢ (1 + ‖aᵢ‖)) - 1 - S` is bounded, via `prod_one_add_norm_le_exp`, by `Real.exp S - 1 - S`, and
then by `S² · Real.exp S` using the second-order exponential remainder `norm_exp_sub_one_sub_id_le`
at `ℝ`. The bound is genuinely second order in `S`, with an explicit `Real.exp S` factor rather than
an `exp(S)`-type prefactor hidden inside an existential constant. Applied to `aᵢ = exp(s•gᵢ) - 1` it
controls how far one Trotter slice `∏ᵢ exp(s•gᵢ)` sits from its linearization uniformly in the list
length — the quantitative core behind an exponential-prefactor-free first-order Lie–Trotter
estimate. (The statement uses `exp` only through the real exponential, so no structure beyond a
normed ring is required.) -/
theorem norm_prod_one_add_sub_one_sub_sum_le_exp (c : List 𝔸) :
    ‖(c.map fun a => 1 + a).prod - 1 - c.sum‖
      ≤ (c.map fun a => ‖a‖).sum ^ 2 * Real.exp ((c.map fun a => ‖a‖).sum) := by
  set S := (c.map fun a => ‖a‖).sum with hS
  have hSnn : 0 ≤ S := by
    rw [hS]; exact List.sum_nonneg fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; exact norm_nonneg y
  have hprod : (c.map fun a => 1 + ‖a‖).prod ≤ Real.exp S := hS ▸ prod_one_add_norm_le_exp c
  have hrem : Real.exp S - 1 - S ≤ S ^ 2 * Real.exp S := by
    have hbridge : NormedSpace.exp S = Real.exp S := (congrFun Real.exp_eq_exp_ℝ S).symm
    have h := NormedSpace.norm_exp_sub_one_sub_id_le (S : ℝ)
    rw [hbridge] at h
    have hnv : ‖S‖ = S := by rw [Real.norm_eq_abs, abs_of_nonneg hSnn]
    rw [hnv] at h
    calc Real.exp S - 1 - S ≤ |Real.exp S - 1 - S| := le_abs_self _
      _ = ‖Real.exp S - 1 - S‖ := (Real.norm_eq_abs _).symm
      _ ≤ S ^ 2 * Real.exp S := h
  calc ‖(c.map fun a => 1 + a).prod - 1 - c.sum‖
      ≤ (c.map fun a => 1 + ‖a‖).prod - 1 - S := norm_prod_one_add_sub_one_sub_sum_le c
    _ ≤ Real.exp S - 1 - S := by linarith
    _ ≤ S ^ 2 * Real.exp S := hrem

/-- The **explicit numerical Lie–Trotter constant** `2e + e²·eᵉ`, i.e.
`2·Real.exp 1 + Real.exp 1 ^ 2 · Real.exp (Real.exp 1)`, of the unitarity-aware first-order and
`k`-fold Trotter product-formula bounds `norm_prod_exp_smul_sub_exp_smul_sum_le_sq` and
`norm_prod_exp_inv_smul_pow_sub_exp_sum_le_sq`. A single fixed real — independent of the list, the
scalar, and the step count `k` — the *one source of truth* both bounds reference; it is the
numerical part of Nielsen & Chuang, *Quantum Computation and Quantum Information*, Problem 4.3(6)'s
`O(4ⁿ)` Trotter constant. -/
noncomputable def trotterProductConst : ℝ :=
  2 * Real.exp 1 + Real.exp 1 ^ 2 * Real.exp (Real.exp 1)

/-- The Lie–Trotter product-formula constant `trotterProductConst` is nonnegative. -/
theorem trotterProductConst_nonneg : 0 ≤ trotterProductConst := by
  unfold trotterProductConst; positivity

/-- The Lie–Trotter product-formula constant `trotterProductConst` is at least `2`. -/
theorem two_le_trotterProductConst : 2 ≤ trotterProductConst := by
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hpos : 0 ≤ Real.exp 1 ^ 2 * Real.exp (Real.exp 1) := by positivity
  unfold trotterProductConst; nlinarith

/-- **Explicit-constant first-order Lie–Trotter splitting bound.** In a Banach algebra, for a list
`l : List 𝔸`, a scalar `s ≥ 0`, and total norm `Λ = ∑ᵢ ‖gᵢ‖` *in the small-step regime* `s·Λ ≤ 1`,
the ordered product `∏ᵢ exp(s•gᵢ)` agrees with `exp(s • ∑ᵢ gᵢ)` up to a second-order error
carrying a **numerical** constant — no `Real.exp Λ`-type prefactor:
`‖(∏ᵢ exp(s•gᵢ)) - exp(s • ∑ᵢ gᵢ)‖ ≤ (2e + e²·eᵉ)·(s·Λ)²`.

This sharpens `exists_norm_prod_exp_smul_sub_exp_smul_sum_le`, which hides its constant inside an
existential and, being built from the crude two-factor estimate, carries an `Real.exp (∑‖gᵢ‖)`
factor. The constant here is the fixed real
`2·Real.exp 1 + Real.exp 1 ^ 2 · Real.exp (Real.exp 1)`, independent of the list. That explicitness
is what a `k`-fold accumulation needs to reach an `O(Λ²)/k` rate with a *polynomial* (not
exponential) `Λ`-dependence — the operator core behind Nielsen & Chuang, *Quantum Computation and
Quantum Information*, Problem 4.3(6)'s literal `O(n·16ⁿ/ε)` gate count (with `gᵢ = -i hᵢ Pᵢ`,
`Λ = ∑ᵢ |hᵢ|`, and `s = Δ = 1/k` in the regime `k ≥ Λ`).

**Proof.** Write the slice as `∏ᵢ (1 + cᵢ)` with `cᵢ = exp(s•gᵢ) - 1`, and split
`(∏ᵢ(1+cᵢ)) - exp(s•∑g) = [∏ᵢ(1+cᵢ) - 1 - ∑ᵢcᵢ] + [∑ᵢcᵢ - s•∑g] - [exp(s•∑g) - 1 - s•∑g]`. In the
regime `s·Λ ≤ 1` each `s‖gᵢ‖ ≤ 1` (a summand is at most the sum, `List.single_le_sum`), so
`Real.exp (s‖gᵢ‖) ≤ e`. The first bracket is the product-linearization corollary
`norm_prod_one_add_sub_one_sub_sum_le_exp` at `c`, whose scalar remainder `∑‖cᵢ‖ ≤ e·s·Λ`
(`norm_exp_sub_one_le` factorwise) gives `≤ e²·eᵉ·(sΛ)²`; the second bracket, via the identity
`∑ᵢcᵢ - s•∑g = ∑ᵢ(exp(s•gᵢ) - 1 - s•gᵢ)` and `norm_exp_sub_one_sub_id_le` termwise (using
`(s‖gᵢ‖)² ≤ s‖gᵢ‖·sΛ`), is `≤ e·(sΛ)²`; the third is `norm_exp_sub_one_sub_id_le` at `s•∑g`
directly, `≤ e·(sΛ)²`. -/
theorem norm_prod_exp_smul_sub_exp_smul_sum_le_sq (l : List 𝔸) {s : ℝ} (hs : 0 ≤ s)
    (hsΛ : s * (l.map fun g => ‖g‖).sum ≤ 1) :
    ‖(l.map fun g => exp (s • g)).prod - exp (s • l.sum)‖
      ≤ trotterProductConst * (s * (l.map fun g => ‖g‖).sum) ^ 2 := by
  unfold trotterProductConst
  set Λ := (l.map fun g => ‖g‖).sum with hΛ
  set e1 : ℝ := Real.exp 1 with he1
  have he1pos : 0 < e1 := Real.exp_pos 1
  have hΛnn : 0 ≤ Λ := by
    rw [hΛ]; exact List.sum_nonneg fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; exact norm_nonneg _
  have hsmul : ∀ g : 𝔸, ‖s • g‖ = s * ‖g‖ := fun g => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  have hsingle : ∀ g ∈ l, ‖g‖ ≤ Λ := by
    intro g hg; rw [hΛ]
    exact List.single_le_sum
      (fun x hx => by rw [List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; exact norm_nonneg _)
      ‖g‖ (List.mem_map.mpr ⟨g, hg, rfl⟩)
  have hsg1 : ∀ g ∈ l, s * ‖g‖ ≤ 1 := fun g hg =>
    le_trans (mul_le_mul_of_nonneg_left (hsingle g hg) hs) hsΛ
  -- MAIN term: the product-linearization corollary at `cᵢ = exp(s•gᵢ) - 1`.
  have hcprod : ((l.map fun g => exp (s • g) - 1).map fun a => 1 + a).prod
      = (l.map fun g => exp (s • g)).prod := by
    congr 1
    rw [List.map_map]
    refine List.map_congr_left (fun g _ => ?_)
    simp only [Function.comp_apply]; abel
  have hcor := norm_prod_one_add_sub_one_sub_sum_le_exp (l.map fun g => exp (s • g) - 1)
  rw [hcprod] at hcor
  simp only [List.map_map, Function.comp_def] at hcor
  set D := (l.map fun g => ‖exp (s • g) - 1‖).sum with hD
  have hDnn : 0 ≤ D := by
    rw [hD]; exact List.sum_nonneg fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; exact norm_nonneg _
  have hDbound : D ≤ e1 * (s * Λ) := by
    calc D ≤ (l.map fun g => (e1 * s) * ‖g‖).sum := by
          refine List.sum_le_sum (fun g hg => ?_)
          calc ‖exp (s • g) - 1‖ ≤ ‖s • g‖ * Real.exp ‖s • g‖ := norm_exp_sub_one_le _
            _ = (s * ‖g‖) * Real.exp (s * ‖g‖) := by rw [hsmul]
            _ ≤ (s * ‖g‖) * e1 := by
                apply mul_le_mul_of_nonneg_left _ (mul_nonneg hs (norm_nonneg g))
                rw [he1]; exact Real.exp_le_exp.mpr (hsg1 g hg)
            _ = (e1 * s) * ‖g‖ := by ring
      _ = (e1 * s) * Λ := by rw [List.sum_map_mul_left, ← hΛ]
      _ = e1 * (s * Λ) := by ring
  have he1sΛ : e1 * (s * Λ) ≤ e1 := mul_le_of_le_one_right he1pos.le hsΛ
  have hDe1 : D ≤ e1 := hDbound.trans he1sΛ
  have hMAIN : ‖(l.map fun g => exp (s • g)).prod - 1 - (l.map fun g => exp (s • g) - 1).sum‖
      ≤ e1 ^ 2 * Real.exp e1 * (s * Λ) ^ 2 := by
    refine hcor.trans ?_
    calc D ^ 2 * Real.exp D ≤ (e1 * (s * Λ)) ^ 2 * Real.exp e1 := by
          apply mul_le_mul (pow_le_pow_left₀ hDnn hDbound 2) (Real.exp_le_exp.mpr hDe1)
            (Real.exp_pos _).le (by positivity)
      _ = e1 ^ 2 * Real.exp e1 * (s * Λ) ^ 2 := by ring
  -- MID term: `∑(exp(s•gᵢ) - 1) - s•∑g = ∑(exp(s•gᵢ) - 1 - s•gᵢ)`, bounded by `e·(sΛ)²`.
  have hMIDeq : (l.map fun g => exp (s • g) - 1).sum - s • l.sum
      = (l.map fun g => exp (s • g) - 1 - s • g).sum := by
    rw [show (fun g : 𝔸 => exp (s • g) - 1)
        = (fun g => (exp (s • g) - 1 - s • g) + s • g) from by funext g; abel,
      List.sum_map_add, ← List.smul_sum]
    abel
  have hnormsum : ‖(l.map fun g => exp (s • g) - 1 - s • g).sum‖
      ≤ (l.map fun g => ‖exp (s • g) - 1 - s • g‖).sum := by
    have := norm_multiset_sum_le ((l.map fun g => exp (s • g) - 1 - s • g) : Multiset 𝔸)
    simpa [List.map_map, Function.comp_def] using this
  have hMID : ‖(l.map fun g => exp (s • g) - 1).sum - s • l.sum‖ ≤ e1 * (s * Λ) ^ 2 := by
    rw [hMIDeq]
    refine le_trans hnormsum ?_
    calc (l.map fun g => ‖exp (s • g) - 1 - s • g‖).sum
        ≤ (l.map fun g => (e1 * s * (s * Λ)) * ‖g‖).sum := by
          refine List.sum_le_sum (fun g hg => ?_)
          have h1 : ‖exp (s • g) - 1 - s • g‖ ≤ ‖s • g‖ ^ 2 * Real.exp ‖s • g‖ :=
            norm_exp_sub_one_sub_id_le _
          rw [hsmul] at h1
          refine h1.trans ?_
          calc (s * ‖g‖) ^ 2 * Real.exp (s * ‖g‖)
              ≤ ((s * ‖g‖) * (s * Λ)) * e1 := by
                apply mul_le_mul _ _ (Real.exp_pos _).le
                  (mul_nonneg (mul_nonneg hs (norm_nonneg g)) (mul_nonneg hs hΛnn))
                · rw [sq]
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left (hsingle g hg) hs) (mul_nonneg hs (norm_nonneg g))
                · rw [he1]; exact Real.exp_le_exp.mpr (hsg1 g hg)
            _ = (e1 * s * (s * Λ)) * ‖g‖ := by ring
      _ = (e1 * s * (s * Λ)) * Λ := by rw [List.sum_map_mul_left, ← hΛ]
      _ = e1 * (s * Λ) ^ 2 := by ring
  -- TAIL term: the single-exponential remainder at `s•∑g`.
  have hlsum : ‖l.sum‖ ≤ Λ := by
    rw [hΛ]; simpa using norm_multiset_sum_le (l : Multiset 𝔸)
  have hnorm : ‖s • l.sum‖ ≤ s * Λ := by
    rw [hsmul]; exact mul_le_mul_of_nonneg_left hlsum hs
  have hTAIL : ‖exp (s • l.sum) - 1 - s • l.sum‖ ≤ e1 * (s * Λ) ^ 2 := by
    refine (norm_exp_sub_one_sub_id_le _).trans ?_
    calc ‖s • l.sum‖ ^ 2 * Real.exp ‖s • l.sum‖ ≤ (s * Λ) ^ 2 * e1 := by
          apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) _ (Real.exp_pos _).le
            (by positivity)
          rw [he1]; exact Real.exp_le_exp.mpr (le_trans hnorm hsΛ)
      _ = e1 * (s * Λ) ^ 2 := by ring
  -- Assemble the three brackets by the triangle inequality.
  have hsplit : (l.map fun g => exp (s • g)).prod - exp (s • l.sum)
      = ((l.map fun g => exp (s • g)).prod - 1 - (l.map fun g => exp (s • g) - 1).sum)
        + ((l.map fun g => exp (s • g) - 1).sum - s • l.sum)
        - (exp (s • l.sum) - 1 - s • l.sum) := by abel
  rw [hsplit]
  calc ‖((l.map fun g => exp (s • g)).prod - 1 - (l.map fun g => exp (s • g) - 1).sum)
          + ((l.map fun g => exp (s • g) - 1).sum - s • l.sum)
          - (exp (s • l.sum) - 1 - s • l.sum)‖
      ≤ ‖((l.map fun g => exp (s • g)).prod - 1 - (l.map fun g => exp (s • g) - 1).sum)
            + ((l.map fun g => exp (s • g) - 1).sum - s • l.sum)‖
          + ‖exp (s • l.sum) - 1 - s • l.sum‖ := norm_sub_le _ _
    _ ≤ (e1 ^ 2 * Real.exp e1 * (s * Λ) ^ 2 + e1 * (s * Λ) ^ 2) + e1 * (s * Λ) ^ 2 :=
        add_le_add ((norm_add_le _ _).trans (add_le_add hMAIN hMID)) hTAIL
    _ = (2 * e1 + e1 ^ 2 * Real.exp e1) * (s * Λ) ^ 2 := by ring

/-- The key second-order estimate behind the Lie–Trotter formula: for `0 ≤ t ≤ 1`,
`exp(t•x) exp(t•y)` and `exp(t•x + t•y)` agree up to `O(t²)`. Both equal `1 + t•(x+y) + O(t²)`; the
difference is controlled by the remainder bound `norm_exp_sub_one_sub_id_le`. -/
private theorem norm_exp_smul_mul_exp_smul_sub_le (x y : 𝔸) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖exp (t • x) * exp (t • y) - exp (t • x + t • y)‖
      ≤ (‖x‖ ^ 2 * Real.exp (‖x‖ + ‖y‖) ^ 2 + (1 + ‖x‖) * ‖y‖ ^ 2 * Real.exp (‖x‖ + ‖y‖)
          + ‖x‖ * ‖y‖ + (‖x‖ + ‖y‖) ^ 2 * Real.exp (‖x‖ + ‖y‖)) * t ^ 2 := by
  set a := ‖x‖ with ha
  set b := ‖y‖ with hb
  set E := Real.exp (a + b) with hE
  have hann : 0 ≤ a := norm_nonneg x
  have hbnn : 0 ≤ b := norm_nonneg y
  have hnx : ‖t • x‖ = t * a := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hny : ‖t • y‖ = t * b := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hta : t * a ≤ a + b := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) hann]
  have htb : t * b ≤ a + b := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) hbnn]
  -- the algebraic identity `pq - r = R(u)·q + (1+u)·R(v) + u·v - R(u+v)` with `R z = exp z - 1 - z`
  have hid : exp (t • x) * exp (t • y) - exp (t • x + t • y)
      = (exp (t • x) - 1 - t • x) * exp (t • y)
        + (1 + t • x) * (exp (t • y) - 1 - t • y)
        + (t • x) * (t • y)
        - (exp (t • x + t • y) - 1 - (t • x + t • y)) := by
    simp only [add_mul, sub_mul, mul_sub, one_mul, mul_one]; abel
  have hT1 : ‖(exp (t • x) - 1 - t • x) * exp (t • y)‖ ≤ a ^ 2 * E ^ 2 * t ^ 2 := by
    refine (norm_mul_le _ _).trans ?_
    have h1 : ‖exp (t • x) - 1 - t • x‖ ≤ (t * a) ^ 2 * E := by
      refine (norm_exp_sub_one_sub_id_le _).trans ?_
      rw [hnx]; gcongr; exact Real.exp_le_exp.mpr hta
    have h2 : ‖exp (t • y)‖ ≤ E :=
      (norm_exp_le _).trans (by rw [hny]; exact Real.exp_le_exp.mpr htb)
    calc ‖exp (t • x) - 1 - t • x‖ * ‖exp (t • y)‖
        ≤ ((t * a) ^ 2 * E) * E := by gcongr
      _ = a ^ 2 * E ^ 2 * t ^ 2 := by ring
  have hT2 : ‖(1 + t • x) * (exp (t • y) - 1 - t • y)‖ ≤ (1 + a) * b ^ 2 * E * t ^ 2 := by
    refine (norm_mul_le _ _).trans ?_
    have h1 : ‖(1 : 𝔸) + t • x‖ ≤ 1 + a := by
      refine (norm_add_le _ _).trans ?_; rw [norm_one, hnx]; nlinarith
    have h2 : ‖exp (t • y) - 1 - t • y‖ ≤ (t * b) ^ 2 * E := by
      refine (norm_exp_sub_one_sub_id_le _).trans ?_
      rw [hny]; gcongr; exact Real.exp_le_exp.mpr htb
    calc ‖(1 : 𝔸) + t • x‖ * ‖exp (t • y) - 1 - t • y‖
        ≤ (1 + a) * ((t * b) ^ 2 * E) := by gcongr
      _ = (1 + a) * b ^ 2 * E * t ^ 2 := by ring
  have hT3 : ‖(t • x) * (t • y)‖ ≤ a * b * t ^ 2 := by
    refine (norm_mul_le _ _).trans (le_of_eq ?_); rw [hnx, hny]; ring
  have hT4 : ‖exp (t • x + t • y) - 1 - (t • x + t • y)‖ ≤ (a + b) ^ 2 * E * t ^ 2 := by
    refine (norm_exp_sub_one_sub_id_le _).trans ?_
    have hw : ‖t • x + t • y‖ ≤ t * (a + b) := by
      refine (norm_add_le _ _).trans (le_of_eq ?_); rw [hnx, hny]; ring
    have hwsq : ‖t • x + t • y‖ ^ 2 ≤ (t * (a + b)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    have hexpw : Real.exp ‖t • x + t • y‖ ≤ E :=
      Real.exp_le_exp.mpr (le_trans hw (by nlinarith))
    calc ‖t • x + t • y‖ ^ 2 * Real.exp ‖t • x + t • y‖
        ≤ (t * (a + b)) ^ 2 * E := by gcongr
      _ = (a + b) ^ 2 * E * t ^ 2 := by ring
  rw [hid]
  calc ‖(exp (t • x) - 1 - t • x) * exp (t • y) + (1 + t • x) * (exp (t • y) - 1 - t • y)
          + (t • x) * (t • y) - (exp (t • x + t • y) - 1 - (t • x + t • y))‖
      ≤ ‖(exp (t • x) - 1 - t • x) * exp (t • y)‖ + ‖(1 + t • x) * (exp (t • y) - 1 - t • y)‖
          + ‖(t • x) * (t • y)‖ + ‖exp (t • x + t • y) - 1 - (t • x + t • y)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add₃_le
    _ ≤ a ^ 2 * E ^ 2 * t ^ 2 + (1 + a) * b ^ 2 * E * t ^ 2 + a * b * t ^ 2
          + (a + b) ^ 2 * E * t ^ 2 := by gcongr
    _ = (a ^ 2 * E ^ 2 + (1 + a) * b ^ 2 * E + a * b + (a + b) ^ 2 * E) * t ^ 2 := by ring

/-- **The Lie product formula** (a.k.a. the **Trotter product formula**; Nielsen & Chuang,
*Quantum Computation and Quantum Information*, Theorem 4.3). In a Banach algebra `𝔸`, for any
`x y : 𝔸`,
`lim (exp(x/n) exp(y/n))ⁿ = exp(x + y)`,
i.e. `Tendsto (fun n => (exp (n⁻¹ • x) * exp (n⁻¹ • y)) ^ n) atTop (𝓝 (exp (x + y)))`. This holds
even when `x` and `y` do **not** commute.

Nielsen & Chuang state it for Hermitian `A, B` and real `t` as
`lim (e^{iAt/n} e^{iBt/n})ⁿ = e^{i(A+B)t}`; that is the instance `x = (t : ℝ) • (i • A)`,
`y = (t : ℝ) • (i • B)` of the statement here (the exponent's `i`, `t` and Hermiticity are absorbed
into the arbitrary algebra elements `x`, `y`). -/
theorem tendsto_pow_exp_smul_mul_exp_smul (x y : 𝔸) :
    Tendsto (fun n : ℕ => (exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)) ^ n) atTop
      (𝓝 (exp (x + y))) := by
  have : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set E := Real.exp (‖x‖ + ‖y‖) with hE
  set K := ‖x‖ ^ 2 * E ^ 2 + (1 + ‖x‖) * ‖y‖ ^ 2 * E + ‖x‖ * ‖y‖ + (‖x‖ + ‖y‖) ^ 2 * E with hK
  have hEnn : 0 ≤ E := (Real.exp_pos _).le
  -- for `n ≥ 1`, `‖(exp(x/n) exp(y/n))ⁿ - exp(x+y)‖ ≤ (E·K)/n`
  have hbound : ∀ n : ℕ, 1 ≤ n →
      ‖(exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)) ^ n - exp (x + y)‖ ≤ E * K * (n : ℝ)⁻¹ := by
    intro n hn
    set t := (n : ℝ)⁻¹ with ht
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hn'
    have ht0 : 0 ≤ t := by rw [ht]; positivity
    have ht1 : t ≤ 1 := by rw [ht]; exact inv_le_one_of_one_le₀ (by exact_mod_cast hn)
    have hnx : ‖t • x‖ = t * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    have hny : ‖t • y‖ = t * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    -- a common bound `M = exp((‖x‖+‖y‖)·t)` on `‖aₙ‖` and `‖bₙ‖`, with `Mⁿ = E`
    have haₙ : ‖exp (t • x) * exp (t • y)‖ ≤ Real.exp ((‖x‖ + ‖y‖) * t) := by
      refine (norm_mul_le _ _).trans ?_
      calc ‖exp (t • x)‖ * ‖exp (t • y)‖
          ≤ Real.exp ‖t • x‖ * Real.exp ‖t • y‖ :=
            mul_le_mul (norm_exp_le _) (norm_exp_le _) (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp ((‖x‖ + ‖y‖) * t) := by
              rw [← Real.exp_add, show ‖t • x‖ + ‖t • y‖ = (‖x‖ + ‖y‖) * t by rw [hnx, hny]; ring]
    have hbₙ : ‖exp (t • x + t • y)‖ ≤ Real.exp ((‖x‖ + ‖y‖) * t) := by
      refine (norm_exp_le _).trans (Real.exp_le_exp.mpr ?_)
      refine (norm_add_le _ _).trans (le_of_eq ?_); rw [hnx, hny]; ring
    have hc1 : (1 : ℝ) ≤ Real.exp ((‖x‖ + ‖y‖) * t) := Real.one_le_exp (by positivity)
    have hnt1 : (n : ℝ) * t = 1 := by rw [ht]; exact mul_inv_cancel₀ hne
    have hexpo : (n : ℝ) * ((‖x‖ + ‖y‖) * t) = ‖x‖ + ‖y‖ := by
      calc (n : ℝ) * ((‖x‖ + ‖y‖) * t) = ((n : ℝ) * t) * (‖x‖ + ‖y‖) := by ring
        _ = 1 * (‖x‖ + ‖y‖) := by rw [hnt1]
        _ = ‖x‖ + ‖y‖ := one_mul _
    have hcpow : Real.exp ((‖x‖ + ‖y‖) * t) ^ n = E := by rw [← Real.exp_natCast_mul, hexpo]
    have hpow := norm_pow_sub_pow_le haₙ hbₙ hc1 n
    rw [hcpow] at hpow
    have key_smul : ∀ w : 𝔸, n • (t • w) = w := by
      intro w
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ht, mul_inv_cancel₀ hne, one_smul]
    have hbpow : exp (t • x + t • y) ^ n = exp (x + y) := by
      rw [← exp_nsmul, smul_add, key_smul, key_smul]
    rw [hbpow] at hpow
    have haux := norm_exp_smul_mul_exp_smul_sub_le x y ht0 ht1
    rw [← hE, ← hK] at haux
    have hnt : (n : ℝ) * t ^ 2 = t := by rw [pow_two, ← mul_assoc, hnt1, one_mul]
    calc ‖(exp (t • x) * exp (t • y)) ^ n - exp (x + y)‖
        ≤ ↑n * E * ‖exp (t • x) * exp (t • y) - exp (t • x + t • y)‖ := hpow
      _ ≤ ↑n * E * (K * t ^ 2) := mul_le_mul_of_nonneg_left haux (by positivity)
      _ = E * K * (↑n * t ^ 2) := by ring
      _ = E * K * t := by rw [hnt]
  have htend : Tendsto (fun n : ℕ => E * K * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using h0.const_mul (E * K)
  refine squeeze_zero' ?_ ?_ htend
  · exact Eventually.of_forall fun n => norm_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with n hn using hbound n hn

/-- Existential repackaging of `norm_exp_smul_mul_exp_smul_sub_le`: for `x y : 𝔸` there is a
constant `K ≥ 0` (depending only on `x`, `y`) with
`‖exp(t•x) exp(t•y) - exp(t•x + t•y)‖ ≤ K·t²` for all `t ∈ [0, 1]`. This hides the explicit second
-order constant so it can be threaded through the induction in
`exists_norm_prod_exp_smul_sub_exp_smul_sum_le`. -/
private theorem exists_norm_exp_smul_mul_exp_smul_sub_le (x y : 𝔸) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖exp (t • x) * exp (t • y) - exp (t • x + t • y)‖ ≤ K * t ^ 2 := by
  refine ⟨_, ?_, fun t ht0 ht1 => norm_exp_smul_mul_exp_smul_sub_le x y ht0 ht1⟩
  positivity

/-- **First-order error of the Lie–Trotter splitting of a finite product.** For a list `l : List 𝔸`
in a Banach algebra there is a constant `C ≥ 0` (depending only on `l`) such that, for every
`t ∈ [0, 1]`,
`‖(∏ g ∈ l, exp(t•g)) - exp(t • ∑ g ∈ l, g)‖ ≤ C·t²`,
where the product is taken in the list's order. In other words, splitting `exp(t • ∑ gᵢ)` as the
ordered product `∏ exp(t•gᵢ)` incurs only a second-order (`O(t²)`) error, even though the `gᵢ` need
not commute.

This is the operator content of Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Problem 4.3(4): taking `gᵢ = -i·hᵢ·Pᵢ` (real `hᵢ`, Pauli-string operators `Pᵢ`) and `t = Δ` gives
`exp(-iHΔ) = ∏ᵢ exp(-i hᵢ Pᵢ Δ) + O(Δ²)` for `H = ∑ᵢ hᵢ Pᵢ`.

The proof is induction on `l`: the empty product is exact, and the cons step inserts
`exp(t•a)·exp(t • ∑ l)` between the two sides, bounding the first gap by the inductive hypothesis
(scaled by `‖exp(t•a)‖ ≤ Real.exp ‖a‖`) and the second by the two-factor estimate
`exists_norm_exp_smul_mul_exp_smul_sub_le`. -/
theorem exists_norm_prod_exp_smul_sub_exp_smul_sum_le (l : List 𝔸) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖(l.map fun g => exp (t • g)).prod - exp (t • l.sum)‖ ≤ C * t ^ 2 := by
  induction l with
  | nil => exact ⟨0, le_refl 0, fun t _ _ => by simp [NormedSpace.exp_zero]⟩
  | cons a l ih =>
    obtain ⟨C', hC'0, hC'⟩ := ih
    obtain ⟨K, hK0, hK⟩ := exists_norm_exp_smul_mul_exp_smul_sub_le a l.sum
    refine ⟨Real.exp ‖a‖ * C' + K, by positivity, fun t ht0 ht1 => ?_⟩
    have hexpa : ‖exp (t • a)‖ ≤ Real.exp ‖a‖ := by
      refine (norm_exp_le _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      exact mul_le_of_le_one_left (norm_nonneg a) ht1
    have hmap : ((a :: l).map fun g => exp (t • g)).prod
        = exp (t • a) * (l.map fun g => exp (t • g)).prod := by
      rw [List.map_cons, List.prod_cons]
    calc ‖((a :: l).map fun g => exp (t • g)).prod - exp (t • (a :: l).sum)‖
        = ‖exp (t • a) * (l.map fun g => exp (t • g)).prod - exp (t • a + t • l.sum)‖ := by
          rw [hmap, List.sum_cons, smul_add]
      _ ≤ ‖exp (t • a) * (l.map fun g => exp (t • g)).prod - exp (t • a) * exp (t • l.sum)‖
            + ‖exp (t • a) * exp (t • l.sum) - exp (t • a + t • l.sum)‖ := by
          have hsplit :
              exp (t • a) * (l.map fun g => exp (t • g)).prod - exp (t • a + t • l.sum)
                = (exp (t • a) * (l.map fun g => exp (t • g)).prod
                    - exp (t • a) * exp (t • l.sum))
                  + (exp (t • a) * exp (t • l.sum) - exp (t • a + t • l.sum)) := by abel
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ Real.exp ‖a‖ * C' * t ^ 2 + K * t ^ 2 := by
          refine add_le_add ?_ (hK t ht0 ht1)
          rw [← mul_sub]
          refine (norm_mul_le _ _).trans ?_
          calc ‖exp (t • a)‖ * ‖(l.map fun g => exp (t • g)).prod - exp (t • l.sum)‖
              ≤ Real.exp ‖a‖ * (C' * t ^ 2) :=
                mul_le_mul hexpa (hC' t ht0 ht1) (norm_nonneg _) (Real.exp_pos _).le
            _ = Real.exp ‖a‖ * C' * t ^ 2 := by ring
      _ = (Real.exp ‖a‖ * C' + K) * t ^ 2 := by ring

/-- **The norm of a product of exponentials is bounded by the exponential of the scaled sum of the
norms.** In a Banach algebra, for `s ≥ 0` and a list `l : List 𝔸`,
`‖∏ g ∈ l, exp(s•g)‖ ≤ Real.exp (s · ∑ g ∈ l, ‖g‖)`.
Submultiplicativity gives `‖exp(s•g)‖ ≤ Real.exp (s‖g‖)` on each factor, and `Real.exp_add` turns
the product of these bounds into `Real.exp` of the sum. This controls both bases of the telescoping
step in `exists_norm_prod_exp_inv_smul_pow_sub_exp_sum_le`. -/
theorem norm_prod_exp_smul_le (l : List 𝔸) {s : ℝ} (hs : 0 ≤ s) :
    ‖(l.map fun g => exp (s • g)).prod‖ ≤ Real.exp (s * (l.map fun g => ‖g‖).sum) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons]
    refine (norm_mul_le _ _).trans ?_
    rw [List.map_cons, List.sum_cons, mul_add, Real.exp_add]
    refine mul_le_mul ?_ ih (norm_nonneg _) (Real.exp_pos _).le
    refine (norm_exp_le _).trans (le_of_eq ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]

/-- **Accumulated first-order error of the `k`-fold Lie–Trotter approximation.** For a list
`l : List 𝔸` in a Banach algebra there is a constant `C ≥ 0` (depending only on `l`) such that, for
every positive integer `k`,
`‖(∏ g ∈ l, exp(k⁻¹•g))^k - exp(∑ g ∈ l, g)‖ ≤ C·k⁻¹`,
where the product is taken in the list's order. Splitting `exp(∑ gᵢ)` into `k` slices of the ordered
product `∏ exp(k⁻¹•gᵢ)` and iterating `k` times drives the total error to zero as `k → ∞`, at rate
`O(k⁻¹)`.

This is the operator content of Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Problem 4.3(5): with `gᵢ = -i·hᵢ·Pᵢ`, `Δ = k⁻¹` and `H = ∑ᵢ hᵢ Pᵢ` (so `exp(∑ gᵢ) = exp(-iH) = U`),
`U = [∏ᵢ exp(-i hᵢ Pᵢ Δ)]^k + O(Δ)`.

The proof combines the per-slice bound `exists_norm_prod_exp_smul_sub_exp_smul_sum_le` (error
`C₁·k⁻²` at `t = k⁻¹`) with the noncommutative telescoping estimate `norm_pow_sub_pow_le`: the
`k`-th powers differ by at most `k · Mᵏ · (per-slice error)`, where `M = Real.exp(k⁻¹·∑‖gᵢ‖)` bounds
both bases and `Mᵏ = Real.exp(∑‖gᵢ‖)` is independent of `k`; the surviving factor `k · k⁻² = k⁻¹` is
the claimed rate. -/
theorem exists_norm_prod_exp_inv_smul_pow_sub_exp_sum_le (l : List 𝔸) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ‖((l.map fun g => exp ((k : ℝ)⁻¹ • g)).prod) ^ k - exp l.sum‖ ≤ C * (k : ℝ)⁻¹ := by
  have : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_prod_exp_smul_sub_exp_smul_sum_le l
  -- `‖∑ g‖ ≤ ∑‖g‖` is the library lemma `norm_multiset_sum_le` on the underlying multiset
  have hSnorm : ‖l.sum‖ ≤ (l.map fun g => ‖g‖).sum := by
    simpa using norm_multiset_sum_le (l : Multiset 𝔸)
  have hNnn : 0 ≤ (l.map fun g => ‖g‖).sum :=
    List.sum_nonneg fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; exact norm_nonneg y
  refine ⟨Real.exp (l.map fun g => ‖g‖).sum * C₁, mul_nonneg (Real.exp_pos _).le hC₁0,
    fun k hk => ?_⟩
  set N := (l.map fun g => ‖g‖).sum with hN
  set t := (k : ℝ)⁻¹ with ht
  have hkne : (k : ℝ) ≠ 0 := by positivity
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht1 : t ≤ 1 := by rw [ht]; exact inv_le_one_of_one_le₀ (by exact_mod_cast hk)
  have hkt : (k : ℝ) * t = 1 := by rw [ht]; exact mul_inv_cancel₀ hkne
  set P := (l.map fun g => exp (t • g)).prod with hP
  set M := Real.exp (t * N) with hM
  have hM1 : 1 ≤ M := Real.one_le_exp (mul_nonneg ht0 hNnn)
  have hPle : ‖P‖ ≤ M := norm_prod_exp_smul_le l ht0
  have hExpSle : ‖exp (t • l.sum)‖ ≤ M := by
    refine (norm_exp_le _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_left hSnorm ht0
  have hMk : M ^ k = Real.exp N := by
    rw [hM, ← Real.exp_natCast_mul]; congr 1; rw [← mul_assoc, hkt, one_mul]
  have hexpk : exp (t • l.sum) ^ k = exp l.sum := by
    rw [← exp_nsmul]; congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hkt, one_smul]
  have hpow := norm_pow_sub_pow_le hPle hExpSle hM1 k
  rw [hexpk, hMk] at hpow
  have hkt2 : (k : ℝ) * t ^ 2 = t := by rw [pow_two, ← mul_assoc, hkt, one_mul]
  calc ‖P ^ k - exp l.sum‖
      ≤ (k : ℝ) * Real.exp N * ‖P - exp (t • l.sum)‖ := hpow
    _ ≤ (k : ℝ) * Real.exp N * (C₁ * t ^ 2) :=
          mul_le_mul_of_nonneg_left (hC₁ t ht0 ht1) (by positivity)
    _ = Real.exp N * C₁ * ((k : ℝ) * t ^ 2) := by ring
    _ = Real.exp N * C₁ * t := by rw [hkt2]

/-- **Explicit-constant `k`-fold Lie–Trotter bound for contraction generators.** In a Banach
algebra, for a list `l : List 𝔸` whose elements — and whose sum `∑ᵢ gᵢ` — generate contractions
(`‖exp(s•gᵢ)‖ ≤ 1` and `‖exp(s•∑g)‖ ≤ 1` for every `s ≥ 0`, e.g. when the `gᵢ` are skew-adjoint so
the exponentials are unitary), the `k`-fold splitting of `exp(∑ᵢ gᵢ)` into `(∏ᵢ exp(k⁻¹•gᵢ))^k`
carries a **numerical**-constant, **polynomial**-in-`Λ` error, `Λ = ∑ᵢ ‖gᵢ‖`:
`‖(∏ᵢ exp(k⁻¹•gᵢ))^k - exp(∑ᵢ gᵢ)‖ ≤ (2e + e²·eᵉ)·Λ²·k⁻¹`.

This sharpens `exists_norm_prod_exp_inv_smul_pow_sub_exp_sum_le`, whose constant is existential and,
being built from the general (non-unitary) two-factor estimate, carries a `Real.exp Λ` factor. Here
the constant is the fixed real `2·Real.exp 1 + Real.exp 1 ^ 2 · Real.exp (Real.exp 1)`, independent
of both `l` and `k`, and the `Λ`-dependence is a clean `Λ²`. That polynomial rate is exactly what
Nielsen & Chuang, *Quantum Computation and Quantum Information*, Problem 4.3(6)'s literal
`O(n·16ⁿ/ε)` gate count needs: with `gᵢ = -i hᵢ Pᵢ` (Pauli-string operators, real `hᵢ`, so the `gᵢ`
are skew-adjoint) and `Δ = k⁻¹`, `Λ = ∑ᵢ |hᵢ| = O(2ⁿ)` gives error `O(4ⁿ)/k`, so achieving accuracy
`ε` needs `k = O(4ⁿ/ε)` steps — no exponential blow-up.

**Proof** (two regimes at the threshold `Λ ≤ k`). Write `t = k⁻¹`, `P = ∏ᵢ exp(t•gᵢ)`,
`Q = exp(t•∑g)`, so `Qᵏ = exp(∑g)` (`exp_nsmul`). Both bases are contractions: `‖P‖ ≤ 1`
(`norm_listProd_le_one`, factorwise from the hypothesis) and `‖Q‖ ≤ 1` (hypothesis). *Regime
`Λ ≤ k`* (so `t·Λ ≤ 1`): the
telescoping bound `norm_pow_sub_pow_le` with `M = 1` gives `‖Pᵏ - Qᵏ‖ ≤ k·‖P - Q‖`, and the explicit
single-step bound `norm_prod_exp_smul_sub_exp_smul_sum_le_sq` gives `‖P - Q‖ ≤ C·(t·Λ)²`; since
`k·t² = t = k⁻¹`, the product is `C·Λ²·k⁻¹`. *Regime `k < Λ`*: `‖Pᵏ - exp(∑g)‖ ≤ ‖Pᵏ‖ + ‖exp(∑g)‖ ≤
2` (both contractions), and `2 ≤ C·Λ²·k⁻¹` because `Λ² > k` (as `Λ > k ≥ 1`) and `C > 2`. -/
theorem norm_prod_exp_inv_smul_pow_sub_exp_sum_le_sq (l : List 𝔸)
    (hg : ∀ g ∈ l, ∀ s : ℝ, 0 ≤ s → ‖exp (s • g)‖ ≤ 1)
    (hsum : ∀ s : ℝ, 0 ≤ s → ‖exp (s • l.sum)‖ ≤ 1)
    {k : ℕ} (hk : 1 ≤ k) :
    ‖((l.map fun g => exp ((k : ℝ)⁻¹ • g)).prod) ^ k - exp l.sum‖
      ≤ trotterProductConst * (l.map fun g => ‖g‖).sum ^ 2 * (k : ℝ)⁻¹ := by
  have : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  set Λ := (l.map fun g => ‖g‖).sum with hΛ
  have hΛnn : 0 ≤ Λ := by
    rw [hΛ]; exact List.sum_nonneg fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; exact norm_nonneg _
  set C := trotterProductConst with hC
  have hC2 : 2 ≤ C := by rw [hC]; exact two_le_trotterProductConst
  have hCnn : 0 ≤ C := le_trans zero_le_two hC2
  set t := (k : ℝ)⁻¹ with ht
  have hkne : (k : ℝ) ≠ 0 := by positivity
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hkt : (k : ℝ) * t = 1 := by rw [ht]; exact mul_inv_cancel₀ hkne
  have hkt2 : (k : ℝ) * t ^ 2 = t := by rw [pow_two, ← mul_assoc, hkt, one_mul]
  set P := (l.map fun g => exp (t • g)).prod with hP
  have hPle : ‖P‖ ≤ 1 := by
    rw [hP]
    exact norm_listProd_le_one fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨g, hgl, rfl⟩ := hx; exact hg g hgl t ht0
  have hexpk : exp (t • l.sum) ^ k = exp l.sum := by
    rw [← exp_nsmul]; congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hkt, one_smul]
  rcases le_or_gt Λ (k : ℝ) with hle | hlt
  · -- Regime `Λ ≤ k`: the explicit single-step bound telescopes with `M = 1`.
    have htΛ : t * Λ ≤ 1 := by
      calc t * Λ ≤ t * (k : ℝ) := mul_le_mul_of_nonneg_left hle ht0
        _ = 1 := by rw [mul_comm]; exact hkt
    have hQle : ‖exp (t • l.sum)‖ ≤ 1 := hsum t ht0
    have hpow := norm_pow_sub_pow_le hPle hQle (le_refl (1 : ℝ)) k
    rw [hexpk, one_pow, mul_one] at hpow
    have hPQ : ‖P - exp (t • l.sum)‖ ≤ C * (t * Λ) ^ 2 :=
      norm_prod_exp_smul_sub_exp_smul_sum_le_sq l ht0 htΛ
    calc ‖P ^ k - exp l.sum‖
        ≤ (k : ℝ) * ‖P - exp (t • l.sum)‖ := hpow
      _ ≤ (k : ℝ) * (C * (t * Λ) ^ 2) := mul_le_mul_of_nonneg_left hPQ (by positivity)
      _ = C * Λ ^ 2 * ((k : ℝ) * t ^ 2) := by ring
      _ = C * Λ ^ 2 * t := by rw [hkt2]
  · -- Regime `k < Λ`: the trivial contraction bound `‖·‖ ≤ 2` already fits `C·Λ²·k⁻¹`.
    have hΛ1 : (1 : ℝ) < Λ := lt_of_le_of_lt (by exact_mod_cast hk) hlt
    have hΛsq : (k : ℝ) ≤ Λ ^ 2 := by
      have hle2 : Λ ≤ Λ ^ 2 := by nlinarith [hΛ1]
      linarith
    have hfrac : 1 ≤ Λ ^ 2 * t := by
      have h := mul_le_mul_of_nonneg_right hΛsq ht0
      rwa [hkt] at h
    have htriv : ‖P ^ k - exp l.sum‖ ≤ 2 := by
      have hPk : ‖P ^ k‖ ≤ 1 := le_trans (norm_pow_le P k) (pow_le_one₀ (norm_nonneg P) hPle)
      have hE : ‖exp l.sum‖ ≤ 1 := by
        have h := hsum 1 zero_le_one; rwa [one_smul] at h
      calc ‖P ^ k - exp l.sum‖ ≤ ‖P ^ k‖ + ‖exp l.sum‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add hPk hE
        _ = 2 := by norm_num
    refine htriv.trans ?_
    calc (2 : ℝ) ≤ C := hC2
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * (Λ ^ 2 * t) := mul_le_mul_of_nonneg_left hfrac hCnn
      _ = C * Λ ^ 2 * t := by ring

/-- **Symmetric (Strang) second-order splitting error of `exp`.** In a Banach algebra, for `x y : 𝔸`
there is a constant `K ≥ 0` (depending only on `x`, `y`) such that, for every `t ∈ [0, 1]`,
`‖exp(t•x) · exp((2t)•y) · exp(t•x) - exp((2t)•(x + y))‖ ≤ K·t³`.

Unlike the plain (unsymmetric) two-factor splitting `exp(t•x) exp(t•y) ≈ exp(t•(x+y))`, which is
only accurate to `O(t²)` (`norm_exp_smul_mul_exp_smul_sub_le`), the **palindromic** product
`exp(t•x) exp((2t)•y) exp(t•x)` approximates `exp((2t)•(x + y))` to `O(t³)`: the second-order terms
cancel by symmetry. This is the base case (`L = 1` interior factor) of Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Exercise 4.50(a), and it is the operator content of one
symmetric Trotter–Suzuki step: taking `x = -i·H₁`, `y = -i·H₂` gives
`e^{-iH₁t} e^{-2iH₂t} e^{-iH₁t} = e^{-2i(H₁+H₂)t} + O(t³)`.

**Proof.** Write `exp z = T z + S z` where `T z = 1 + z + z²/2` is the second-order Taylor
polynomial and `S z = exp z - T z` the remainder, `‖S z‖ ≤ ‖z‖³·Real.exp‖z‖` (the bound
`norm_exp_sub_one_sub_id_sub_half_sq_le`). With `u = t•x`, `v = (2t)•y`, `w = (2t)•(x+y)`, split
`exp u · exp v · exp u - exp w = (exp u exp v exp u - Tu Tv Tu) + (Tu Tv Tu - Tw) - S w`.
The first bracket telescopes into three products, each carrying one `S`-factor, hence `O(t³)`. The
middle bracket is a *polynomial* identity: `Tu Tv Tu - Tw` has **no** terms of degree `≤ 2` in
`u, v` — the second-order cancellation — so it factors as `t³·D₃ + t⁴·D₄ + t⁵·D₅ + t⁶·D₆` and is
`O(t³)` on `[0,1]`. The last term is the remainder `S w`. -/
theorem exists_norm_exp_smul_mul_exp_two_smul_mul_exp_smul_sub_le (x y : 𝔸) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖exp (t • x) * exp ((2 * t) • y) * exp (t • x) - exp ((2 * t) • (x + y))‖ ≤ K * t ^ 3 := by
  refine ⟨(‖x‖ ^ 3 * Real.exp ‖x‖ * Real.exp (2 * ‖y‖) * Real.exp ‖x‖
      + 8 * (1 + ‖x‖ + 2⁻¹ * ‖x‖ ^ 2) * ‖y‖ ^ 3 * Real.exp (2 * ‖y‖) * Real.exp ‖x‖
      + (1 + ‖x‖ + 2⁻¹ * ‖x‖ ^ 2) * (1 + 2 * ‖y‖ + 2 * ‖y‖ ^ 2) * (‖x‖ ^ 3 * Real.exp ‖x‖))
    + (‖(x ^ 3 + 2 • (x * y * x) + 2 • (x * y ^ 2) + x ^ 2 * y + 2 • (y ^ 2 * x) + y * x ^ 2 : 𝔸)‖
       + ‖((4⁻¹ : ℝ) • x ^ 4 + 2 • (x * y ^ 2 * x) + x ^ 2 * y * x + x * y * x ^ 2 + x ^ 2 * y ^ 2
          + y ^ 2 * x ^ 2 : 𝔸)‖
       + ‖(x ^ 2 * y ^ 2 * x + x * y ^ 2 * x ^ 2 + (2⁻¹ : ℝ) • (x ^ 2 * y * x ^ 2) : 𝔸)‖
       + ‖((2⁻¹ : ℝ) • (x ^ 2 * y ^ 2 * x ^ 2) : 𝔸)‖)
    + 8 * ‖x + y‖ ^ 3 * Real.exp (2 * ‖x + y‖), by positivity, fun t ht0 ht1 => ?_⟩
  set Tu : 𝔸 := 1 + t • x + (2⁻¹ : ℝ) • (t • x) ^ 2 with hTu
  set Tv : 𝔸 := 1 + (2 * t) • y + (2⁻¹ : ℝ) • ((2 * t) • y) ^ 2 with hTv
  set Tw : 𝔸 := 1 + (2 * t) • (x + y) + (2⁻¹ : ℝ) • ((2 * t) • (x + y)) ^ 2 with hTw
  have hnx : ‖t • x‖ = t * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hny : ‖(2 * t) • y‖ = 2 * t * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnw : ‖(2 * t) • (x + y)‖ = 2 * t * ‖x + y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have htx : t * ‖x‖ ≤ ‖x‖ := by nlinarith [norm_nonneg x]
  -- each `t^n • D` with `n ≥ 3` is bounded by `‖D‖·t³` on `[0,1]`
  have hk : ∀ (n : ℕ) (D : 𝔸), 3 ≤ n → ‖(t ^ n : ℝ) • D‖ ≤ ‖D‖ * t ^ 3 := by
    intro n D hn
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc t ^ n * ‖D‖ ≤ t ^ 3 * ‖D‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht0 ht1 hn) (norm_nonneg D)
      _ = ‖D‖ * t ^ 3 := by ring
  -- third-order remainders `S u`, `S v`, `S w`, each `O(t³)`
  have hSu : ‖exp (t • x) - Tu‖ ≤ ‖x‖ ^ 3 * Real.exp ‖x‖ * t ^ 3 := by
    have heq : exp (t • x) - Tu = exp (t • x) - 1 - (t • x) - (2⁻¹ : ℝ) • (t • x) ^ 2 := by
      rw [hTu]; abel
    rw [heq]
    refine (norm_exp_sub_one_sub_id_sub_half_sq_le (t • x)).trans ?_
    rw [hnx]
    calc (t * ‖x‖) ^ 3 * Real.exp (t * ‖x‖)
        ≤ (t * ‖x‖) ^ 3 * Real.exp ‖x‖ :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htx) (by positivity)
      _ = ‖x‖ ^ 3 * Real.exp ‖x‖ * t ^ 3 := by ring
  have hSv : ‖exp ((2 * t) • y) - Tv‖ ≤ 8 * ‖y‖ ^ 3 * Real.exp (2 * ‖y‖) * t ^ 3 := by
    have heq : exp ((2 * t) • y) - Tv
        = exp ((2 * t) • y) - 1 - ((2 * t) • y) - (2⁻¹ : ℝ) • ((2 * t) • y) ^ 2 := by rw [hTv]; abel
    rw [heq]
    refine (norm_exp_sub_one_sub_id_sub_half_sq_le ((2 * t) • y)).trans ?_
    rw [hny]
    calc (2 * t * ‖y‖) ^ 3 * Real.exp (2 * t * ‖y‖)
        ≤ (2 * t * ‖y‖) ^ 3 * Real.exp (2 * ‖y‖) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [norm_nonneg y]))
            (by positivity)
      _ = 8 * ‖y‖ ^ 3 * Real.exp (2 * ‖y‖) * t ^ 3 := by ring
  have hSw : ‖exp ((2 * t) • (x + y)) - Tw‖ ≤ 8 * ‖x + y‖ ^ 3 * Real.exp (2 * ‖x + y‖) * t ^ 3 := by
    have heq : exp ((2 * t) • (x + y)) - Tw
        = exp ((2 * t) • (x + y)) - 1 - ((2 * t) • (x + y))
          - (2⁻¹ : ℝ) • ((2 * t) • (x + y)) ^ 2 := by rw [hTw]; abel
    rw [heq]
    refine (norm_exp_sub_one_sub_id_sub_half_sq_le ((2 * t) • (x + y))).trans ?_
    rw [hnw]
    calc (2 * t * ‖x + y‖) ^ 3 * Real.exp (2 * t * ‖x + y‖)
        ≤ (2 * t * ‖x + y‖) ^ 3 * Real.exp (2 * ‖x + y‖) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [norm_nonneg (x + y)]))
            (by positivity)
      _ = 8 * ‖x + y‖ ^ 3 * Real.exp (2 * ‖x + y‖) * t ^ 3 := by ring
  -- `O(1)` bounds on the remaining factors
  have hexpu : ‖exp (t • x)‖ ≤ Real.exp ‖x‖ :=
    (norm_exp_le _).trans (Real.exp_le_exp.mpr (by rw [hnx]; exact htx))
  have hexpv : ‖exp ((2 * t) • y)‖ ≤ Real.exp (2 * ‖y‖) :=
    (norm_exp_le _).trans (Real.exp_le_exp.mpr (by rw [hny]; nlinarith [norm_nonneg y]))
  have hTun : ‖Tu‖ ≤ 1 + ‖x‖ + 2⁻¹ * ‖x‖ ^ 2 := by
    have hp : ‖(t • x) ^ 2‖ ≤ ‖x‖ ^ 2 := by
      refine (norm_pow_le _ 2).trans ?_; rw [hnx]
      exact pow_le_pow_left₀ (mul_nonneg ht0 (norm_nonneg x)) htx 2
    have h2 : ‖(2⁻¹ : ℝ) • (t • x) ^ 2‖ ≤ 2⁻¹ * ‖x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]; gcongr
    rw [hTu]
    calc ‖(1 : 𝔸) + t • x + (2⁻¹ : ℝ) • (t • x) ^ 2‖
        ≤ ‖(1 : 𝔸)‖ + ‖t • x‖ + ‖(2⁻¹ : ℝ) • (t • x) ^ 2‖ := norm_add₃_le
      _ ≤ 1 + ‖x‖ + 2⁻¹ * ‖x‖ ^ 2 := by
          rw [norm_one, hnx]; exact add_le_add (add_le_add le_rfl htx) h2
  have hTvn : ‖Tv‖ ≤ 1 + 2 * ‖y‖ + 2 * ‖y‖ ^ 2 := by
    have hp : ‖((2 * t) • y) ^ 2‖ ≤ (2 * ‖y‖) ^ 2 := by
      refine (norm_pow_le _ 2).trans ?_; rw [hny]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg y]) 2
    have h2 : ‖(2⁻¹ : ℝ) • ((2 * t) • y) ^ 2‖ ≤ 2 * ‖y‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
      calc (2⁻¹ : ℝ) * ‖((2 * t) • y) ^ 2‖ ≤ 2⁻¹ * (2 * ‖y‖) ^ 2 := by gcongr
        _ = 2 * ‖y‖ ^ 2 := by ring
    rw [hTv]
    calc ‖(1 : 𝔸) + (2 * t) • y + (2⁻¹ : ℝ) • ((2 * t) • y) ^ 2‖
        ≤ ‖(1 : 𝔸)‖ + ‖(2 * t) • y‖ + ‖(2⁻¹ : ℝ) • ((2 * t) • y) ^ 2‖ := norm_add₃_le
      _ ≤ 1 + 2 * ‖y‖ + 2 * ‖y‖ ^ 2 := by
          rw [norm_one, hny]
          exact add_le_add (add_le_add le_rfl (by nlinarith [norm_nonneg y])) h2
  -- the telescoping (`S`-factor) part: `exp u exp v exp u - Tu Tv Tu`
  have hRest : ‖exp (t • x) * exp ((2 * t) • y) * exp (t • x) - Tu * Tv * Tu‖
      ≤ (‖x‖ ^ 3 * Real.exp ‖x‖ * Real.exp (2 * ‖y‖) * Real.exp ‖x‖
        + 8 * (1 + ‖x‖ + 2⁻¹ * ‖x‖ ^ 2) * ‖y‖ ^ 3 * Real.exp (2 * ‖y‖) * Real.exp ‖x‖
        + (1 + ‖x‖ + 2⁻¹ * ‖x‖ ^ 2) * (1 + 2 * ‖y‖ + 2 * ‖y‖ ^ 2) * (‖x‖ ^ 3 * Real.exp ‖x‖))
          * t ^ 3 := by
    have hid : exp (t • x) * exp ((2 * t) • y) * exp (t • x) - Tu * Tv * Tu
        = (exp (t • x) - Tu) * exp ((2 * t) • y) * exp (t • x)
          + Tu * (exp ((2 * t) • y) - Tv) * exp (t • x)
          + Tu * Tv * (exp (t • x) - Tu) := by noncomm_ring
    rw [hid]
    conv_rhs => rw [add_mul, add_mul]
    refine norm_add₃_le.trans (add_le_add (add_le_add ?_ ?_) ?_)
    · refine norm_mul₃_le.trans ?_
      calc ‖exp (t • x) - Tu‖ * ‖exp ((2 * t) • y)‖ * ‖exp (t • x)‖
          ≤ (‖x‖ ^ 3 * Real.exp ‖x‖ * t ^ 3) * Real.exp (2 * ‖y‖) * Real.exp ‖x‖ := by gcongr
        _ = ‖x‖ ^ 3 * Real.exp ‖x‖ * Real.exp (2 * ‖y‖) * Real.exp ‖x‖ * t ^ 3 := by ring
    · refine norm_mul₃_le.trans ?_
      calc ‖Tu‖ * ‖exp ((2 * t) • y) - Tv‖ * ‖exp (t • x)‖
          ≤ (1 + ‖x‖ + 2⁻¹ * ‖x‖ ^ 2) * (8 * ‖y‖ ^ 3 * Real.exp (2 * ‖y‖) * t ^ 3)
            * Real.exp ‖x‖ := by gcongr
        _ = 8 * (1 + ‖x‖ + 2⁻¹ * ‖x‖ ^ 2) * ‖y‖ ^ 3 * Real.exp (2 * ‖y‖) * Real.exp ‖x‖
            * t ^ 3 := by ring
    · refine norm_mul₃_le.trans ?_
      calc ‖Tu‖ * ‖Tv‖ * ‖exp (t • x) - Tu‖
          ≤ (1 + ‖x‖ + 2⁻¹ * ‖x‖ ^ 2) * (1 + 2 * ‖y‖ + 2 * ‖y‖ ^ 2)
            * (‖x‖ ^ 3 * Real.exp ‖x‖ * t ^ 3) := by gcongr
        _ = (1 + ‖x‖ + 2⁻¹ * ‖x‖ ^ 2) * (1 + 2 * ‖y‖ + 2 * ‖y‖ ^ 2) * (‖x‖ ^ 3 * Real.exp ‖x‖)
            * t ^ 3 := by ring
  -- the polynomial part: `Tu Tv Tu - Tw` has no degree-`≤ 2` terms (the second-order cancellation)
  have hDpoly : ‖Tu * Tv * Tu - Tw‖
      ≤ (‖(x ^ 3 + 2 • (x * y * x) + 2 • (x * y ^ 2) + x ^ 2 * y + 2 • (y ^ 2 * x) + y * x ^ 2 : 𝔸)‖
         + ‖((4⁻¹ : ℝ) • x ^ 4 + 2 • (x * y ^ 2 * x) + x ^ 2 * y * x + x * y * x ^ 2 + x ^ 2 * y ^ 2
            + y ^ 2 * x ^ 2 : 𝔸)‖
         + ‖(x ^ 2 * y ^ 2 * x + x * y ^ 2 * x ^ 2 + (2⁻¹ : ℝ) • (x ^ 2 * y * x ^ 2) : 𝔸)‖
         + ‖((2⁻¹ : ℝ) • (x ^ 2 * y ^ 2 * x ^ 2) : 𝔸)‖) * t ^ 3 := by
    have hfact : Tu * Tv * Tu - Tw
        = t ^ 3 • (x ^ 3 + 2 • (x * y * x) + 2 • (x * y ^ 2) + x ^ 2 * y + 2 • (y ^ 2 * x)
              + y * x ^ 2)
          + t ^ 4 • ((4⁻¹ : ℝ) • x ^ 4 + 2 • (x * y ^ 2 * x) + x ^ 2 * y * x + x * y * x ^ 2
              + x ^ 2 * y ^ 2 + y ^ 2 * x ^ 2)
          + t ^ 5 • (x ^ 2 * y ^ 2 * x + x * y ^ 2 * x ^ 2 + (2⁻¹ : ℝ) • (x ^ 2 * y * x ^ 2))
          + t ^ 6 • ((2⁻¹ : ℝ) • (x ^ 2 * y ^ 2 * x ^ 2)) := by
      rw [hTu, hTv, hTw]; noncomm_ring; module
    rw [hfact]
    conv_rhs => rw [add_mul, add_mul, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (hk 3 _ (by norm_num)) (hk 4 _ (by norm_num))))
      (hk 5 _ (by norm_num)))) (hk 6 _ (by norm_num)))
  calc ‖exp (t • x) * exp ((2 * t) • y) * exp (t • x) - exp ((2 * t) • (x + y))‖
      = ‖(exp (t • x) * exp ((2 * t) • y) * exp (t • x) - Tu * Tv * Tu) + (Tu * Tv * Tu - Tw)
          + (Tw - exp ((2 * t) • (x + y)))‖ := by congr 1; abel
    _ ≤ ‖exp (t • x) * exp ((2 * t) • y) * exp (t • x) - Tu * Tv * Tu‖ + ‖Tu * Tv * Tu - Tw‖
          + ‖Tw - exp ((2 * t) • (x + y))‖ := norm_add₃_le
    _ ≤ _ := by
        conv_rhs => rw [add_mul, add_mul]
        refine add_le_add (add_le_add hRest hDpoly) ?_
        rw [norm_sub_rev]; exact hSw

/-- **Symmetric (Strang) second-order splitting error of a finite product** (Nielsen & Chuang,
*Quantum Computation and Quantum Information*, Exercise 4.50(a), list form). For a list `l : List 𝔸`
in a Banach algebra there is a constant `C ≥ 0` (depending only on `l`) such that, for every
`t ∈ [0, 1]`,
`‖(∏ g ∈ l, exp(t•g)) · (∏ g ∈ l.reverse, exp(t•g)) - exp((2t) • ∑ g ∈ l, g)‖ ≤ C·t³`,
each product taken in its list's order. That is, the **palindromic** product — the ordered product
of the `exp(t•gᵢ)` immediately followed by the same factors in reverse order — approximates
`exp(2t • ∑ gᵢ)` to third order in `t`, one order better than the unsymmetric splitting
`exists_norm_prod_exp_smul_sub_exp_smul_sum_le` (only `O(t²)`); the palindrome makes the
second-order terms cancel.

This is the operator content of Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 4.50(a): taking `gᵢ = -i·Hᵢ` and `t = Δt` gives, for `H = ∑ᵢ Hᵢ`,
`UΔt := [e^{-iH₁Δt} ⋯ e^{-iH_LΔt}][e^{-iH_LΔt} ⋯ e^{-iH₁Δt}] = e^{-2iHΔt} + O(Δt³)`.

The proof is induction on `l` via the palindrome recursion. The empty product is `exp 0` exactly;
for `a :: l` the product equals `exp(t•a) · P(l) · exp(t•a)`, where `P(l)` is the palindromic
product of `l`. Replacing `P(l)` by `exp(2t•∑l)` costs
`‖exp(t•a)‖² · (C_l·t³) ≤ Real.exp(2‖a‖) · C_l·t³` (the
inductive hypothesis, conjugated by `exp(t•a)`), and the remaining
`exp(t•a) · exp(2t•∑l) · exp(t•a) - exp(2t•(a + ∑l))` is bounded by the two-factor base estimate
`exists_norm_exp_smul_mul_exp_two_smul_mul_exp_smul_sub_le`, itself `O(t³)`. -/
theorem exists_norm_symmProd_exp_smul_sub_exp_two_smul_sum_le (l : List 𝔸) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖(l.map fun g => exp (t • g)).prod * (l.reverse.map fun g => exp (t • g)).prod
        - exp ((2 * t) • l.sum)‖ ≤ C * t ^ 3 := by
  induction l with
  | nil => exact ⟨0, le_refl 0, fun t _ _ => by simp⟩
  | cons a l ih =>
    obtain ⟨C', hC'0, hC'⟩ := ih
    obtain ⟨K, hK0, hK⟩ := exists_norm_exp_smul_mul_exp_two_smul_mul_exp_smul_sub_le a l.sum
    refine ⟨Real.exp (2 * ‖a‖) * C' + K, by positivity, fun t ht0 ht1 => ?_⟩
    have hexpa : ‖exp (t • a)‖ ≤ Real.exp ‖a‖ := by
      refine (norm_exp_le _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      exact mul_le_of_le_one_left (norm_nonneg a) ht1
    -- palindrome recursion: `symmProd (a :: l) = exp(t•a) · symmProd l · exp(t•a)`
    have hpal : ((a :: l).map fun g => exp (t • g)).prod
          * ((a :: l).reverse.map fun g => exp (t • g)).prod
        = exp (t • a) * ((l.map fun g => exp (t • g)).prod
            * (l.reverse.map fun g => exp (t • g)).prod) * exp (t • a) := by
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.prod_append, List.map_nil, List.prod_nil, mul_one]
      noncomm_ring
    have hIH := hC' t ht0 ht1
    have hbase := hK t ht0 ht1
    rw [hpal, List.sum_cons]
    set Q := (l.map fun g => exp (t • g)).prod * (l.reverse.map fun g => exp (t • g)).prod with hQ
    set R := exp ((2 * t) • l.sum) with hR
    -- `hIH : ‖Q - R‖ ≤ C'·t³`; conjugating by `exp(t•a)` costs a factor `Real.exp(2‖a‖)`
    have hfirst : ‖exp (t • a) * (Q - R) * exp (t • a)‖ ≤ Real.exp (2 * ‖a‖) * C' * t ^ 3 := by
      refine norm_mul₃_le.trans ?_
      calc ‖exp (t • a)‖ * ‖Q - R‖ * ‖exp (t • a)‖
          ≤ Real.exp ‖a‖ * (C' * t ^ 3) * Real.exp ‖a‖ := by gcongr
        _ = Real.exp (2 * ‖a‖) * C' * t ^ 3 := by
            rw [show (2 : ℝ) * ‖a‖ = ‖a‖ + ‖a‖ by ring, Real.exp_add]; ring
    -- `hbase : ‖exp(t•a)·R·exp(t•a) - exp(2t•(a+∑l))‖ ≤ K·t³` (the two-factor base estimate)
    calc ‖exp (t • a) * Q * exp (t • a) - exp ((2 * t) • (a + l.sum))‖
        = ‖exp (t • a) * (Q - R) * exp (t • a)
            + (exp (t • a) * R * exp (t • a) - exp ((2 * t) • (a + l.sum)))‖ := by
          congr 1; noncomm_ring
      _ ≤ ‖exp (t • a) * (Q - R) * exp (t • a)‖
            + ‖exp (t • a) * R * exp (t • a) - exp ((2 * t) • (a + l.sum))‖ := norm_add_le _ _
      _ ≤ Real.exp (2 * ‖a‖) * C' * t ^ 3 + K * t ^ 3 := add_le_add hfirst hbase
      _ = (Real.exp (2 * ‖a‖) * C' + K) * t ^ 3 := by ring

end NormedSpace
