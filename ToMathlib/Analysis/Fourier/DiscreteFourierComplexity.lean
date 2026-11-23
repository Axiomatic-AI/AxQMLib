/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Operation counts of the discrete Fourier transform and the fast Fourier transform

This file formalises the operation-count analysis underlying Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Exercise 5.3 (p. 221): computing the discrete Fourier
transform (DFT, N&C (5.1)) of a vector of `N = 2 ^ n` complex numbers by **direct evaluation**
costs `Θ(2 ^ (2 n))` elementary arithmetic operations, whereas the **fast Fourier transform**
(FFT) — the divide-and-conquer algorithm induced by the product form N&C (5.4) — reduces this to
`Θ(n · 2 ^ n)`.

## Modelling choice

Like the gate-count treatment of `AxQM.Concrete.mcNotGateBound` (N&C Exercise 4.29), the
count of *elementary arithmetic operations* used by each algorithm is modelled as an explicit
`ℕ → ℕ` function whose control structure mirrors the algorithm, and the asymptotic claims are
`Asymptotics.IsTheta` statements about these functions (the library's `=Θ[atTop]`). This is the
mathematical content Exercise 5.3 teaches; it is pure combinatorics / real analysis over `ℕ` and
`ℝ`.

* `directDftOpCount n` counts the operations of the **schoolbook** evaluation: the DFT is the
  matrix–vector product `y = F x` with the `N × N` Fourier matrix `F`. Computing all `N` outputs,
  each as a sum of `N` products, uses `N ^ 2 = 2 ^ (2 n)` complex multiplications together with
  `N · (N − 1)` additions, i.e. `4 ^ n + 2 ^ n · (2 ^ n − 1)` operations — `Θ(2 ^ (2 n))`
  (`directDftOpCount_isTheta`).

* `fftOpCount n` is defined by the **divide-and-conquer recurrence** `T 0 = 0`,
  `T (n + 1) = 2 · T n + 2 ^ (n + 1)`. The product form N&C (5.4) splits a size-`2 ^ (n+1)`
  transform into two size-`2 ^ n` transforms (on the even- and odd-indexed inputs) combined by a
  `2 ^ (n + 1)`-operation "butterfly" pass; that is exactly this recurrence. It solves to
  `fftOpCount n = n · 2 ^ n` (`fftOpCount_eq`), hence `Θ(n · 2 ^ n)` (`fftOpCount_isTheta`).

The recurrence solution is isolated as `eq_mul_two_pow_of_divideAndConquer`, valid for *any*
sequence obeying the same recurrence: the closed form is a genuine theorem about the recurrence,
not a value chosen to match the target.

`fftOpCount_le_directDftOpCount` records that the FFT never costs more (an elementary consequence
of `n ≤ 2 ^ n`), and `fftOpCount_isLittleO_directDftOpCount` records the exponential speed-up:
`n · 2 ^ n = o(2 ^ (2 n))`, so the FFT is asymptotically negligible against direct evaluation.

## Scope

The concern of Exercise 5.3 is the *operation count*, which is what is formalised here. Full
verification that an explicit straight-line program of this length actually evaluates the DFT (as
`AxQM.Concrete.exists_mcNotCircuit` does for the multi-controlled-`NOT` gate list) is a
separate, much larger development and is deliberately not attempted; correctness of the DFT itself
is Exercise 5.1 (`ZMod.dftMatrix_mem_unitaryGroup`).
-/

@[expose] public section

open Filter Asymptotics

namespace DiscreteFourier

/-- **Direct-evaluation operation count** of the discrete Fourier transform on `N = 2 ^ n` points.

The DFT is the matrix–vector product with the `N × N` Fourier matrix (N&C (5.1)). Evaluating all
`N` outputs directly, each as a sum of `N` products, uses `N ^ 2 = 4 ^ n` complex multiplications
and `N · (N − 1) = 2 ^ n · (2 ^ n − 1)` additions. -/
def directDftOpCount (n : ℕ) : ℕ := 4 ^ n + 2 ^ n * (2 ^ n - 1)

/-- **Fast Fourier transform operation count** on `N = 2 ^ n` points, as the divide-and-conquer
recurrence induced by the product form N&C (5.4): a size-`2 ^ (n+1)` transform is two
size-`2 ^ n` transforms (on even/odd inputs) plus a `2 ^ (n + 1)`-operation butterfly combine.
The `n = 0` (single point) transform costs nothing. -/
def fftOpCount : ℕ → ℕ
  | 0 => 0
  | (n + 1) => 2 * fftOpCount n + 2 ^ (n + 1)

@[simp] theorem fftOpCount_zero : fftOpCount 0 = 0 := rfl

/-- The FFT recurrence: one recursion level adds two half-size transforms and a `2 ^ (n+1)`
butterfly combine. -/
theorem fftOpCount_succ (n : ℕ) : fftOpCount (n + 1) = 2 * fftOpCount n + 2 ^ (n + 1) := rfl

/-- `2 ^ n · 2 ^ n = 4 ^ n`, i.e. `N ^ 2 = 4 ^ n` for `N = 2 ^ n`. -/
private theorem two_pow_sq (n : ℕ) : 2 ^ n * 2 ^ n = 4 ^ n := by
  rw [← mul_pow]; norm_num

/-- The `N ^ 2 = 4 ^ n` multiplications alone are a lower bound for the direct count. -/
theorem four_pow_le_directDftOpCount (n : ℕ) : 4 ^ n ≤ directDftOpCount n :=
  Nat.le_add_right _ _

/-- The direct count is at most `2 · 4 ^ n` (multiplications plus fewer-than-`N ^ 2` additions). -/
theorem directDftOpCount_le (n : ℕ) : directDftOpCount n ≤ 2 * 4 ^ n := by
  have h : 2 ^ n * (2 ^ n - 1) ≤ 4 ^ n := by
    rw [← two_pow_sq]; exact Nat.mul_le_mul (le_refl _) (Nat.sub_le _ _)
  unfold directDftOpCount; omega

/-- **Direct evaluation is `Θ(2 ^ (2 n))`** — the first claim of N&C Exercise 5.3. The direct DFT
operation count grows at the same rate as `2 ^ (2 n) = 4 ^ n = N ^ 2`, bounded below by `4 ^ n`
(the multiplications) and above by `2 · 4 ^ n`. -/
theorem directDftOpCount_isTheta :
    (fun n => (directDftOpCount n : ℝ)) =Θ[atTop] fun (n : ℕ) => (2 : ℝ) ^ (2 * n) := by
  have key : ∀ n : ℕ, (2 : ℝ) ^ (2 * n) = ((4 ^ n : ℕ) : ℝ) := by
    intro n; push_cast; rw [pow_mul]; norm_num
  refine ⟨isBigO_of_le' atTop (c := 2) (fun n => ?_), isBigO_of_le' atTop (c := 1) (fun n => ?_)⟩
  · rw [Real.norm_natCast, norm_pow, Real.norm_two, key]
    exact_mod_cast directDftOpCount_le n
  · rw [Real.norm_natCast, norm_pow, Real.norm_two, one_mul, key]
    exact_mod_cast four_pow_le_directDftOpCount n

/-- **Solution of the divide-and-conquer recurrence.** Any `T : ℕ → ℕ` with `T 0 = 0` and
`T (n + 1) = 2 · T n + 2 ^ (n + 1)` equals `n · 2 ^ n`. Dividing the recurrence by `2 ^ (n+1)`
shows `T n / 2 ^ n` increases by exactly one at each step; the FFT count `fftOpCount` is the
instance `T = fftOpCount`. -/
theorem eq_mul_two_pow_of_divideAndConquer (T : ℕ → ℕ) (h0 : T 0 = 0)
    (hrec : ∀ n, T (n + 1) = 2 * T n + 2 ^ (n + 1)) (n : ℕ) : T n = n * 2 ^ n := by
  induction n with
  | zero => simpa using h0
  | succ k ih => rw [hrec, ih]; ring

/-- **Closed form of the FFT count:** `fftOpCount n = n · 2 ^ n`. -/
theorem fftOpCount_eq (n : ℕ) : fftOpCount n = n * 2 ^ n :=
  eq_mul_two_pow_of_divideAndConquer fftOpCount rfl (fun _ => rfl) n

/-- **The FFT is `Θ(n · 2 ^ n)`** — the second claim of N&C Exercise 5.3: the product form (5.4)
reduces the transform's cost to `Θ(n · 2 ^ n)`. Immediate from the closed form `fftOpCount_eq`. -/
theorem fftOpCount_isTheta :
    (fun n => (fftOpCount n : ℝ)) =Θ[atTop] fun (n : ℕ) => (n : ℝ) * 2 ^ n := by
  have h : (fun n => (fftOpCount n : ℝ)) = fun (n : ℕ) => (n : ℝ) * 2 ^ n := by
    funext n; rw [fftOpCount_eq]; push_cast; ring
  rw [h]

/-- The FFT never uses more operations than direct evaluation, for every `n` (using `n ≤ 2 ^ n`):
`n · 2 ^ n ≤ 2 ^ n · 2 ^ n = 4 ^ n ≤ directDftOpCount n`. -/
theorem fftOpCount_le_directDftOpCount (n : ℕ) : fftOpCount n ≤ directDftOpCount n := by
  rw [fftOpCount_eq]
  calc n * 2 ^ n ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul Nat.lt_two_pow_self.le (le_refl _)
    _ = 4 ^ n := two_pow_sq n
    _ ≤ directDftOpCount n := four_pow_le_directDftOpCount n

/-- **The FFT is asymptotically negligible compared with direct evaluation**, quantifying the
"reduction" of N&C Exercise 5.3: `fftOpCount = o(directDftOpCount)`, since
`n · 2 ^ n = o(2 ^ (2 n))` (the ratio is `n · (1 / 2) ^ n → 0`). -/
theorem fftOpCount_isLittleO_directDftOpCount :
    (fun n => (fftOpCount n : ℝ)) =o[atTop] fun n => (directDftOpCount n : ℝ) := by
  have hlo : (fun (n : ℕ) => (n : ℝ) * 2 ^ n) =o[atTop] fun (n : ℕ) => (2 : ℝ) ^ (2 * n) := by
    rw [isLittleO_iff_tendsto (fun n hn => absurd hn (by positivity))]
    have hfun : (fun n : ℕ => ((n : ℝ) * 2 ^ n) / 2 ^ (2 * n)) =
        fun (n : ℕ) => (n : ℝ) * (1 / 2) ^ n := by
      funext n
      have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
      rw [two_mul, pow_add, div_pow, one_pow]
      field_simp
    rw [hfun]
    exact tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  exact IsTheta.trans_isLittleO fftOpCount_isTheta
    (IsLittleO.trans_isTheta hlo (IsTheta.symm directDftOpCount_isTheta))

end DiscreteFourier
