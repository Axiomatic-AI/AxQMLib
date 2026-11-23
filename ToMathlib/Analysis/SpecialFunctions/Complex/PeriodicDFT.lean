/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Algebra.Field.GeomSumRootOfUnity
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Ring.Periodic
public import ToMathlib.Algebra.BigOperators.Fin

/-!
# The finite discrete Fourier transform of a periodic function

For a function `f : ℤ → ℂ` that is periodic with period `r` and a length `N` that is an integer
multiple of `r`, this file computes the normalized length-`N` discrete Fourier transform
`f̂(ℓ) = (1/√N) ∑_{x=0}^{N-1} exp(-2πi ℓ x / N) f(x)` and shows it is supported on the multiples
of `N / r`, where its value is `√(N/r)` times the length-`r` transform of the same function.

## Main definitions

* `normDFT` : the normalized finite discrete Fourier transform
  `normDFT n f ℓ = (√n)⁻¹ ∑_{x<n} exp(-2πi ℓ x / n) f x` (with `normDFT_apply` its definitional
  unfolding / API surface).

## Main statements

* `sum_range_exp_two_pi_mul_I_div` : the root-of-unity orthogonality sum
  `∑_{j<m} exp(2πi ℓ j / m) = m` when `m ∣ ℓ` and `0` otherwise.
* `normDFT_periodic_eq_zero` : if `ℓ` is **not** a multiple of `N / r`, then `normDFT N f ℓ = 0`.
* `normDFT_periodic_mul` : `normDFT N f (k · (N/r)) = √(N/r) · normDFT r f k`.

## Nielsen & Chuang, Exercise 5.20

This is the mathematical content of Exercise 5.20 of Nielsen & Chuang, *Quantum Computation and
Quantum Information* (p. 238). `normDFT N f` is their transform `f̂` of equation (5.68), and
`normDFT r f` reproduces the coefficients of the period-finding state `|f̂(ℓ)⟩` of equation (5.63);
`normDFT_periodic_mul` is the requested relation between the two. The orthogonality identity
`sum_range_exp_two_pi_mul_I_div` is the "fact" (5.69) the exercise instructs one to use — note that
the printed right-hand side of (5.69), `√(N/r)`, is a misprint: the geometric sum of the `N/r`-th
roots of unity is `N/r`, not `√(N/r)` (the `√` normalization appears only once, in the `1/√N`
prefactor of (5.68), which is why the *final* relation carries the factor `√(N/r)`).
-/

open Finset Complex
open scoped Real

@[expose] public section

variable {f : ℤ → ℂ}

/-- **Root-of-unity orthogonality (Nielsen & Chuang eq. (5.69), evaluated).**
The geometric sum of the `m`-th roots of unity `∑_{j<m} exp(2πi ℓ j / m)` equals `m` when `m ∣ ℓ`
and `0` otherwise. (N&C print the right-hand side as `√(N/r)`; the correct value of the sum itself
is `N/r`, here `m`.) -/
theorem sum_range_exp_two_pi_mul_I_div (m : ℕ) (hm : 0 < m) (ℓ : ℤ) :
    ∑ j ∈ range m, exp (2 * (π : ℂ) * I * (ℓ : ℂ) * (j : ℂ) / (m : ℂ))
      = if (m : ℤ) ∣ ℓ then (m : ℂ) else 0 := by
  have hkey : ∀ j : ℕ, exp (2 * (π : ℂ) * I * (ℓ : ℂ) * (j : ℂ) / (m : ℂ))
      = exp (2 * (π : ℂ) * I * (ℓ : ℂ) / (m : ℂ)) ^ j := by
    intro j
    rw [← Complex.exp_natCast_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun j _ => hkey j)]
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hpow : exp (2 * (π : ℂ) * I * (ℓ : ℂ) / (m : ℂ)) ^ m = 1 := by
    rw [← Complex.exp_natCast_mul,
      show (m : ℂ) * (2 * (π : ℂ) * I * (ℓ : ℂ) / (m : ℂ)) = (ℓ : ℂ) * (2 * (π : ℂ) * I) from by
        field_simp]
    exact_mod_cast Complex.exp_int_mul_two_pi_mul_I ℓ
  rw [geom_sum_eq_ite_of_pow_eq_one hpow]
  have hc : (2 : ℂ) * (π : ℂ) * I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hcond : exp (2 * (π : ℂ) * I * (ℓ : ℂ) / (m : ℂ)) = 1 ↔ (m : ℤ) ∣ ℓ := by
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h2 : (2 * (π : ℂ) * I) * (ℓ : ℂ) = (2 * (π : ℂ) * I) * ((m : ℂ) * (k : ℂ)) := by
        rw [div_eq_iff hm0] at hk
        linear_combination hk
      have h3 : (ℓ : ℂ) = (m : ℂ) * (k : ℂ) := mul_left_cancel₀ hc h2
      exact_mod_cast h3
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hk]
      push_cast
      field_simp
  simp only [hcond]

/-- The normalized finite discrete Fourier transform of `f : ℤ → ℂ` at length `n`, following
Nielsen & Chuang eq. (5.68)/(5.63): `normDFT n f ℓ = (1/√n) ∑_{x<n} exp(-2πi ℓ x / n) f x`. -/
noncomputable def normDFT (n : ℕ) (f : ℤ → ℂ) (ℓ : ℤ) : ℂ :=
  (Real.sqrt (n : ℝ) : ℂ)⁻¹ *
    ∑ x ∈ range n, exp (-(2 * (π : ℂ) * I * (ℓ : ℂ) * (x : ℂ)) / (n : ℂ)) * f (x : ℤ)

/-- Definitional unfolding of `normDFT` (its API surface): `normDFT n f ℓ` is the `1/√n`-normalized
sum `∑_{x<n} exp(-2πi ℓ x / n) f x`. -/
theorem normDFT_apply (n : ℕ) (f : ℤ → ℂ) (ℓ : ℤ) :
    normDFT n f ℓ = (Real.sqrt (n : ℝ) : ℂ)⁻¹ *
      ∑ x ∈ range n, exp (-(2 * (π : ℂ) * I * (ℓ : ℂ) * (x : ℂ)) / (n : ℂ)) * f (x : ℤ) :=
  rfl

/-- Splitting the length-`N` Fourier sum of a period-`r` function `f` (with `r ∣ N`) into a product
of a length-`r` sum and a geometric sum over the `N / r` complete periods. -/
private theorem normDFT_sum_factor (r N : ℕ) (hd : r ∣ N)
    (hf : Function.Periodic f (r : ℤ)) (ℓ : ℤ) :
    ∑ x ∈ range N, exp (-(2 * (π : ℂ) * I * (ℓ : ℂ) * (x : ℂ)) / (N : ℂ)) * f (x : ℤ)
      = (∑ j ∈ range r, exp (-(2 * (π : ℂ) * I * (ℓ : ℂ) * (j : ℂ)) / (N : ℂ)) * f (j : ℤ))
        * ∑ i ∈ range (N / r),
            exp (-(2 * (π : ℂ) * I * (ℓ : ℂ) * ((r : ℂ) * (i : ℂ))) / (N : ℂ)) := by
  have hper : ∀ (i j : ℕ), f ((j + r * i : ℕ) : ℤ) = f (j : ℤ) := by
    intro i j
    have h := (hf.nsmul i) (j : ℤ)
    rw [nsmul_eq_mul] at h
    push_cast
    rw [mul_comm (r : ℤ) (i : ℤ)]
    exact h
  have hidx : range N = range (N / r * r) := by rw [Nat.div_mul_cancel hd]
  rw [hidx, sum_range_mul_reindex, Finset.sum_comm, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [hper i j,
    show exp (-(2 * (π : ℂ) * I * (ℓ : ℂ) * ((j + r * i : ℕ) : ℂ)) / (N : ℂ))
      = exp (-(2 * (π : ℂ) * I * (ℓ : ℂ) * (j : ℂ)) / (N : ℂ))
        * exp (-(2 * (π : ℂ) * I * (ℓ : ℂ) * ((r : ℂ) * (i : ℂ))) / (N : ℂ)) from by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
  ring

/-- **Nielsen & Chuang, Exercise 5.20 (off-support).** For a period-`r` function `f` sampled over a
length `N` that is a multiple of `r`, the length-`N` Fourier coefficient vanishes at every frequency
`ℓ` that is not a multiple of `N / r`. -/
theorem normDFT_periodic_eq_zero (r N : ℕ) (hr : 0 < r) (hd : r ∣ N) (hN : 0 < N)
    (hf : Function.Periodic f (r : ℤ)) {ℓ : ℤ} (hℓ : ¬ (↑(N / r) : ℤ) ∣ ℓ) :
    normDFT N f ℓ = 0 := by
  have hm : 0 < N / r := Nat.div_pos (Nat.le_of_dvd hN hd) hr
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hm0 : ((N / r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hNval : (N : ℂ) = (r : ℂ) * ((N / r : ℕ) : ℂ) := by
    rw [← Nat.cast_mul]; exact_mod_cast (Nat.mul_div_cancel' hd).symm
  have hEq : ∀ i ∈ range (N / r),
      exp (-(2 * (π : ℂ) * I * (ℓ : ℂ) * ((r : ℂ) * (i : ℂ))) / (N : ℂ))
        = exp (2 * (π : ℂ) * I * ((-ℓ : ℤ) : ℂ) * (i : ℂ) / ((N / r : ℕ) : ℂ)) := by
    intro i _
    congr 1
    rw [hNval, div_eq_div_iff (mul_ne_zero hr0 hm0) hm0]
    push_cast
    ring
  have hB : ∑ i ∈ range (N / r),
      exp (-(2 * (π : ℂ) * I * (ℓ : ℂ) * ((r : ℂ) * (i : ℂ))) / (N : ℂ)) = 0 := by
    rw [Finset.sum_congr rfl hEq, sum_range_exp_two_pi_mul_I_div (N / r) hm (-ℓ),
      ite_eq_right (by rw [Int.dvd_neg]; exact hℓ)]
  rw [normDFT_apply, normDFT_sum_factor r N hd hf ℓ, hB, mul_zero, mul_zero]

/-- **Nielsen & Chuang, Exercise 5.20 (on-support).** For a period-`r` function `f` sampled over a
length `N` that is a multiple of `r`, the length-`N` Fourier coefficient at a frequency `k · (N/r)`
equals `√(N/r)` times the length-`r` Fourier coefficient of `f` at `k` — i.e. the transform
`normDFT r f` of equation (5.63), up to the `√(N/r)` normalization. -/
theorem normDFT_periodic_mul (r N : ℕ) (hr : 0 < r) (hd : r ∣ N) (hN : 0 < N)
    (hf : Function.Periodic f (r : ℤ)) (k : ℤ) :
    normDFT N f (k * (↑(N / r) : ℤ)) = (Real.sqrt ((N / r : ℕ) : ℝ) : ℂ) * normDFT r f k := by
  have hm : 0 < N / r := Nat.div_pos (Nat.le_of_dvd hN hd) hr
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hm0 : ((N / r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hNval : (N : ℂ) = (r : ℂ) * ((N / r : ℕ) : ℂ) := by
    rw [← Nat.cast_mul]; exact_mod_cast (Nat.mul_div_cancel' hd).symm
  have hsrC : (Real.sqrt (r : ℝ) : ℂ) ≠ 0 := by
    have : Real.sqrt (r : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hr)
    exact_mod_cast this
  set L : ℤ := k * (↑(N / r) : ℤ) with hL
  -- the geometric factor over complete periods is `N / r`
  have hB : ∑ i ∈ range (N / r),
      exp (-(2 * (π : ℂ) * I * (L : ℂ) * ((r : ℂ) * (i : ℂ))) / (N : ℂ)) = ((N / r : ℕ) : ℂ) := by
    have hEq : ∀ i ∈ range (N / r),
        exp (-(2 * (π : ℂ) * I * (L : ℂ) * ((r : ℂ) * (i : ℂ))) / (N : ℂ)) = 1 := by
      intro i _
      rw [show -(2 * (π : ℂ) * I * (L : ℂ) * ((r : ℂ) * (i : ℂ))) / (N : ℂ)
            = ((-(k * (i : ℤ)) : ℤ) : ℂ) * (2 * (π : ℂ) * I) from by
        rw [hL, hNval, div_eq_iff (mul_ne_zero hr0 hm0)]
        simp only [Int.cast_mul, Int.cast_natCast, Int.cast_neg]; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [Finset.sum_congr rfl hEq, Finset.sum_const, card_range, nsmul_eq_mul, mul_one]
  -- the length-`r` factor is `√r · normDFT r f k`
  have hA : ∑ j ∈ range r,
      exp (-(2 * (π : ℂ) * I * (L : ℂ) * (j : ℂ)) / (N : ℂ)) * f (j : ℤ)
        = (Real.sqrt (r : ℝ) : ℂ) * normDFT r f k := by
    have hEq : ∀ j ∈ range r,
        exp (-(2 * (π : ℂ) * I * (L : ℂ) * (j : ℂ)) / (N : ℂ)) * f (j : ℤ)
          = exp (-(2 * (π : ℂ) * I * (k : ℂ) * (j : ℂ)) / (r : ℂ)) * f (j : ℤ) := by
      intro j _
      rw [show -(2 * (π : ℂ) * I * (L : ℂ) * (j : ℂ)) / (N : ℂ)
            = -(2 * (π : ℂ) * I * (k : ℂ) * (j : ℂ)) / (r : ℂ) from by
        rw [hL, hNval, div_eq_div_iff (mul_ne_zero hr0 hm0) hr0]
        simp only [Int.cast_mul, Int.cast_natCast]; ring]
    rw [Finset.sum_congr rfl hEq, normDFT_apply, ← mul_assoc, mul_inv_cancel₀ hsrC, one_mul]
  rw [normDFT_apply, normDFT_sum_factor r N hd hf L, hA, hB,
    show (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
        (((Real.sqrt (r : ℝ) : ℂ) * normDFT r f k) * ((N / r : ℕ) : ℂ))
      = ((Real.sqrt (N : ℝ) : ℂ)⁻¹ * (Real.sqrt (r : ℝ) : ℂ) * ((N / r : ℕ) : ℂ))
        * normDFT r f k from by ring]
  congr 1
  have hreal : (Real.sqrt (N : ℝ))⁻¹ * Real.sqrt (r : ℝ) * ((N / r : ℕ) : ℝ)
      = Real.sqrt ((N / r : ℕ) : ℝ) := by
    have hNr : (N : ℝ) = ((N / r : ℕ) : ℝ) * (r : ℝ) := by
      rw [← Nat.cast_mul]; exact_mod_cast (Nat.div_mul_cancel hd).symm
    have hsr : Real.sqrt (r : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hr)
    have hsm : Real.sqrt ((N / r : ℕ) : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hm)
    have esm : Real.sqrt ((N / r : ℕ) : ℝ) * Real.sqrt ((N / r : ℕ) : ℝ) = ((N / r : ℕ) : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg _)
    rw [hNr, Real.sqrt_mul (Nat.cast_nonneg _)]
    field_simp
    linear_combination -esm
  calc (Real.sqrt (N : ℝ) : ℂ)⁻¹ * (Real.sqrt (r : ℝ) : ℂ) * ((N / r : ℕ) : ℂ)
      = ((Real.sqrt (N : ℝ))⁻¹ * Real.sqrt (r : ℝ) * ((N / r : ℕ) : ℝ) : ℝ) := by push_cast; ring
    _ = (Real.sqrt ((N / r : ℕ) : ℝ) : ℂ) := by rw [hreal]
