/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Concrete: amplitude damping of a harmonic oscillator (N&C, Exercise 8.21)

This file develops the operation elements of the **amplitude-damping quantum operation of a
harmonic oscillator** (Nielsen & Chuang, Exercise 8.21, p. 381) and proves that they define a
*trace-preserving* quantum operation. Everything is stated for natural numbers, real amplitudes and
`Matrix ℕ ℕ ℂ`. The statement of Exercise 8.21 is in `AxQM/NC/Ch8/Exercise8_21.lean`.

## The exercise

A principal harmonic oscillator interacts with an environment oscillator through the Hamiltonian
`H = χ(a†b + b†a)` (eq. 8.109), where `a`, `b` are the annihilation operators of the two
oscillators. Writing `U = exp(-i H Δt)`, taking the environment vacuum `|0_b⟩` as its initial state,
and letting `|n⟩` denote the number (`a†a`-eigen) states of the principal oscillator, the operation
elements `Eₖ = ⟨k_b| U |0_b⟩` are (eq. 8.110)

`Eₖ = Σₙ √( C(n,k) (1-γ)^{n-k} γ^k ) |n-k⟩⟨n|`,   `γ = 1 - cos²(χΔt) = sin²(χΔt)`,

with `γ` the probability of losing a single quantum of energy. The exercise asks:

1. derive the operation elements `Eₖ` (eq. 8.110) from `U`, and
2. show the `Eₖ` define a *trace-preserving* quantum operation, i.e. `Σₖ Eₖ† Eₖ = I`.

## What is formalised, and what the library cannot express

The oscillator's state space is the infinite-dimensional Fock space `ℓ²(ℕ)` (number states `|n⟩`,
`n : ℕ`). This is **not** an `AxQM.QSystem`, which has a *finite*-dimensional Hilbert space
(`QSystem.findim`), so the harmonic oscillator is not covered by the library's notion of a quantum
system, and there is at present no bosonic Fock-space / creation-annihilation / beam-splitter
infrastructure in `ToMathlib/` to build `U = exp(-i H Δt)` from `H = χ(a†b + b†a)` and read
off `Eₖ = ⟨k_b|U|0_b⟩`. Part **(1)**'s *derivation* of eq. 8.110 from the Hamiltonian is therefore
beyond the current library; we take eq. 8.110 as the **definition** of the operation elements —
which is exactly the hypothesis of part (2) ("show the `Eₖ` [given by 8.110] define a
trace-preserving operation") — and additionally certify the physical parameter
`γ = 1 - cos²(χΔt) = sin²(χΔt) ∈ [0,1]` (`fockDampingProb`). Part **(2)** — the substantive
verifiable claim — is proved in full.

Because there is no matrix multiplication on `Matrix ℕ ℕ ℂ` (`ℕ` is not a `Fintype`), the
completeness relation `Σₖ Eₖ† Eₖ = I` is stated *entrywise*: the `(a,b)` entry of the product
`Eₖ† Eₖ` is the (finitely supported) sum `∑ᶠ j, (Eₖ)ᴴ a j · (Eₖ) j b` — the standard formula
`(MN)_{ab} = Σⱼ M_{aj} N_{jb}` — and completeness reads `∑ᶠ k, ∑ᶠ j, (Eₖ)ᴴ a j · (Eₖ) j b = I_{ab}`
for all `a b : ℕ`. Each `Eₖ† Eₖ` is diagonal (`fockDampingGram`), so the relation collapses, level
by level, to the binomial identity `Σₖ C(n,k) (1-γ)^{n-k} γ^k = ((1-γ) + γ)^n = 1` — the
mathematical heart of the exercise.

## Contents

* `fockDampingProb` (`γ = 1 - cos²(χΔt)`) with `fockDampingProb_eq_sin_sq`,
  `fockDampingProb_nonneg`, `fockDampingProb_le_one` — the physical parameter and its `[0,1]`
  bounds.
* `fockDampingProbCoef` (`C(n,k) (1-γ)^{n-k} γ^k`, the probability of losing `k` quanta from level
  `n`), with `fockDampingProbCoef_nonneg` and `fockDampingProbCoef_sum` (`Σ_{k≤n} = 1`, the binomial
  theorem).
* `fockDampingAmp` (`√(fockDampingProbCoef)`, the amplitude in eq. 8.110) with `fockDampingAmp_sq`.
* `fockDampingKraus` — the operation element `Eₖ` of eq. 8.110, as a `Matrix ℕ ℕ ℂ`; with
  `fockDampingKraus_apply` and `fockDampingKraus_lower` (`Eₖ |n⟩ = √(…) |n-k⟩` for `k ≤ n`).
* `fockDampingGram` — the diagonal operator `Eₖ† Eₖ`, with `fockDampingGram_eq` certifying it equals
  the entrywise product `∑ᶠ j (Eₖ)ᴴ a j (Eₖ) j b`.
* `fockDampingKraus_completeness` — **Exercise 8.21(2):** the trace-preservation / completeness
  relation `Σₖ Eₖ† Eₖ = I`, stated entrywise.
-/

namespace AxQM.Concrete

open Matrix
open scoped BigOperators

/-! ### The damping probability `γ = 1 - cos²(χΔt)` (eq. 8.110) -/

/-- The **single-quantum loss probability** `γ = 1 - cos²(χΔt)` of Exercise 8.21 (eq. 8.110), where
`χ` is the interaction strength of `H = χ(a†b + b†a)` and `Δt` the interaction time. -/
noncomputable def fockDampingProb (χ Δt : ℝ) : ℝ := 1 - Real.cos (χ * Δt) ^ 2

/-- `γ = 1 - cos²(χΔt) = sin²(χΔt)`: the loss probability equals `sin²(χΔt)` (N&C give both
forms). -/
theorem fockDampingProb_eq_sin_sq (χ Δt : ℝ) :
    fockDampingProb χ Δt = Real.sin (χ * Δt) ^ 2 := by
  have h := Real.sin_sq_add_cos_sq (χ * Δt)
  rw [fockDampingProb]; linarith

/-- The loss probability is nonnegative: `0 ≤ γ` (it equals `sin²(χΔt) ≥ 0`). -/
theorem fockDampingProb_nonneg (χ Δt : ℝ) : 0 ≤ fockDampingProb χ Δt := by
  rw [fockDampingProb_eq_sin_sq]; positivity

/-- The loss probability is at most one: `γ ≤ 1` (since `cos²(χΔt) ≥ 0`). -/
theorem fockDampingProb_le_one (χ Δt : ℝ) : fockDampingProb χ Δt ≤ 1 := by
  have h : (0 : ℝ) ≤ Real.cos (χ * Δt) ^ 2 := sq_nonneg _
  rw [fockDampingProb]; linarith

/-! ### The operation-element coefficients (eq. 8.110) -/

/-- The **probability of losing `k` quanta from the `n`-quantum level**, `C(n,k) (1-γ)^{n-k} γ^k`:
the squared amplitude of the operation element `Eₖ` on the number state `|n⟩` (a binomial weight —
each of the `n` quanta is lost with probability `γ`, independently). -/
noncomputable def fockDampingProbCoef (γ : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (1 - γ) ^ (n - k) * γ ^ k

/-- For a genuine probability `γ ∈ [0,1]` the coefficient `C(n,k) (1-γ)^{n-k} γ^k` is
nonnegative. -/
theorem fockDampingProbCoef_nonneg {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (n k : ℕ) :
    0 ≤ fockDampingProbCoef γ n k := by
  rw [fockDampingProbCoef]
  refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ?_ _)) (pow_nonneg hγ0 _)
  linarith

/-- **The binomial completeness of the loss probabilities** (the heart of part (2)): summing over
the number `k` of quanta lost from a fixed level `n`,
`Σ_{k=0}^n C(n,k) (1-γ)^{n-k} γ^k = ((1-γ)+γ)^n = 1`. This is the binomial theorem, and it is
exactly what makes the operation trace preserving. -/
theorem fockDampingProbCoef_sum (γ : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), fockDampingProbCoef γ n k = 1 := by
  have h := add_pow γ (1 - γ) n
  rw [show γ + (1 - γ) = 1 by ring, one_pow] at h
  refine (Finset.sum_congr rfl fun k _ => ?_).trans h.symm
  rw [fockDampingProbCoef]
  generalize (1 - γ) ^ (n - k) = A
  generalize γ ^ k = B
  ring

/-- For `k > n` the coefficient vanishes: no state has fewer than `0` quanta, so `Eₖ` annihilates
`|n⟩` when `k > n` (formally `C(n,k) = 0`). -/
theorem fockDampingProbCoef_eq_zero {n k : ℕ} (h : n < k) (γ : ℝ) :
    fockDampingProbCoef γ n k = 0 := by
  rw [fockDampingProbCoef, Nat.choose_eq_zero_of_lt h]; push_cast; ring

/-- The **amplitude** `√( C(n,k) (1-γ)^{n-k} γ^k )` of the operation element `Eₖ` on `|n⟩`
(eq. 8.110). -/
noncomputable def fockDampingAmp (γ : ℝ) (n k : ℕ) : ℝ :=
  Real.sqrt (fockDampingProbCoef γ n k)

/-- The squared amplitude is the loss probability:
`(fockDampingAmp γ n k)² = C(n,k) (1-γ)^{n-k} γ^k`, for `γ ∈ [0,1]` (so the radicand is
nonnegative). -/
theorem fockDampingAmp_sq {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (n k : ℕ) :
    fockDampingAmp γ n k ^ 2 = fockDampingProbCoef γ n k :=
  Real.sq_sqrt (fockDampingProbCoef_nonneg hγ0 hγ1 n k)

/-! ### The operation elements `Eₖ` (eq. 8.110) -/

/-- The **operation element** `Eₖ` of amplitude damping (eq. 8.110), as an infinite matrix over the
number-state index `ℕ`:
`Eₖ = Σₙ √( C(n,k) (1-γ)^{n-k} γ^k ) |n-k⟩⟨n|`.
The `(r,c)` entry is the amplitude `√(…)` when `r = c - k` (row `n-k`, column `n`, i.e. `r + k = c`)
and `0` otherwise — so `Eₖ` lowers the quantum number by `k`. -/
noncomputable def fockDampingKraus (γ : ℝ) (k : ℕ) : Matrix ℕ ℕ ℂ :=
  fun r c => if r + k = c then (fockDampingAmp γ c k : ℂ) else 0

/-- The defining entrywise formula for `Eₖ` (eq. 8.110). -/
theorem fockDampingKraus_apply (γ : ℝ) (k r c : ℕ) :
    fockDampingKraus γ k r c = if r + k = c then (fockDampingAmp γ c k : ℂ) else 0 := rfl

/-- `Eₖ` **lowers `|n⟩` to `|n-k⟩` with amplitude `√(…)`** (for `k ≤ n`): the matrix element
`⟨n-k| Eₖ |n⟩ = fockDampingAmp γ n k`, the coefficient of `|n-k⟩⟨n|` in eq. 8.110. -/
theorem fockDampingKraus_lower (γ : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    fockDampingKraus γ k (n - k) n = (fockDampingAmp γ n k : ℂ) := by
  rw [fockDampingKraus_apply, ite_eq_left (by omega)]

/-! ### Trace preservation (`Σₖ Eₖ† Eₖ = I`, part (2)) -/

/-- The diagonal operator `Eₖ† Eₖ = Σₙ C(n,k) (1-γ)^{n-k} γ^k |n⟩⟨n|`: the `k`-th summand of the
completeness relation. It is certified to be the genuine product `Eₖ† Eₖ` by
`fockDampingGram_eq`. -/
noncomputable def fockDampingGram (γ : ℝ) (k : ℕ) : Matrix ℕ ℕ ℂ :=
  Matrix.diagonal fun n => (fockDampingProbCoef γ n k : ℂ)

/-- **`fockDampingGram γ k` is the product `Eₖ† Eₖ`, entrywise.** The `(a,b)` entry of `Eₖ† Eₖ` is
the (finitely supported) sum `∑ᶠ j, (Eₖ)ᴴ a j · (Eₖ) j b` (the matrix-product formula
`(MN)_{ab} = Σⱼ M_{aj} N_{jb}`, valid over the infinite index `ℕ` because the family has finite
support). Since `Eₖ` has a single nonzero entry per column (`|n-k⟩⟨n|`), the product is diagonal
with entries the loss probabilities `C(n,k)(1-γ)^{n-k}γ^k`. -/
theorem fockDampingGram_eq {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (k a b : ℕ) :
    (∑ᶠ j, (fockDampingKraus γ k)ᴴ a j * fockDampingKraus γ k j b) = fockDampingGram γ k a b := by
  -- off the single surviving column `j = a - k`, every term of the product vanishes
  have hzero : ∀ j, j ≠ a - k →
      (fockDampingKraus γ k)ᴴ a j * fockDampingKraus γ k j b = 0 := by
    intro j hj
    simp only [Matrix.conjTranspose_apply, fockDampingKraus_apply]
    rw [ite_eq_right (show ¬ j + k = a by omega), star_zero, zero_mul]
  rw [finsum_eq_single _ (a - k) hzero]
  simp only [fockDampingGram, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    fockDampingKraus_apply]
  rcases eq_or_ne a b with hab | hab
  · subst hab
    by_cases hka : k ≤ a
    · rw [ite_eq_left (show a - k + k = a by omega), ite_eq_left rfl]
      have hstar : star (fockDampingAmp γ a k : ℂ) = (fockDampingAmp γ a k : ℂ) :=
        Complex.conj_ofReal _
      rw [hstar, ← Complex.ofReal_mul, ← pow_two, fockDampingAmp_sq hγ0 hγ1]
    · rw [ite_eq_right (show ¬ a - k + k = a by omega), ite_eq_left rfl,
        fockDampingProbCoef_eq_zero (show a < k by omega), Complex.ofReal_zero,
        star_zero, zero_mul]
  · rw [ite_eq_right hab]
    by_cases hka : k ≤ a
    · rw [ite_eq_left (show a - k + k = a by omega), ite_eq_right (show ¬ a - k + k = b by omega),
          mul_zero]
    · rw [ite_eq_right (show ¬ a - k + k = a by omega), star_zero, zero_mul]

/-- **Exercise 8.21(2): the operation elements define a trace-preserving quantum operation.** The
completeness relation `Σₖ Eₖ† Eₖ = I`, stated entrywise over the number-state index `ℕ`: for all
`a b : ℕ`,
`∑ᶠ k, ∑ᶠ j, (Eₖ)ᴴ a j · (Eₖ) j b = I_{ab}`,
where the inner `∑ᶠ j` is the `(a,b)` entry of `Eₖ† Eₖ`. Each `Eₖ† Eₖ` is diagonal
(`fockDampingGram_eq`), and on the diagonal the sum over `k` is the binomial identity
`Σₖ C(n,k)(1-γ)^{n-k}γ^k = 1` (`fockDampingProbCoef_sum`); off the diagonal every term vanishes. -/
theorem fockDampingKraus_completeness {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (a b : ℕ) :
    (∑ᶠ k, ∑ᶠ j, (fockDampingKraus γ k)ᴴ a j * fockDampingKraus γ k j b)
      = (1 : Matrix ℕ ℕ ℂ) a b := by
  have hgram : (∑ᶠ k, ∑ᶠ j, (fockDampingKraus γ k)ᴴ a j * fockDampingKraus γ k j b)
      = ∑ᶠ k, fockDampingGram γ k a b :=
    finsum_congr fun k => fockDampingGram_eq hγ0 hγ1 k a b
  rw [hgram, Matrix.one_apply]
  rcases eq_or_ne a b with hab | hab
  · subst hab
    rw [ite_eq_left rfl]
    simp only [fockDampingGram, Matrix.diagonal_apply_eq]
    rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (a + 1)), ← Complex.ofReal_sum,
      fockDampingProbCoef_sum, Complex.ofReal_one]
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hle
    exact hk (by rw [fockDampingProbCoef_eq_zero (by omega), Complex.ofReal_zero])
  · rw [ite_eq_right hab]
    simp only [fockDampingGram, Matrix.diagonal_apply_ne _ hab, finsum_zero]

end AxQM.Concrete
