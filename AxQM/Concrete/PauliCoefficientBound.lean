/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliString
import Mathlib.Algebra.Order.Chebyshev

/-!
# Concrete: the `ℓ¹` bound on the Pauli coefficients of a Hermitian matrix

This file bounds the **sum of absolute values** of the real Pauli coefficients of a Hermitian
`2ⁿ × 2ⁿ` matrix by its Hilbert–Schmidt (Frobenius) norm. It is stated for matrices (`Matrix`,
`Concrete.pauliString`, `trace`).

## What this delivers

For a Hermitian matrix `M` with real Pauli expansion `M = ∑_g (h_g : ℂ) • P_g` (Nielsen & Chuang,
Problem 4.3(2); `Concrete.exists_real_pauliString_expansion`):

* `Concrete.trace_conjTranspose_mul_self_re_eq_sum_pauliCoeff_sq` — the **Parseval identity**
  `(Mᴴ * M).trace.re = 2ⁿ · ∑_g h_g²`. The Pauli strings are Hilbert–Schmidt orthogonal
  (`pauliString_trace_mul`: `tr(P_g P_{g'}) = 2ⁿ δ_{g g'}`), so expanding one factor of `M` in
  `tr(Mᴴ M) = tr(M²)` (`M` Hermitian) collapses the double sum to `2ⁿ ∑_g h_g²`.
* `Concrete.sq_sum_abs_pauliCoeff_le` — the **`ℓ¹` bound** `(∑_g |h_g|)² ≤ 2ⁿ · (Mᴴ * M).trace.re`.
  Cauchy–Schwarz over the `4ⁿ` coefficients (`sq_sum_le_card_mul_sum_sq`) gives
  `(∑_g |h_g|)² ≤ 4ⁿ ∑_g h_g²`; substituting Parseval (`∑ h_g² = (2ⁿ)⁻¹ tr(Mᴴ M)`) turns the `4ⁿ`
  into `4ⁿ · (2ⁿ)⁻¹ = 2ⁿ` times the trace.

## Why this matters (Problem 4.3(6))

N&C's alternate-universality gate count is `O(n · 16ⁿ / ε)`. The `16ⁿ = 4ⁿ · 4ⁿ` factors as the
`4ⁿ` gates per Trotter step times `O(4ⁿ)` Trotter repetitions `k`. The `O(4ⁿ)` on `k` needs the
first-order Trotter constant `C = O(Λ²)` with `Λ = ∑_g |h_g|` (the total Pauli weight of
`H = i ln U`), and `Λ = O(2ⁿ)`: with `‖H‖ ≤ 2π` (part 1b spectrum bound) the Frobenius norm obeys
`tr(Mᴴ M) = ∑ eigenvalues² ≤ 2ⁿ · ‖H‖²`, whence `(∑ |h_g|)² ≤ 2ⁿ · 2ⁿ ‖H‖² = 4ⁿ ‖H‖²`, i.e.
`∑ |h_g| ≤ 2ⁿ ‖H‖`, so `Λ² = O(4ⁿ)`. This file is the matrix core of that estimate — the pure
Parseval + Cauchy–Schwarz half. The operator-norm step `tr(Mᴴ M) ≤ 2ⁿ ‖H.op‖²` (which concerns
the operator `H.op` of an evolution) and the assembly into `Λ = O(2ⁿ)` are in
`AxQM/Postulates/API/`.
-/

open scoped Matrix

noncomputable section

namespace AxQM.Concrete

variable {n : ℕ}

/-- **Parseval identity for the real Pauli coefficients.** For a Hermitian matrix `M` with real
Pauli expansion `M = ∑_g (h_g : ℂ) • P_g`, the Hilbert–Schmidt inner product of `M` with itself is
`2ⁿ` times the sum of the squared coefficients: `(Mᴴ * M).trace.re = 2ⁿ · ∑_g h_g²`.

Since `M` is Hermitian, `Mᴴ * M = M * M`. Expanding one factor of `M` and using the Hilbert–Schmidt
orthogonality `tr(P_g P_{g'}) = 2ⁿ δ_{g g'}` (`pauliString_trace_mul`) collapses the pairing
`tr(P_g M) = h_g · 2ⁿ`, and a second expansion gives `tr(M²) = ∑_g h_g · (h_g · 2ⁿ) = 2ⁿ ∑_g h_g²`.
This is the `n`-fold Parseval theorem for the Pauli basis `{2^{-n/2} P_g}`. -/
theorem trace_conjTranspose_mul_self_re_eq_sum_pauliCoeff_sq
    {M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ} (hM : M.IsHermitian)
    {h : (Fin n → Fin 4) → ℝ} (hexp : M = ∑ g, (h g : ℂ) • pauliString g) :
    (Mᴴ * M).trace.re = 2 ^ n * ∑ g, h g ^ 2 := by
  -- The Pauli trace pairing extracts a single coefficient: `tr(P_g M) = h_g · 2ⁿ`
  -- (Hilbert–Schmidt orthogonality, `pauliString_trace_mul_sum_smul`).
  have htr : ∀ g : Fin n → Fin 4, (pauliString g * M).trace = (h g : ℂ) * 2 ^ n := by
    intro g
    rw [hexp]
    exact pauliString_trace_mul_sum_smul (fun g' => (h g' : ℂ)) g
  -- Now expand the outer `M` in `tr(Mᴴ M) = tr(M²)`.
  have hHM : (Mᴴ * M).trace = ((2 ^ n * ∑ g, h g ^ 2 : ℝ) : ℂ) := by
    rw [hM.eq]
    calc (M * M).trace
        = ((∑ g, (h g : ℂ) • pauliString g) * M).trace := by rw [← hexp]
      _ = ∑ g, (h g : ℂ) * (pauliString g * M).trace := by
            rw [Matrix.sum_mul, Matrix.trace_sum]
            exact Finset.sum_congr rfl fun g _ => by
              rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      _ = ∑ g, (h g : ℂ) * ((h g : ℂ) * 2 ^ n) := by
            exact Finset.sum_congr rfl fun g _ => by rw [htr]
      _ = ((2 ^ n * ∑ g, h g ^ 2 : ℝ) : ℂ) := by
            push_cast
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun g _ => by ring
  rw [hHM, Complex.ofReal_re]

/-- **`ℓ¹` bound on the real Pauli coefficients.** For a Hermitian matrix `M` with real Pauli
expansion `M = ∑_g (h_g : ℂ) • P_g`, the sum of absolute values of the coefficients is controlled by
the Hilbert–Schmidt norm: `(∑_g |h_g|)² ≤ 2ⁿ · (Mᴴ * M).trace.re`.

Cauchy–Schwarz over the `4ⁿ` Pauli strings (`sq_sum_le_card_mul_sum_sq`) gives
`(∑_g |h_g|)² ≤ 4ⁿ ∑_g h_g²`, and the Parseval identity
`trace_conjTranspose_mul_self_re_eq_sum_pauliCoeff_sq` rewrites
`∑_g h_g² = (2ⁿ)⁻¹ (Mᴴ * M).trace.re`, turning the `4ⁿ` into `2ⁿ`. This is the matrix core of the
coefficient estimate `∑_g |h_g| = O(2ⁿ)` for Nielsen & Chuang Problem 4.3(6). -/
theorem sq_sum_abs_pauliCoeff_le
    {M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ} (hM : M.IsHermitian)
    {h : (Fin n → Fin 4) → ℝ} (hexp : M = ∑ g, (h g : ℂ) • pauliString g) :
    (∑ g, |h g|) ^ 2 ≤ 2 ^ n * (Mᴴ * M).trace.re := by
  rw [trace_conjTranspose_mul_self_re_eq_sum_pauliCoeff_sq hM hexp]
  have hcard : (Finset.univ : Finset (Fin n → Fin 4)).card = 4 ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  calc (∑ g, |h g|) ^ 2
      ≤ ((Finset.univ : Finset (Fin n → Fin 4)).card : ℝ) * ∑ g, |h g| ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ = (4 : ℝ) ^ n * ∑ g, h g ^ 2 := by
        rw [hcard]; push_cast
        exact congrArg _ (Finset.sum_congr rfl fun g _ => sq_abs (h g))
    _ = 2 ^ n * (2 ^ n * ∑ g, h g ^ 2) := by rw [h4, mul_assoc]

end AxQM.Concrete
