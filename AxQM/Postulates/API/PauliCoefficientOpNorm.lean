/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliExpansion
import AxQM.Postulates.API.QuditMeasurement
import AxQM.Concrete.PauliCoefficientBound

/-!
# AxQM.Postulates.API — operator-norm bound on the Pauli coefficients (N&C 4.3(6))

This file proves one ingredient of Nielsen & Chuang, Problem 4.3(6): the
sum of the absolute values of a Hamiltonian's real Pauli coefficients is controlled by its operator
norm,
`∑_g |h_g| ≤ 2ⁿ · ‖H.op‖`. Together with the part-(1b) spectrum bound `‖H.op‖ ≤ 2π` this gives the
total Pauli weight `Λ = ∑_g |h_g| = O(2ⁿ)` that the literal `O(n · 16ⁿ / ε)` gate count of Problem
4.3(6) needs (`Λ² = O(4ⁿ)` is the first-order Trotter constant).

## What this delivers

For a Hamiltonian `H : Observable (qudit (2ⁿ))` on the `n`-qubit register:

* `Observable.trace_stdMatrix_conjTranspose_mul_self_re_le` — the **Hilbert–Schmidt vs. operator
  norm** bridge `(H.stdMatrixᴴ * H.stdMatrix).trace.re ≤ 2ⁿ · ‖H.op‖²`. Its computational-basis
  matrix `A = H.stdMatrix` has `(Aᴴ A).trace = ∑_j ‖A · e_j‖²_column = ∑_j ‖H.op |j⟩‖²` (each column
  norm is a Parseval sum, `OrthonormalBasis.sum_sq_norm_inner_right` over the computational
  orthonormal basis), and each `‖H.op |j⟩‖ ≤ ‖H.op‖` since `|j⟩` is a unit vector; the `2ⁿ = d`
  columns then give the `d · ‖H.op‖²` bound. This is the operator-norm form of the Frobenius bound
  `tr(MᴴM) = ∑ σ_i² ≤ d · ‖M‖²`.
* `Observable.sum_abs_pauliCoeff_le` — **Problem 4.3(6) (op-norm form)**: for any real
  Pauli expansion `H.stdMatrix.submatrix _ _ = ∑_g (h_g : ℂ) • pauliString g` (part (2),
  `Observable.exists_real_pauliString_expansion`), `∑_g |h_g| ≤ 2ⁿ · ‖H.op‖`. It chains the
  `Concrete/` matrix core `Concrete.sq_sum_abs_pauliCoeff_le` (`(∑_g |h_g|)² ≤ 2ⁿ · tr(MᴴM).re`)
  with the trace bound above: `(∑_g |h_g|)² ≤ 2ⁿ · 2ⁿ ‖H.op‖² = (2ⁿ ‖H.op‖)²`, and both sides are
  nonnegative.
* `Observable.opNorm_le_of_spectrum_subset_Icc` — the **self-adjoint operator-norm-from-spectrum**
  bound: if `spectrum ℂ H.op ⊆ ℝ ∩ [0, c]` (with `0 ≤ c`) then `‖H.op‖ ≤ c`. For a self-adjoint
  operator the norm is the spectral radius (`ContinuousLinearMap.spectralRadius_eq_nnNorm`), and
  each eigenvalue `k = r` has `‖k‖ = |r| = r ≤ c`, so the radius `⨆ ‖k‖` is `≤ c`.
* `Observable.sum_abs_pauliCoeff_le_of_spectrum_Icc` — the **generator specialisation**: combining
  the two bounds above, if additionally `spectrum ℂ H.op ⊆ ℝ ∩ [0, c]` then `∑_g |h_g| ≤ 2ⁿ · c`.
  With
  `c = 2π` for the generator `H = i ln U` (part (1b),
  `Evolution.exists_hamiltonian_generator_spectrum_Icc`) this is the total Pauli weight bound
  `Λ = ∑_g |h_g| ≤ 2ⁿ · 2π = O(2ⁿ)` that the gate count of Problem 4.3(6) uses.

## Design

* **Reusable, generator-independent core.** N&C introduce `H` as `i ln U`, but the coefficient
  estimate uses only that `H` is a Hamiltonian (self-adjoint) with a real Pauli expansion; stating
  `sum_abs_pauliCoeff_le` for every `Observable` (and every real `h` witnessing the expansion) is
  the faithful reusable form, and the generator specialisation `..._of_spectrum_Icc` layers the
  spectrum bound on top by a single `.trans`. The `[0, 2π]` spectrum itself is supplied per-unitary
  by part (1b); this file states the bound for a general `c` so that it can be instantiated for
  each unitary.
-/

open scoped InnerProductSpace Matrix ENNReal NNReal

noncomputable section

namespace AxQM

variable {d : ℕ}

/-- **Hilbert–Schmidt vs. operator norm for a Hamiltonian's computational-basis matrix.** For a
Hamiltonian `H : Observable (qudit d)`, the real part of the trace of `H.stdMatrixᴴ * H.stdMatrix`
(the squared Frobenius norm of the computational-basis matrix `A = H.stdMatrix`) is bounded by
`d · ‖H.op‖²`.

The `(a, a)` diagonal entry of `Aᴴ A` is `∑_i ‖A i a‖² = ‖H.op |a⟩‖²` (each entry
`A i a = ⟪|i⟩, H.op|a⟩⟫`, so the column-`a` squared norm is the Parseval sum
`∑_i ‖⟪|i⟩, H.op|a⟩⟫‖² = ‖H.op|a⟩‖²` over the
computational orthonormal basis). Since `|a⟩` is a unit vector, `‖H.op|a⟩‖ ≤ ‖H.op‖`, and summing
the `d` diagonal entries gives `tr(Aᴴ A).re = ∑_a ‖H.op|a⟩‖² ≤ d · ‖H.op‖²`. -/
theorem Observable.trace_stdMatrix_conjTranspose_mul_self_re_le (H : Observable (qudit d)) :
    (H.stdMatrixᴴ * H.stdMatrix).trace.re ≤ (d : ℝ) * ‖H.op‖ ^ 2 := by
  -- Each diagonal entry of `Aᴴ A` is `‖H.op |a⟩‖²` as a nonnegative real.
  have hdiag : ∀ a : Fin d,
      (H.stdMatrixᴴ * H.stdMatrix) a a = ((‖H.op (quditBasis a).vec‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [Matrix.mul_apply]
    have hterm : ∀ i : Fin d, H.stdMatrixᴴ a i * H.stdMatrix i a
        = ((‖H.stdMatrix i a‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [Matrix.conjTranspose_apply, ← starRingEnd_apply, RCLike.conj_mul]
      norm_cast
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Complex.ofReal_sum]
    congr 1
    -- The column-`a` squared norm is a Parseval sum over the computational orthonormal basis.
    have hpar := (quditOrthonormalBasis d).sum_sq_norm_inner_right (H.op (quditBasis a).vec)
    rw [← hpar]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Observable.stdMatrix_apply, quditOrthonormalBasis_apply]
  have htrace : (H.stdMatrixᴴ * H.stdMatrix).trace
      = ((∑ a, ‖H.op (quditBasis a).vec‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [Finset.sum_congr rfl (fun a _ => hdiag a), ← Complex.ofReal_sum]
  rw [htrace, Complex.ofReal_re]
  calc ∑ a, ‖H.op (quditBasis a).vec‖ ^ 2
      ≤ ∑ _a : Fin d, ‖H.op‖ ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        have hle : ‖H.op (quditBasis a).vec‖ ≤ ‖H.op‖ := by
          refine (H.op.le_opNorm _).trans ?_; rw [(quditBasis a).normalized, mul_one]
        gcongr
    _ = (d : ℝ) * ‖H.op‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Nielsen & Chuang, Problem 4.3(6) (operator-norm form): the total Pauli weight is
`O(2ⁿ)`.** For a Hamiltonian `H : Observable (qudit (2ⁿ))` on the `n`-qubit register with any real
Pauli expansion `H.stdMatrix.submatrix _ _ = ∑_g (h_g : ℂ) • pauliString g` (part (2),
`Observable.exists_real_pauliString_expansion`), the total Pauli weight is bounded by the operator
norm: `∑_g |h_g| ≤ 2ⁿ · ‖H.op‖`.

Chains the `Concrete/` matrix core `Concrete.sq_sum_abs_pauliCoeff_le` — Pauli Parseval +
Cauchy–Schwarz gives `(∑_g |h_g|)² ≤ 2ⁿ · (MᴴM).trace.re` for `M = H.stdMatrix.submatrix _ _` — with
the Hilbert–Schmidt bound `trace_stdMatrix_conjTranspose_mul_self_re_le` (the trace is reindex-
invariant, so `(MᴴM).trace = (H.stdMatrixᴴ H.stdMatrix).trace ≤ 2ⁿ ‖H.op‖²` after taking real
parts): `(∑_g |h_g|)² ≤ 2ⁿ · 2ⁿ ‖H.op‖² = (2ⁿ ‖H.op‖)²`, and both sides are nonnegative.

With `‖H.op‖ ≤ 2π` (the part-(1b) spectrum bound for the generator `H = i ln U`) this is
`Λ = ∑_g |h_g| = O(2ⁿ)`, whence the first-order Trotter constant `C = O(Λ²) = O(4ⁿ)` and N&C's
literal `O(n · 16ⁿ / ε)`. -/
theorem Observable.sum_abs_pauliCoeff_le {n : ℕ} (H : Observable (qudit (2 ^ n)))
    {h : (Fin n → Fin 4) → ℝ}
    (hexp : H.stdMatrix.submatrix finFunctionFinEquiv finFunctionFinEquiv
        = ∑ g, (h g : ℂ) • Concrete.pauliString g) :
    ∑ g, |h g| ≤ 2 ^ n * ‖H.op‖ := by
  set e : (Fin n → Fin 2) ≃ Fin (2 ^ n) := finFunctionFinEquiv with he
  set M := H.stdMatrix.submatrix e e with hM
  have hMherm : M.IsHermitian := H.stdMatrix_isHermitian.submatrix e
  -- The `Concrete/` matrix core.
  have hbeta : (∑ g, |h g|) ^ 2 ≤ 2 ^ n * (Mᴴ * M).trace.re :=
    Concrete.sq_sum_abs_pauliCoeff_le hMherm hexp
  -- The trace is invariant under the bit-string reindexing.
  have hreindex : (Mᴴ * M).trace = (H.stdMatrixᴴ * H.stdMatrix).trace := by
    rw [hM, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
    exact e.sum_comp (fun k => (H.stdMatrixᴴ * H.stdMatrix) k k)
  -- Combine into a bound on `(∑ |h_g|)²`.
  have hsq : (∑ g, |h g|) ^ 2 ≤ (2 ^ n * ‖H.op‖) ^ 2 := by
    refine hbeta.trans ?_
    rw [hreindex]
    have hHS := H.trace_stdMatrix_conjTranspose_mul_self_re_le
    have h2n : ((2 : ℝ) ^ n : ℝ) = ((2 ^ n : ℕ) : ℝ) := by push_cast; ring
    calc (2 : ℝ) ^ n * (H.stdMatrixᴴ * H.stdMatrix).trace.re
        ≤ (2 : ℝ) ^ n * (((2 ^ n : ℕ) : ℝ) * ‖H.op‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hHS (by positivity)
      _ = (2 ^ n * ‖H.op‖) ^ 2 := by rw [← h2n]; ring
  -- Take nonnegative square roots.
  have h1 : (0 : ℝ) ≤ ∑ g, |h g| := Finset.sum_nonneg fun g _ => abs_nonneg _
  have h2 : (0 : ℝ) ≤ 2 ^ n * ‖H.op‖ := by positivity
  have hroot := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at hroot

/-- **Operator norm of a self-adjoint operator from its spectrum.** For a Hamiltonian
`H : Observable S` with spectrum in `ℝ ∩ [0, c]` (`spectrum ℂ H.op ⊆ Complex.ofReal '' [0, c]`,
with `0 ≤ c`), the operator norm is bounded by `c`: `‖H.op‖ ≤ c`.

Since `H.op` is self-adjoint, its operator norm equals its spectral radius
(`ContinuousLinearMap.spectralRadius_eq_nnNorm`), which is the supremum of `‖k‖` over the spectrum;
each spectral value `k = r` is a real number in `[0, c]`, so `‖k‖ = |r| = r ≤ c`, and the sup
is `≤ c`. (`S.space` is finite-dimensional, hence complete.) -/
theorem Observable.opNorm_le_of_spectrum_subset_Icc {S : QSystem} (H : Observable S)
    {c : ℝ} (hc : 0 ≤ c) (hspec : spectrum ℂ H.op ⊆ Complex.ofReal '' Set.Icc 0 c) :
    ‖H.op‖ ≤ c := by
  have : CompleteSpace S.space := FiniteDimensional.completeSpace ℂ S.space
  have hsr : spectralRadius ℂ H.op = ‖H.op‖₊ :=
    ContinuousLinearMap.spectralRadius_eq_nnNorm H.op H.selfAdjoint
  have hbound : spectralRadius ℂ H.op ≤ ENNReal.ofReal c := by
    rw [spectralRadius_eq_of_unital]
    refine iSup₂_le fun k hk => ?_
    obtain ⟨r, hr, rfl⟩ := hspec hk
    rw [← eNorm_eq_nnNorm, ← ofReal_norm,
      show ‖(↑r : ℂ)‖ = r by simp [Real.norm_eq_abs, abs_of_nonneg hr.1]]
    exact ENNReal.ofReal_le_ofReal hr.2
  rw [hsr] at hbound
  calc ‖H.op‖ = ((‖H.op‖₊ : ℝ≥0∞)).toReal := by simp
    _ ≤ (ENNReal.ofReal c).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = c := ENNReal.toReal_ofReal hc

/-- **Nielsen & Chuang, Problem 4.3(6): the total Pauli weight is `O(2ⁿ)`.** For a
Hamiltonian `H : Observable (qudit (2ⁿ))` whose spectrum lies in `ℝ ∩ [0, c]` (with `0 ≤ c`) and any
real Pauli expansion `H.stdMatrix.submatrix _ _ = ∑_g (h_g : ℂ) • pauliString g`, the total Pauli
weight is `∑_g |h_g| ≤ 2ⁿ · c`.

Chains `Observable.sum_abs_pauliCoeff_le` (`∑_g |h_g| ≤ 2ⁿ · ‖H.op‖`) with the spectrum bound
`Observable.opNorm_le_of_spectrum_subset_Icc` (`‖H.op‖ ≤ c`). With `c = 2π` for the generator
`H = i ln U` of a unitary (part (1b), `Evolution.exists_hamiltonian_generator_spectrum_Icc`) this is
`Λ = ∑_g |h_g| ≤ 2ⁿ · 2π = O(2ⁿ)`, whence the first-order Trotter constant `C = O(Λ²) = O(4ⁿ)` and
N&C's literal `O(n · 16ⁿ / ε)` gate count. -/
theorem Observable.sum_abs_pauliCoeff_le_of_spectrum_Icc {n : ℕ} (H : Observable (qudit (2 ^ n)))
    {c : ℝ} (hc : 0 ≤ c) (hspec : spectrum ℂ H.op ⊆ Complex.ofReal '' Set.Icc 0 c)
    {h : (Fin n → Fin 4) → ℝ}
    (hexp : H.stdMatrix.submatrix finFunctionFinEquiv finFunctionFinEquiv
        = ∑ g, (h g : ℂ) • Concrete.pauliString g) :
    ∑ g, |h g| ≤ 2 ^ n * c := by
  refine (H.sum_abs_pauliCoeff_le hexp).trans ?_
  gcongr
  exact H.opNorm_le_of_spectrum_subset_Icc hc hspec

end AxQM
