/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochMatrix

/-!
# Concrete: the single-qubit Pauli average `E(A) = (A + XAX + YAY + ZAZ)/4`

This file defines the map

`E(A) = (A + X A X + Y A Y + Z A Z) / 4`

on `2 × 2` complex matrices — Nielsen & Chuang's operator `E` of eq. (8.104), the uniform
average of `A` over conjugation by the four Pauli matrices `I, X, Y, Z` — and records the
matrix facts of **Exercise 8.17**, the verification of eq. (8.101)

`I/2 = (ρ + X ρ X + Y ρ Y + Z ρ Z) / 4`.

The engine is a single closed computation:

* `pauliConjSum_eq` — for **every** `2 × 2` matrix `A`,
  `A + X A X + Y A Y + Z A Z = (2 · tr A) • I`. Conjugating by `X`/`Y`/`Z` permutes and
  sign-flips the entries of `A` (e.g. `X A X` swaps the two rows and the two columns), and the
  four contributions cancel off the diagonal while the diagonal entries add up to `2 · tr A`.

From it, the two displays the exercise asks for:

* `pauliAverage_eq_trace` — `E(A) = (½ · tr A) • I`, the general form of `E`, from which
* `pauliAverage_one`, `pauliAverage_pauliX`, `pauliAverage_pauliY`, `pauliAverage_pauliZ` —
  N&C eq. (8.105): `E(I) = I` (`tr I = 2`) and `E(X) = E(Y) = E(Z) = 0` (the non-identity Pauli
  matrices are traceless), and
* `pauliAverage_blochMatrix` — N&C eq. (8.101): for a single-qubit density matrix written in the
  **Bloch representation** `ρ = blochMatrix r = ½(I + r·σ)`, one has `E(ρ) = ½ I = I/2`, because
  such a `ρ` has trace one (`blochMatrix_trace`). This is exactly the identity (8.101), for an
  arbitrary Bloch vector `r` (indeed for any trace-one matrix, via `pauliConjSum_eq`).

Everything here is stated for matrices (`Matrix`, `Concrete.pauliX/Y/Z`,
`Concrete.blochMatrix`). It is the shared mathematical core imported by Exercise 8.17
(`AxQM/NC/Ch8/Exercise8_17.lean`), whose depolarizing-channel context
(eq. (8.100)–(8.102)) is the physics reading of this average.

## Design notes

* `E` is defined directly as `(4⁻¹ : ℂ) • (A + X A X + Y A Y + Z A Z)` rather than through the
  indexed Pauli family `Concrete.pauli`, so the statement matches N&C's eq. (8.104) letter for
  letter and the individual `E(X)`, `E(Y)`, `E(Z)` displays read off with no index bookkeeping.
* All four eq. (8.105) facts and eq. (8.101) are corollaries of the one strengthened lemma
  `pauliConjSum_eq` (valid for every `A`) specialised through the trace: `tr I = 2` gives
  `E(I) = I`, `tr σ = 0` gives `E(σ) = 0`, and `tr ρ = 1` gives `E(ρ) = I/2` — the Bloch
  representation entering only through its trace-one property.
-/

namespace AxQM.Concrete

open Matrix

/-- **The Pauli average `E(A) = (A + XAX + YAY + ZAZ)/4`** on `2 × 2` complex matrices, Nielsen &
Chuang eq. (8.104): the uniform average of `A` over conjugation by the four Pauli matrices
`I, X, Y, Z`. (The `I`-conjugate is `A` itself.) This is the completely depolarizing projection
`A ↦ (tr A / 2) • I` behind the depolarizing channel of Section 8.3.4. -/
noncomputable def pauliAverage (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (4⁻¹ : ℂ) • (A + pauliX * A * pauliX + pauliY * A * pauliY + pauliZ * A * pauliZ)

/-- **The sum behind the Pauli average.** For every `2 × 2` complex matrix `A`,
`A + X A X + Y A Y + Z A Z = (2 · tr A) • I`. Conjugation by `X` swaps both rows and both columns
of `A`, by `Y` does the same up to sign flips, and by `Z` flips the signs of the off-diagonal
entries; summing, the off-diagonal entries cancel and each diagonal entry becomes `2 (A₀₀ + A₁₁)`.
This is the engine for Nielsen & Chuang eqs. (8.105) and (8.101). -/
theorem pauliConjSum_eq (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A + pauliX * A * pauliX + pauliY * A * pauliY + pauliZ * A * pauliZ
      = (2 * A.trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliX, pauliY, pauliZ, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.trace_fin_two, Matrix.smul_apply, Matrix.one_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, ite_true,
      ite_false] <;>
    ring_nf <;>
    simp only [Complex.I_sq] <;>
    ring

/-- **`E(A) = (½ · tr A) • I`**: the closed form of the Pauli average, dividing `pauliConjSum_eq`
by `4`. Every value of `E` is a scalar multiple of the identity, the scalar being half the trace. -/
theorem pauliAverage_eq_trace (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pauliAverage A = (2⁻¹ * A.trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pauliAverage, pauliConjSum_eq, smul_smul]
  congr 1
  ring

/-- **`E(I) = I`** (Nielsen & Chuang eq. (8.105)): the identity is a fixed point of the Pauli
average, since `tr I = 2` and `½ · 2 = 1`. -/
theorem pauliAverage_one : pauliAverage (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [pauliAverage_eq_trace, trace_one_fin_two]; norm_num

/-- **`E(X) = 0`** (Nielsen & Chuang eq. (8.105)): the Pauli average annihilates `X`, which is
traceless (`tr X = 0`). -/
theorem pauliAverage_pauliX : pauliAverage pauliX = 0 := by
  rw [pauliAverage_eq_trace, pauliX_trace, mul_zero, zero_smul]

/-- **`E(Y) = 0`** (Nielsen & Chuang eq. (8.105)): the Pauli average annihilates `Y`, which is
traceless (`tr Y = 0`). -/
theorem pauliAverage_pauliY : pauliAverage pauliY = 0 := by
  rw [pauliAverage_eq_trace, pauliY_trace, mul_zero, zero_smul]

/-- **`E(Z) = 0`** (Nielsen & Chuang eq. (8.105)): the Pauli average annihilates `Z`, which is
traceless (`tr Z = 0`). -/
theorem pauliAverage_pauliZ : pauliAverage pauliZ = 0 := by
  rw [pauliAverage_eq_trace, pauliZ_trace, mul_zero, zero_smul]

/-- **`E(ρ) = I/2`** for a single-qubit density matrix `ρ` in the Bloch representation
`ρ = blochMatrix r = ½(I + r·σ)` — Nielsen & Chuang eq. (8.101),
`I/2 = (ρ + X ρ X + Y ρ Y + Z ρ Z)/4`. Because a Bloch matrix has trace one
(`blochMatrix_trace`), `pauliAverage_eq_trace` collapses `E(ρ)` to `½ · I`. The identity in fact
holds for any trace-one matrix; here it is stated over the Bloch representation the exercise
prescribes, for an arbitrary Bloch vector `r`. -/
theorem pauliAverage_blochMatrix (r : Fin 3 → ℝ) :
    pauliAverage (blochMatrix r) = (2⁻¹ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pauliAverage_eq_trace, blochMatrix_trace, mul_one]

end AxQM.Concrete
