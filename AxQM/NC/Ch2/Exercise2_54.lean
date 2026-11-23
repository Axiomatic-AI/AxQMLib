/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.Normed.Algebra.Exponential
import ToMathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Nielsen & Chuang, Exercise 2.54 (Exponential of a sum of commuting operators)

For commuting Hermitian A,B prove exp(A)exp(B)=exp(A+B).

The statement is a fact about the operator (matrix) exponential: if two operators commute, the
exponential of their sum factors as the product of their exponentials.

The result is *already present in Mathlib* — the exponential's additivity for commuting
elements is a standard lemma, in both its Banach-algebra and its matrix form. The exercise is
discharged by the existing declarations below, which correspond to N&C's statement as follows.

## The declarations

**Banach-algebra form (general).** In `Mathlib/Analysis/Normed/Algebra/Exponential.lean`, for a
complete normed algebra `𝔸` over `ℚ` (e.g. any C*-algebra, in particular the bounded operators on a
Hilbert space) and `x y : 𝔸`,

* `NormedSpace.exp_add_of_commute`, whose statement is
  `Commute x y → NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y`,

is exactly `exp(A) exp(B) = exp(A + B)` under the commutativity hypothesis `AB = BA`.

**Matrix form (most faithful to N&C's finite-dimensional operators).** In
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`, for a finite index type `m` and a complete
normed algebra `𝔸` over `ℚ`, with `A B : Matrix m m 𝔸`,

* `Matrix.exp_add_of_commute`, whose statement is
  `Commute A B → NormedSpace.exp (A + B) = NormedSpace.exp A * NormedSpace.exp B`.

Instantiating `m := Fin d` and `𝔸 := ℂ` gives the exercise verbatim for `d × d` complex operators.

**The `n`-fold generalisation** — the same identity for a pairwise-commuting family — is recorded by
`NormedSpace.exp_sum_of_commute` and its matrix counterpart `Matrix.exp_sum_of_commute`
(`exp(∑ᵢ fᵢ) = ∏ᵢ exp(fᵢ)` over a `Finset`, with the product taken as a `Finset.noncommProd` since
matrix multiplication is not commutative in general).

## N&C ↦ Mathlib dictionary and fidelity

* **The exponential.** `exp(A)` is the operator/matrix exponential defined by the power series
  `∑ₖ Aᵏ / k!`, which is `NormedSpace.exp` (`Matrix.exp` on `Matrix m m 𝔸` is definitionally this
  exponential of the matrix ring). This is the same object N&C names via its spectral form
  `exp(A) = ∑ₐ e^a |a⟩⟨a|` for a Hermitian `A = ∑ₐ a |a⟩⟨a|` (Section 2.1.9): the two agree, since
  applying the entire-function power series entrywise in the eigenbasis reproduces the spectral
  formula.
* **Commutativity** `AB = BA` is `Commute A B`; it is the sole hypothesis the conclusion needs.
* **The `Hermitian` hypothesis is superfluous — dropping it strengthens, not weakens, the theorem.**
  The identity `exp(A) exp(B) = exp(A + B)` holds for *any* commuting elements of a Banach algebra,
  Hermitian or not; the proof is the Cauchy product of the two exponential series, valid whenever
  `A` and `B` commute. N&C attaches "Hermitian" because the surrounding context is Hermitian
  observables/Hamiltonians and because its intended proof route — the spectral decomposition of
  Section 2.1.9 — is available for Hermitian (indeed normal) operators: commuting Hermitian
  operators are *simultaneously diagonalisable* (N&C Theorem 2.2, in `ToMathlib/`), so in the
  common eigenbasis `A` and `B` are diagonal and the identity is the scalar law `e^{aₖ} e^{bₖ} =
  e^{aₖ + bₖ}` on each eigenvalue. Mathlib's `Commute`-only statement subsumes this argument, so
  requiring `A.IsHermitian` and `B.IsHermitian` would only add unused hypotheses. Recording the
  general lemma is therefore a faithful generalisation of the exercise, not a weakening of it.
-/
