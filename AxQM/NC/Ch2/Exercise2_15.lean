/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Nielsen & Chuang, Exercise 2.15 (Involutivity of the adjoint)

Show that (A^dagger)^dagger = A.

The **adjoint** `A†` of an operator `A` is the unique operator satisfying N&C's eq. (2.32),
`(|v⟩, A|w⟩) = (A†|v⟩, |w⟩)`, for all `|v⟩, |w⟩`; equivalently, in a matrix representation, `A†` is
the conjugate-transpose `A† ≡ (A∗)ᵀ` (N&C p. 70). The claim is that Hermitian conjugation is an
*involution*: applying it twice returns the original operator, `(A†)† = A`.

The result is *already present in Mathlib*, so
nothing new is introduced: the exercise is discharged by the existing declaration below, which
corresponds to N&C's notation as explained here. The sibling adjoint exercise
`Exercise2_13` (`(|w⟩⟨v|)† = |v⟩⟨w|`) is covered by the same Mathlib file.

## The declaration

`ContinuousLinearMap.adjoint_adjoint`, in `Mathlib/Analysis/InnerProductSpace/Adjoint.lean`,
states — for `A : E →L[𝕜] F` with `E`, `F` complete inner-product spaces over `𝕜` (`RCLike 𝕜`) —
that `ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint A) = A`.
This is exactly `(A†)† = A`.

## N&C ↦ Mathlib dictionary and fidelity

* `V` is a (finite-dimensional, complex) Hilbert space; Mathlib's lemma is over any complete
  inner-product spaces `E`, `F` over `𝕜` (`RCLike 𝕜`, i.e. `ℝ` or `ℂ`), and even allows the domain
  and codomain to differ. N&C's `V = ℂ^d` is the instance `E = F = V`, `𝕜 = ℂ`; finite
  dimensionality supplies the completeness Mathlib requires. This is a faithful generalisation, not
  a weakening — the exercise's "any operator `A`" is universally quantified over `A` here with no
  extra hypotheses.
* The **adjoint** `A†` is `ContinuousLinearMap.adjoint A`, whose defining property
  `ContinuousLinearMap.adjoint_inner_left`, `⟪A† y, x⟫ = ⟪y, A x⟫`, is precisely N&C's eq. (2.32)
  `(A†|v⟩, |w⟩) = (|v⟩, A|w⟩)` (both inner products conjugate-linear in the first argument). This is
  the same operator/adjoint framing used by `Exercise2_13`.
* Under this dictionary `ContinuousLinearMap.adjoint_adjoint` reads `(A†)† = A` — precisely the
  exercise's claim. The proof in Mathlib is by uniqueness of the adjoint: `(A†)†` and `A` satisfy
  the same defining inner-product identity, hence agree.
* The matrix picture N&C gives, `A† ≡ (A∗)ᵀ`, has the same content: conjugate-transposing twice
  restores the matrix (Mathlib's `Matrix.conjTranspose_conjTranspose`, `Aᴴᴴ = A`); it is the
  coordinate form of the same involution, so either declaration is a faithful formalisation, and the
  operator form is chosen here to match the adjoint framing of the adjacent adjoint exercises.
-/
