/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Matrix.Normal

/-!
# Nielsen & Chuang, Exercise 2.17 (Normal matrix Hermitian iff real eigenvalues)

Show a normal matrix is Hermitian iff it has real eigenvalues.

A matrix `A` is **normal** when `AᴴA = AAᴴ` (N&C p. 70) and **Hermitian** (self-adjoint) when
`A = Aᴴ`. By the spectral decomposition (N&C Box 2.2), a normal `A` diagonalises in an orthonormal
eigenbasis, `A = ∑ᵢ λᵢ |i⟩⟨i|`, whence `Aᴴ = ∑ᵢ λᵢ* |i⟩⟨i|`; comparing the two,
`A = Aᴴ ⟺ λᵢ = λᵢ*` for every `i`, i.e. every eigenvalue is real. The forward implication
(Hermitian ⟹ real eigenvalues) needs no normality; the converse does.

## The declarations

* `isSelfAdjoint_iff_forall_spectrum_im_eq_zero` (general), in
  `ToMathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Normal.lean`: for a normal element
  `a`
  of a complex C⋆-algebra (`[CStarAlgebra A]`, `IsStarNormal a`),
  `IsSelfAdjoint a ↔ ∀ z ∈ spectrum ℂ a, z.im = 0`.
* `Matrix.isHermitian_iff_forall_spectrum_im_eq_zero`, in `ToMathlib/Analysis/Matrix/Normal.lean`:
  the
  matrix transport corollary — for a normal `A : Matrix n n ℂ` (`n` a finite type),
  `A.IsHermitian ↔ ∀ z ∈ spectrum ℂ A, z.im = 0`.

## N&C ↦ Mathlib dictionary and fidelity

* **Normal** `AᴴA = AAᴴ` is `IsStarNormal A`, i.e. `Commute (star A) A` with `star A = Aᴴ`
  (`Matrix.star_eq_conjTranspose`).
* **Hermitian** `A = Aᴴ` is `Matrix.IsHermitian A` (defined as `Aᴴ = A`), which for matrices is
  definitionally `IsSelfAdjoint A`.
* **Real eigenvalues.** For a finite matrix over `ℂ` the spectrum `spectrum ℂ A` is exactly the set
  of eigenvalues (roots of the characteristic polynomial), so "`A` has real eigenvalues" is
  `∀ z ∈ spectrum ℂ A, z.im = 0` — every spectral value lies on the real axis.

The statement is fixed to `ℂ`, matching N&C's complex Hilbert space, and is faithful, not weakened:
it quantifies over an arbitrary finite index type `n` with no dimension fixed and adds no hypothesis
beyond normality. (Over `ℝ` the `ℝ`-spectrum would drop the genuinely complex eigenvalues, so the
characterization would no longer express "real eigenvalues".)

The general lemma proves both directions in any complex C⋆-algebra carrying the continuous
functional calculus for normal elements: the forward direction is
`IsSelfAdjoint.im_eq_zero_of_mem_spectrum` (needs no normality), and the converse recovers
self-adjointness from a real spectrum via `QuasispectrumRestricts.isSelfAdjoint` (this is where
normality is used). The matrix statement is a thin corollary: `Matrix n n ℂ` is not registered as a
`CStarAlgebra`, so the claim is transported along the star-algebra equivalence
`Matrix.toEuclideanCLM` to `EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n` (where the general lemma
applies), with spectrum / `IsSelfAdjoint` / `IsStarNormal` transferring across the equivalence. This
is the analytic incarnation of N&C's spectral-decomposition argument.
-/
