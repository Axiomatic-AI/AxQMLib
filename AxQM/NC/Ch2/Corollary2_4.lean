/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Matrix.SVD

/-!
# Nielsen & Chuang, Corollary 2.4 (Singular value decomposition)

Singular value decomposition: A=UDV with U,V unitary and D diagonal non-negative.

The formalisation is in `ToMathlib/Analysis/Matrix/SVD.lean`:

* `Matrix.exists_unitary_mul_diagonal_mul_unitary` — **Corollary 2.4 itself**: for a square matrix
  `A : Matrix n n 𝕜` over an `RCLike` field there exist `U V : Matrix n n 𝕜` in
  `Matrix.unitaryGroup n 𝕜` and `d : n → ℝ` with `0 ≤ d i` for all `i` such that
  `A = U * Matrix.diagonal (RCLike.ofReal ∘ d) * V`. This is the faithful reading of N&C's `A = UDV`
  (the diagonal entries `d i` are the singular values), generalised from `ℂ` to any `RCLike` field.
  The result is stated as an existence claim, matching the corollary, rather than as a canonical
  choice of `U`, `D`, `V`.

## Proof approach

N&C derive the SVD by combining the polar decomposition (`A = SJ`, `S` unitary, `J` positive) with
the spectral theorem (`J = TDT†`). The formalisation instead applies the spectral theorem *directly*
to the positive semidefinite Gram matrix `M = Aᴴ * A`, so it does not depend on a matrix polar
decomposition (which is not yet in the library — see N&C Theorem 2.3):

* diagonalise `M = W * diagonal μ * Wᴴ` with `W` unitary and eigenvalues `μ ≥ 0`, and set
  `σ i = √(μ i)`;
* the columns of `B = A * W` satisfy `Bᴴ * B = diagonal μ`, hence are orthogonal with squared norms
  `σ i ^ 2`;
* normalising the columns with `σ i ≠ 0` yields an orthonormal family which extends to an
  orthonormal basis (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`); the associated
  change-of-basis matrix is the left unitary factor `U`, and `U * diagonal σ = B = A * W`, so
  `A = U * diagonal σ * Wᴴ` with `V = Wᴴ`.
-/
