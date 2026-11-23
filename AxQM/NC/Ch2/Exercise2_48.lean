/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Matrix.PolarDecomposition

/-!
# Nielsen & Chuang, Exercise 2.48 (polar decomposition of positive/unitary/Hermitian matrices)

Find the polar decomposition of a positive/unitary/Hermitian matrix.

The polar decomposition (N&C Theorem 2.3, §2.1.10) writes a linear operator `A` as `A = UJ = KU`
with `U` unitary and the *positive* factors the canonical `J ≡ √(A†A)`, `K ≡ √(AA†)`. The exercise
asks for these factors in three special cases:

* **Positive `P`.** `P† = P` and `P ≥ 0`, so `J = √(P†P) = √(P²) = P` and likewise `K = P`; the
  decomposition is `P = I · P` (unitary factor the identity).
* **Unitary `U`.** `U†U = UU† = I`, so `J = √(I) = I` and `K = I`; the decomposition is `U = U · I`
  (positive factor the identity).
* **Hermitian `H`.** `H† = H`, so `J = √(H†H) = √(H²) = |H|`, the absolute value of `H`; the
  decomposition is `H = sgn(H) · |H|` with `sgn(H)` the sign of `H`.

These are statements about matrices over `ℝ`/`ℂ` and their positive semidefinite square root.

## The declarations

The formalisation is in `ToMathlib/Analysis/Matrix/PolarDecomposition.lean`, where `√` is the
positive semidefinite square root `CFC.sqrt` and `Aᴴ` is `A†` (under
`open scoped MatrixOrder ComplexOrder`).

* `Matrix.PosSemidef.sqrt_conjTranspose_mul_self` /
  `Matrix.PosSemidef.sqrt_mul_conjTranspose_self`
  — positive case: `√(Pᴴ * P) = P` and `√(P * Pᴴ) = P` (both polar factors are `P`);
  `Matrix.PosSemidef.eq_one_mul_sqrt_conjTranspose_mul_self` records the decomposition
  `P = 1 * √(Pᴴ * P)` (i.e. `P = I · P`).
* `Matrix.sqrt_conjTranspose_mul_self_of_mem_unitaryGroup` /
  `Matrix.sqrt_mul_conjTranspose_self_of_mem_unitaryGroup` — unitary case: `√(Uᴴ * U) = 1` and
  `√(U * Uᴴ) = 1` (both polar factors are the identity);
  `Matrix.eq_mul_sqrt_conjTranspose_mul_self_of_mem_unitaryGroup` records the decomposition
  `U = U * √(Uᴴ * U)` (i.e. `U = U · I`).
* `Matrix.IsHermitian.sqrt_conjTranspose_mul_self` — Hermitian case (positive factor):
  `√(Hᴴ * H) = √(H ^ 2)`, the absolute value `|H|`.
* `Matrix.IsHermitian.polarUnitary` (`= cfc polarSign H`, the sign of `H`),
  `Matrix.IsHermitian.polarUnitary_mem_unitaryGroup` and
  `Matrix.IsHermitian.eq_polarUnitary_mul_sqrt_conjTranspose_mul_self` — Hermitian case (unitary
  factor and full decomposition): `sgn(H)` is unitary and `H = sgn(H) · √(Hᴴ * H)`, i.e. the polar
  decomposition `H = sgn(H) · |H|`
  (`Matrix.IsHermitian.exists_mem_unitaryGroup_mul_sqrt_conjTranspose_mul_self` is its existence
  form). The value `1` chosen at `0` makes `sgn(H)` a genuine unitary even for singular `H` (where
  the sign is otherwise only a partial isometry), so the decomposition holds for every Hermitian
  matrix — no invertibility hypothesis.
* `Matrix.sqrt_conjTranspose_mul_self_eq_self_iff` — the polar factor `√(Aᴴ * A)` equals `A` iff `A`
  is positive semidefinite; so among Hermitian matrices `|H| = √(H ^ 2)` equals `H` exactly for the
  positive ones (and differs from `H` otherwise).
-/
