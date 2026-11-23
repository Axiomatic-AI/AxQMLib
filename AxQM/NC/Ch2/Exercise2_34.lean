/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MatrixFunctionExample

/-!
# Nielsen & Chuang, Exercise 2.34

Find the square root and logarithm of the matrix [[4,3],[3,4]].

This is a linear-algebra computation about a concrete `2 × 2` real matrix, using N&C's own
construction of *functions of a normal operator* (§2.1.8):
`f(A) ≡ ∑ₐ f(a) |a⟩⟨a|` over the spectral decomposition.

The formalisation is in `AxQM/Concrete/MatrixFunctionExample.lean`. The matrix
`A = matFourThree` is real symmetric with eigenvalues `7` (eigenvector `(1,1)`) and `1`
(eigenvector `(1,-1)`), hence positive definite, so both functions are well-defined:

* `AxQM.Concrete.matFourThreeSqrt` — the principal square root
  `√A = [[(1+√7)/2, (√7-1)/2], [(√7-1)/2, (1+√7)/2]]`, with
  * `matFourThreeSqrt_mul_self` : `(√A)² = A` (it is a square root of `A`);
  * `matFourThreeSqrt_isHermitian`, `matFourThreeSqrt_posDef` : it is Hermitian and positive
    definite, pinning it down as *the* principal (positive) square root.
* `AxQM.Concrete.matFourThreeLog` — the logarithm `log A = (log 7 / 2) • [[1,1],[1,1]]`,
  with
  * `exp_matFourThreeLog` : `exp(log A) = A` (it is a logarithm of `A`), proved by
    diagonalising `A` and pushing `exp` through the conjugation and the diagonal;
  * `matFourThreeLog_isHermitian` : it is the real-symmetric branch.

Supporting facts (`matFourThree_isHermitian`, the eigenvector matrix `matFourThreeEigen` and
its conjugation lemma `matFourThreeEigen_conj_diagonal`, and `exp_diagonal_logSeven`) are also
in that file.
-/
