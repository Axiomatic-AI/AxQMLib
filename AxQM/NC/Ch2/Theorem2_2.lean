/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.JointEigenspace

/-!
# Nielsen & Chuang, Theorem 2.2 (Simultaneous diagonalization theorem)

Simultaneous diagonalization: [A,B]=0 iff Hermitian A,B diagonal in a common basis.

The statement is a theorem of finite-dimensional inner product spaces: commuting self-adjoint
(Hermitian) operators share an orthonormal eigenbasis.

The formalisation, in `ToMathlib/Analysis/InnerProductSpace/JointEigenspace.lean`, extends
`Mathlib/Analysis/InnerProductSpace/JointEigenspace.lean`
— the file that already houses the eigenspace-level decomposition results for
commuting symmetric operators — with the packaged "common orthonormal eigenbasis"
form. "Hermitian" is `LinearMap.IsSymmetric` over an `RCLike` field `𝕜` (for
`𝕜 = ℂ`, `⟨A x, y⟩ = ⟨x, A y⟩` is exactly Hermiticity; the `RCLike` statement is a
faithful generalisation that also covers real-symmetric operators), "diagonal with
respect to a basis" is spelled out as every basis vector being an eigenvector, and
`[A, B] = 0` is `Commute A B` in the endomorphism ring:

* `Module.End.commute_of_forall_apply_basis_eq_smul` — the **easy direction**, in
  full generality (any commutative ring): if every vector of a basis `b` is an
  eigenvector of both `f` and `g` (i.e. `f`, `g` are simultaneously diagonal in
  `b`), then `Commute f g`.
* `LinearMap.IsSymmetric.exists_orthonormalBasis_forall_apply_eq_smul_of_commute`
  — the **hard direction**: two commuting symmetric operators on a
  finite-dimensional inner product space admit an orthonormal basis of common
  eigenvectors, returning explicit eigenvalue functions `μ ν` with
  `A (b i) = μ i • b i` and `B (b i) = ν i • b i`. The joint eigenspaces
  `eigenspace A i.2 ⊓ eigenspace B i.1` give an internal direct sum (the file's
  `directSum_isInternal_of_commute`); reindexing along the finite type of actual
  eigenvalue pairs `Eigenvalues B × Eigenvalues A` makes
  `DirectSum.IsInternal.subordinateOrthonormalBasis` applicable, and each of its
  vectors lies in a single joint eigenspace, hence is a common eigenvector. This is
  the shared construction also consumed by the spectral theorem for normal operators
  (`IsStarNormal.exists_orthonormalBasis_forall_apply_eq_smul` in `NormalOperator.lean`,
  via `T = ℜT + i·ℑT`).
* `LinearMap.IsSymmetric.commute_iff_exists_orthonormalBasis_forall_apply_eq_smul`
  — **Theorem 2.2 itself**: the `↔` combining the two directions, i.e.
  `Commute A B` iff there is an orthonormal basis diagonalizing both `A` and `B`.
-/
