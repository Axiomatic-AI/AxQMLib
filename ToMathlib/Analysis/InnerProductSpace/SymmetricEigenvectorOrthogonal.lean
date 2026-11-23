/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Eigenvectors of a symmetric operator with distinct eigenvalues are orthogonal

Let `E` be an inner product space over `𝕜` (`ℝ` or `ℂ`). This file records that two eigenvectors of
a symmetric (self-adjoint, "Hermitian") operator belonging to different eigenvalues are necessarily
orthogonal — Nielsen & Chuang, Exercise 2.22.

The argument is the classical one-liner. If `T` is symmetric, `T v = μ • v` and `T w = ν • w`, then
symmetry gives `⟪T v, w⟫ = ⟪v, T w⟫`, i.e. `μ̄ * ⟪v, w⟫ = ν * ⟪v, w⟫` (the inner product is
conjugate-linear in the first argument). The eigenvalue `μ` of a symmetric operator is real
(`LinearMap.IsSymmetric.conj_eigenvalue_eq_self`), so `μ̄ = μ` and `(μ - ν) * ⟪v, w⟫ = 0`; since
`μ ≠ ν` this forces `⟪v, w⟫ = 0`.

Mathlib already contains the *eigenspace* form of this fact —
`LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`, that the eigenspaces of a symmetric operator
form an orthogonal family. The result here is the complementary *eigenvector* idiom that N&C's
exercise is phrased in, proved directly from symmetry and the reality of the eigenvalues.

## Main results

* `LinearMap.IsSymmetric.inner_eq_zero_of_hasEigenvector_of_ne`: two eigenvectors of a symmetric
  operator with distinct eigenvalues are orthogonal.
-/

@[expose] public section

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Nielsen & Chuang, Exercise 2.22.** Two eigenvectors of a symmetric (self-adjoint) operator `T`
belonging to *different* eigenvalues are orthogonal: if `T.IsSymmetric`, `v` is an eigenvector with
eigenvalue `μ`, `w` is an eigenvector with eigenvalue `ν`, and `μ ≠ ν`, then `⟪v, w⟫ = 0`.

Symmetry gives `⟪T v, w⟫ = ⟪v, T w⟫`; expanding the eigenvalue equations and using that the
eigenvalue `μ` is real (`conj_eigenvalue_eq_self`) yields `(μ - ν) * ⟪v, w⟫ = 0`, and `μ ≠ ν`
cancels the scalar factor. -/
theorem inner_eq_zero_of_hasEigenvector_of_ne {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {μ ν : 𝕜}
    {v w : E} (hv : Module.End.HasEigenvector T μ v) (hw : Module.End.HasEigenvector T ν w)
    (hμν : μ ≠ ν) : inner 𝕜 v w = 0 := by
  have key : inner 𝕜 (T v) w = inner 𝕜 v (T w) := hT v w
  rw [hv.apply_eq_smul, hw.apply_eq_smul, inner_smul_left, inner_smul_right,
    hT.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector hv)] at key
  -- `key : μ * ⟪v, w⟫ = ν * ⟪v, w⟫`, so `(μ - ν) * ⟪v, w⟫ = 0` and `μ ≠ ν` cancels the factor.
  refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hμν)
  rw [sub_mul, key, sub_self]

end LinearMap.IsSymmetric
