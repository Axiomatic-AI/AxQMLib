/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.LinearMap
public import ToMathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Data.Matrix.Basis

/-!
# Matrix representation of a rank-one operator in an orthonormal basis

Let `b` be an orthonormal basis (indexed by a finite type `n`) of a finite-dimensional inner
product space `E` over `𝕜` (`ℝ` or `ℂ`). This file computes the matrix, with respect to `b`, of the
rank-one "ket-bra" operator `|b j⟩⟨b k| = InnerProductSpace.rankOne 𝕜 (b j) (b k)`, which sends
`z ↦ ⟪b k, z⟫ • b j`.

## Main result

* `LinearMap.toMatrixOrthonormal_rankOne`: the matrix of `|b j⟩⟨b k|` in the basis `b` is the
  single-entry matrix `Matrix.single j k 1` — a `1` at row `j`, column `k`, and `0` elsewhere.
  Its `(i, l)` entry is `⟪b i, |b j⟩⟨b k| (b l)⟫ = ⟪b k, b l⟫ * ⟪b i, b j⟫`, which by orthonormality
  is `δ_{ij} δ_{kl}` — nonzero (and equal to `1`) exactly at row `j`, column `k`.
-/

@[expose] public section

namespace LinearMap

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {n : Type*} [Fintype n] [DecidableEq n] [FiniteDimensional 𝕜 E]

/-- **Nielsen & Chuang, Exercise 2.10.** With respect to an orthonormal basis `b` of a
finite-dimensional inner product space, the matrix of the rank-one operator `|b j⟩⟨b k|`
(`InnerProductSpace.rankOne 𝕜 (b j) (b k)`, sending `z ↦ ⟪b k, z⟫ • b j`) is the single-entry
matrix `Matrix.single j k 1`, i.e. a `1` at row `j`, column `k`, and `0` elsewhere.

Concretely the `(i, l)` matrix element is `⟪b i, |b j⟩⟨b k| (b l)⟫ = ⟪b i, b j⟫ * ⟪b k, b l⟫`,
which by orthonormality is `δ_{ij} δ_{kl}`: equal to `1` exactly at row `j`, column `k`. -/
theorem toMatrixOrthonormal_rankOne (b : OrthonormalBasis n 𝕜 E) (j k : n) :
    toMatrixOrthonormal b (InnerProductSpace.rankOne 𝕜 (b j) (b k) : E →ₗ[𝕜] E)
      = Matrix.single j k 1 := by
  ext i l
  simp only [toMatrixOrthonormal_apply_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal,
    Matrix.single_apply]
  -- `(if k = l then 1 else 0) * (if i = j then 1 else 0) = if j = i ∧ k = l then 1 else 0`
  split_ifs <;> simp_all

end LinearMap
