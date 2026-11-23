/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.NormalOperator

/-!
# Nielsen & Chuang, Theorem 2.1 (Spectral decomposition)

Spectral decomposition: normal operator M is diagonal in some orthonormal basis, and conversely.

N&C's "vector space" is a finite-dimensional complex Hilbert space, and "diagonal with respect to
some orthonormal basis" means an orthonormal eigenbasis exists (`M = ∑ᵢ λᵢ |i⟩⟨i|`). "Normal"
means `M` commutes with its adjoint. Over `ℂ` (algebraically closed) this holds; over `ℝ` it can
fail (e.g. a rotation), so the complex hypothesis is genuine. N&C's converse ("any diagonalizable
operator is normal") is read as its intended meaning: an operator diagonal *in an orthonormal
basis* is normal — a merely diagonalisable operator (non-orthogonal eigenbasis) need not be.

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/NormalOperator.lean`:

* `IsStarNormal.exists_orthonormalBasis_forall_apply_eq_smul` — the forward direction: a normal
  operator (`IsStarNormal T`, i.e. `Commute (adjoint T) T`) has an orthonormal basis `b` and
  eigenvalues `μ` with `T (b i) = μ i • b i` for all `i`.
* `LinearMap.isStarNormal_of_forall_apply_eq_smul` — the converse: an operator diagonal in an
  orthonormal basis is normal.
* `LinearMap.isStarNormal_iff_exists_orthonormalBasis` — the theorem itself, as an equivalence
  between normality and the existence of an orthonormal eigenbasis.
-/
