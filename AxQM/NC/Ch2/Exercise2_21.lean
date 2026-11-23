/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.SelfAdjointOperator

/-!
# Nielsen & Chuang, Exercise 2.21 (Spectral decomposition — the Hermitian case)

Repeat the spectral decomposition proof for the Hermitian case.

Box 2.2 (Theorem 2.1) is the spectral decomposition for **normal** operators: any normal operator
`M` on a finite-dimensional space is diagonal with respect to some orthonormal basis, and
conversely any operator diagonal in an orthonormal basis is normal. This exercise asks for the
**Hermitian** (self-adjoint, `M† = M`) special case. Its distinctive content — and the point of
"simplifying wherever possible" — is that the eigenvalues are then **real**, and the whole
argument holds over `ℝ` as well as `ℂ` (no Cartesian decomposition `M = A + iB` and no induction on
`QMQ` are needed, unlike the normal case which genuinely requires `ℂ`).

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/SelfAdjointOperator.lean`, the
Hermitian analogue of the normal spectral theorem
`LinearMap.isStarNormal_iff_exists_orthonormalBasis` (Theorem 2.1):

* `IsSelfAdjoint.exists_orthonormalBasis_forall_apply_eq_real_smul` — the forward direction: a
  self-adjoint operator `T` on a finite-dimensional inner product space over `𝕜` (`RCLike 𝕜`) has
  an orthonormal basis `b` and **real** eigenvalues `μ : _ → ℝ` with `T (b i) = (μ i : 𝕜) • b i`
  for all `i`.
* `LinearMap.isSelfAdjoint_of_forall_apply_eq_real_smul` — the converse: an operator diagonal in an
  orthonormal basis with real eigenvalues is self-adjoint. (Reality is essential: with complex
  eigenvalues the operator is merely normal.)
* `LinearMap.isSelfAdjoint_iff_exists_orthonormalBasis_real` — the theorem itself, as an
  equivalence between self-adjointness and the existence of an orthonormal eigenbasis with real
  eigenvalues.

## N&C ↦ Mathlib dictionary and fidelity

* N&C's Hermitian operator `M` is `IsSelfAdjoint T` for `T : E →ₗ[𝕜] E`, which for a linear
  endomorphism unfolds to `Tᴴ = T` (`LinearMap.star_eq_adjoint`). N&C's finite-dimensional complex
  space is the instance `𝕜 = ℂ`; stating the result over any `RCLike 𝕜` is a faithful
  generalisation, not a weakening — it is exactly the simplification the exercise invites, since
  the self-adjoint spectral theorem (unlike the normal one) needs no algebraic closure.
* "Diagonal with respect to some orthonormal basis" is the existence of an `OrthonormalBasis` `b`
  with `T (b i) = (μ i : 𝕜) • b i`; the outer-product form `M = ∑ᵢ λᵢ |i⟩⟨i|` of Box 2.2 is the
  same statement read through `b`.
* The eigenvalues `λᵢ` being real is captured by the index family living in `ℝ`
  (`μ : _ → ℝ`), coerced into `𝕜` via `RCLike.ofReal`. The forward direction inherits this from
  Mathlib's `LinearMap.IsSymmetric.eigenvalues : _ → ℝ`; the converse imposes it as a hypothesis,
  faithfully mirroring N&C's converse ("diagonalizable ⇒ normal") sharpened to the Hermitian case.
-/
