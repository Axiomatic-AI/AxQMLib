/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.UnitaryExtension

/-!
# Nielsen & Chuang, Exercise 2.67 (unitary extension of an isometry on a subspace)

Prove an inner-product-preserving U on subspace W extends to a unitary on V.

The statement is linear algebra: an inner-product-preserving linear map from a subspace of a
finite-dimensional inner product space extends to a unitary of the whole space.

N&C's "Hilbert space `V`" is a finite-dimensional inner product space (the extension argument is
the finite-dimensional dimension count: the isometry `U` has an equidimensional image, so the
orthogonal complements of `W` and of `range U` have equal dimension and any isometry between them
completes `U` to a unitary). The formalisation is over an `RCLike` field `𝕜`, a faithful
generalisation covering N&C's `𝕜 = ℂ` case; a "unitary operator on `V`" is a linear isometry
equivalence `V ≃ₗᵢ[𝕜] V`. N&C's hypothesis `⟨w₁|U†U|w₂⟩ = ⟨w₁|w₂⟩` is exactly
`⟪U w₁, U w₂⟫ = ⟪w₁, w₂⟫` (that `U` preserves inner products).

## The declarations

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/UnitaryExtension.lean`:

* `LinearMap.unitaryExtend` — the unitary extension `V ≃ₗᵢ[𝕜] V` of an inner-product-preserving
  `U : W →ₗ[𝕜] V`.
* `LinearMap.unitaryExtend_apply` — the extension agrees with `U` on `W`
  (`U.unitaryExtend hU w = U w`), i.e. `U'` genuinely extends `U`.
* `LinearMap.exists_unitaryExtend` — the existence statement of Exercise 2.67:
  there is a unitary `U' : V ≃ₗᵢ[𝕜] V` with `U' w = U w` for every `w ∈ W`.

The construction reuses Mathlib's `LinearMap.isometryOfInner` (inner-product-preserving linear map
⇒ `LinearIsometry`), `LinearIsometry.extend` (extend an isometry of a subspace to the whole
finite-dimensional space), and `LinearIsometry.toLinearIsometryEquiv` (a linear isometry between
equidimensional finite-dimensional spaces is an equivalence).
-/
