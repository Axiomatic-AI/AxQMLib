/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# A positive operator on a complex inner product space is Hermitian

Let `E` be a complex inner product space. An operator `T : E →ₗ[ℂ] E` is *positive* in the sense of
Nielsen & Chuang (Exercise 2.24) when the quadratic form `⟪T x, x⟫` is a real, non-negative number
for every `x`. Over `ℂ` these two requirements are captured at once by a single order relation
in the star-ordered field `ℂ`: `0 ≤ ⟪T x, x⟫` unfolds (`Complex.le_def`) to `0 ≤ (⟪T x, x⟫).re`
with `(⟪T x, x⟫).im = 0`. This file records that such a `T` is automatically symmetric (Hermitian),
and, in the finite-dimensional setting N&C works in, self-adjoint (`T† = T`).

Crucially the hypothesis does **not** presuppose symmetry: that `⟪T x, x⟫` is real for all `x`
already forces `⟪T x, y⟫ = ⟪x, T y⟫`. This is the whole content of the exercise, and it is
genuinely a feature of the complex field (it fails over `ℝ`, where a non-symmetric operator can
still have a real, non-negative quadratic form). By contrast, Mathlib's `LinearMap.IsPositive`
bakes symmetry into its definition (following Bourbaki), so `LinearMap.IsPositive.isSelfAdjoint`
does *not* by itself express Exercise 2.24; the substance is that the bare quadratic-form
condition below implies symmetry.

## Main results

* `LinearMap.isSymmetric_of_forall_inner_map_self_nonneg`: for `T : E →ₗ[ℂ] E`, if `0 ≤ ⟪T x, x⟫`
  for every `x`, then `T` is symmetric. This is Nielsen & Chuang, Exercise 2.24.
* `LinearMap.isSelfAdjoint_of_forall_inner_map_self_nonneg`: the finite-dimensional consequence,
  `IsSelfAdjoint T` (i.e. `T† = T`), matching N&C's `d`-dimensional operators.

## Implementation notes

Only reality of the quadratic form is used for symmetry; non-negativity is carried along solely to
match N&C's definition of *positive* and is discharged for free from `0 ≤ ⟪T x, x⟫`. The proof is a
one-line specialization of `LinearMap.isSymmetric_iff_inner_map_self_real` (symmetry of a complex
operator is equivalent to reality of its quadratic form, proved there via the complex polarization
identity `inner_map_polarization`). The slot `⟪T x, x⟫` is Mathlib's positivity convention; N&C's
`⟪x, T x⟫ = (starRingEnd ℂ) ⟪T x, x⟫` is its complex conjugate, so the "real and non-negative"
condition is identical in either slot.
-/

@[expose] public section

open scoped ComplexOrder

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Nielsen & Chuang, Exercise 2.24 (Hermiticity of positive operators).** A positive operator
on a complex inner product space is symmetric (Hermitian). Positivity here is N&C's definition: the
quadratic form `⟪T x, x⟫` is a real, non-negative number for every `x`, encoded by the single
order relation `0 ≤ ⟪T x, x⟫` in the star-ordered field `ℂ`.

The hypothesis does not assume symmetry: reality of `⟪T x, x⟫` for all `x` alone forces
`⟪T x, y⟫ = ⟪x, T y⟫`, via the complex polarization identity (see
`LinearMap.isSymmetric_iff_inner_map_self_real`). Non-negativity plays no role in the conclusion. -/
theorem isSymmetric_of_forall_inner_map_self_nonneg {T : E →ₗ[ℂ] E}
    (h : ∀ x, 0 ≤ inner ℂ (T x) x) : T.IsSymmetric := by
  rw [isSymmetric_iff_inner_map_self_real]
  intro v
  exact Complex.conj_eq_iff_im.mpr (Complex.le_def.mp (h v)).2.symm

/-- **Nielsen & Chuang, Exercise 2.24**, self-adjoint form. In the finite-dimensional setting N&C
works in, a positive operator `T` on a complex inner product space is self-adjoint, `T† = T`
(`IsSelfAdjoint T`). This upgrades `LinearMap.isSymmetric_of_forall_inner_map_self_nonneg` through
`LinearMap.isSymmetric_iff_isSelfAdjoint`. -/
theorem isSelfAdjoint_of_forall_inner_map_self_nonneg [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E}
    (h : ∀ x, 0 ≤ inner ℂ (T x) x) : IsSelfAdjoint T :=
  (isSymmetric_iff_isSelfAdjoint _).mp (isSymmetric_of_forall_inner_map_self_nonneg h)

end LinearMap
