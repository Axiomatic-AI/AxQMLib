/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.PositiveHermitian

/-!
# Nielsen & Chuang, Exercise 2.24 (Hermiticity of positive operators)

Show a positive operator is necessarily Hermitian.

N&C define (p. 71) a **positive** operator `A` to be one such that for every vector `|v⟩` the number
`(|v⟩, A|v⟩) = ⟪v, A v⟫` is *real and non-negative*. The exercise asks to show such an `A` is
**Hermitian** (self-adjoint), `A† = A`. The hint's decomposition `A = B + iC` with `B = (A+A†)/2`,
`C = (A-A†)/(2i)` Hermitian gives `⟪v, Av⟫ = ⟪v, Bv⟫ + i⟪v, Cv⟫` with both `⟪v, Bv⟫, ⟪v, Cv⟫` real;
reality of `⟪v, Av⟫` for all `v` forces `⟪v, Cv⟫ = 0` for all `v`, hence `C = 0` and `A = B` is
Hermitian. Formally this is the standard fact that, **over `ℂ`**, an operator whose quadratic form
`⟪T x, x⟫` is real for all `x` is symmetric — a genuinely complex phenomenon (it fails over `ℝ`),
proved via the complex polarization identity.

The statement is pure operator theory on a complex inner product space: "positive operator" is a
condition on `⟪T x, x⟫` (real & non-negative) and "Hermitian" is `LinearMap.IsSymmetric` /
`IsSelfAdjoint`.

Compare Exercises 2.17 and 2.18.

## The formalisation

In `ToMathlib/Analysis/InnerProductSpace/PositiveHermitian.lean`:

* `LinearMap.isSymmetric_of_forall_inner_map_self_nonneg` — the direct form of the exercise: for
  `T : E →ₗ[ℂ] E` on a complex inner product space, if `0 ≤ ⟪T x, x⟫` for every `x` then `T` is
  symmetric (Hermitian).
* `LinearMap.isSelfAdjoint_of_forall_inner_map_self_nonneg` — the finite-dimensional consequence
  `IsSelfAdjoint T` (`T† = T`), matching N&C's `d`-dimensional operators.

These are thin, non-circular corollaries of the pre-existing complex characterization
`LinearMap.isSymmetric_iff_inner_map_self_real` (in
`Mathlib/Analysis/InnerProductSpace/Symmetric.lean`: `T.IsSymmetric ↔ ∀ v, ⟪T v, v⟫` is real), which
is itself proved from the symmetry-free complex
polarization identity `inner_map_polarization`.

## N&C ↦ Mathlib dictionary and fidelity

* **Positive operator** — N&C's "for all `|v⟩`, `(|v⟩, A|v⟩)` is a real, non-negative number" is
  `∀ x, 0 ≤ ⟪T x, x⟫` in the star-ordered field `ℂ`: `0 ≤ (z : ℂ)` unfolds to `0 ≤ z.re ∧ z.im = 0`,
  i.e. exactly "real and non-negative". (N&C's slot `⟪v, A v⟫` is the complex conjugate of the
  Mathlib-convention slot `⟪T x, x⟫`, so the condition is identical either way.)
* **Hermitian** — `LinearMap.IsSymmetric T` (`∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`), the coordinate-free form
  of `A† = A`; in finite dimensions this is `IsSelfAdjoint T` via
  `LinearMap.isSymmetric_iff_isSelfAdjoint`.

The formalisation is faithful, not weakened: the hypothesis is exactly N&C-positivity and does
**not** assume symmetry — deriving symmetry *is* the exercise. This is deliberately distinct from
Mathlib's
`LinearMap.IsPositive`, whose definition (following Bourbaki) already bundles `IsSymmetric`; using
it as the hypothesis would make "positive ⟹ Hermitian" circular. Only the reality half of
positivity is needed for the Hermiticity conclusion (non-negativity is retained solely to state
N&C's definition verbatim), and the result is fixed to `ℂ`, matching N&C's complex Hilbert space,
over an arbitrary complex inner product space with no dimension fixed.
-/
