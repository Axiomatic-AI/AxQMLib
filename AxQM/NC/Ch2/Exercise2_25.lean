/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.Positive

/-!
# Nielsen & Chuang, Exercise 2.25 (Positivity of `A†A`)

Show that for any operator A, A^dagger A is positive.

N&C (p. 71) define a **positive operator** `A` to be one such that for every vector `|v⟩` the
number `(|v⟩, A|v⟩) = ⟪v, A v⟫` is *real and non-negative*. The exercise is the standard one-line
fact: for any operator `A`, `⟪v, A†A v⟫ = ⟪A v, A v⟫ = ‖A v‖² ≥ 0`, so `A†A` is positive (and,
since the quadratic form is real for every `v`, automatically Hermitian — the content of
Exercise 2.24 — as N&C's definition of positivity requires).

N&C's "positive operator" is Mathlib's `LinearMap.IsPositive` / `ContinuousLinearMap.IsPositive`,
"`A†`" is the Hilbert-space adjoint, and "`A†A`" is the composite `adjoint A ∘ A`.

Compare Exercises 2.17 and 2.22. Unlike those, this fact was already present in Mathlib, so this
exercise adds no new declaration; it records where the existing statements are.

## The declarations

The exercise follows from existing Mathlib statements. All three are in Mathlib (imported here via
`Mathlib.Analysis.InnerProductSpace.Positive`, which carries the first two):

* `LinearMap.isPositive_adjoint_comp_self` — the finite-dimensional operator form, matching N&C's
  setting most closely: for `S : E →ₗ[𝕜] F` between finite-dimensional inner product spaces over
  `𝕜` (`RCLike 𝕜`), `(LinearMap.adjoint S ∘ₗ S).IsPositive`.
* `ContinuousLinearMap.isPositive_adjoint_comp_self` — the bounded-operator generalisation to
  Hilbert spaces: for `S : E →L[𝕜] F` with `E`, `F` complete,
  `((ContinuousLinearMap.adjoint S).comp S).IsPositive`.
* `Matrix.posSemidef_conjTranspose_mul_self` (in `Mathlib.LinearAlgebra.Matrix.PosDef`) — the
  matrix incarnation: for `A : Matrix m n R` over a `StarOrderedRing`, `(Aᴴ * A).PosSemidef`.

## N&C ↦ Mathlib dictionary and fidelity

* **Positive operator.** N&C's "`(|v⟩, A|v⟩)` is real and non-negative for all `|v⟩`" is
  `LinearMap.IsPositive T`, definitionally `T.IsSymmetric ∧ ∀ x, 0 ≤ RCLike.re ⟪T x, x⟫`
  (`ContinuousLinearMap.IsPositive` is the same predicate for a bounded operator). Over `ℂ` the
  requirement that `⟪v, A v⟫` be *real* for every `v` already forces `A` self-adjoint (Ex. 2.24),
  so bundling `IsSymmetric` into the predicate is exactly N&C's notion, not a strengthening; the
  conclusion `(A†A).IsPositive` faithfully asserts both halves N&C intends.
* **Argument-order convention.** Mathlib's condition is on `⟪T x, x⟫` (operator in the first
  slot), N&C's on `(|v⟩, A|v⟩) = ⟪v, A v⟫` (operator in the second). For a symmetric operator the
  two are complex conjugates with the same, real, value, so `0 ≤ re ⟪T x, x⟫ ⟺ 0 ≤ ⟪x, T x⟫`; the
  two phrasings coincide.
* **Adjoint `A†`.** `LinearMap.adjoint` / `ContinuousLinearMap.adjoint` is the Hilbert-space
  adjoint `⟪A† x, y⟫ = ⟪x, A y⟫`, N&C's `A†`; `A†A` is `adjoint S ∘ₗ S` (resp. `(adjoint S).comp
  S`).

The statements are faithful generalisations, not weakenings: they fix no dimension and, taking
the domain and codomain equal (`E = F`), specialise to N&C's endomorphism `A : V → V`, while the
general `E →ₗ[𝕜] F` / `E →L[𝕜] F` form even allows a rectangular `A`. N&C's finite-dimensional
complex Hilbert space is the instance `𝕜 = ℂ`, `E = F` finite-dimensional; the
`ContinuousLinearMap` form extends the same fact to any complex (or real) Hilbert space, and the
`Matrix` form is its concrete matrix transcription `A†A ↦ Aᴴ * A`.
-/
