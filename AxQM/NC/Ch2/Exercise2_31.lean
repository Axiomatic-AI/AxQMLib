/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.CFCTensor

/-!
# Nielsen & Chuang, Exercise 2.31 (Tensor product of two positive operators is positive)

Show the tensor product of two positive operators is positive.

A **positive** operator `A` is one for which `⟨v, A v⟩` is a real, non-negative number for every
vector `|v⟩` (N&C p. 71); over `ℂ` this reality condition already forces `A` to be self-adjoint
(N&C Exercise 2.24), so a positive operator is a self-adjoint operator with non-negative spectrum.
If `A` on `E` and `B` on `F` are positive, take their positive square roots `√A`, `√B` (which exist
by the continuous functional calculus / spectral theorem) and write
`A ⊗ B = (√A ⊗ √B)(√A ⊗ √B) = S · S` with `S = √A ⊗ √B` self-adjoint. Any `S · S` with `S`
self-adjoint is positive, since `⟨v, S·S v⟩ = ⟨S v, S v⟩ = ‖S v‖² ≥ 0`. Hence `A ⊗ B` is positive.

Compare the tensor-product exercises 2.28, 2.29 and 2.30.

## The declarations

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/CFCTensor.lean`:

* `TensorProduct.mapL_isPositive` — the direct form of the exercise: for positive operators
  `A : E →L[ℂ] E` and `B : F →L[ℂ] F` on finite-dimensional complex Hilbert spaces, the operator
  tensor product `TensorProduct.mapL A B` is positive (`ContinuousLinearMap.IsPositive`). This is
  the `IsPositive`-phrased predicate — symmetric with `0 ≤ re⟪·, ·⟫`, matching N&C's defining
  property of a positive operator — obtained from the Loewner-order form `mapL_nonneg` via the
  bridge `ContinuousLinearMap.nonneg_iff_isPositive`.
* `TensorProduct.mapL_nonneg` — the underlying content phrased in the Loewner operator order,
  `0 ≤ A → 0 ≤ B → 0 ≤ TensorProduct.mapL A B`, from which `mapL_isPositive` is a one-line
  bridge. Its proof is exactly the square-root factorisation above: `A ⊗ B = (√A ⊗ √B)²` (via
  `CFC.sqrt_mul_sqrt_self` and `mapL_mul`), and `S · S ≥ 0` for self-adjoint `S` by
  `IsSelfAdjoint.mul_self_nonneg`.

The matrix (Kronecker-product) face of the same exercise is already in Mathlib as
`Matrix.PosSemidef.kronecker` (`Mathlib/Analysis/Matrix/Order.lean`): the Kronecker product of two
positive-semidefinite matrices is positive semidefinite. In a fixed orthonormal basis N&C's tensor
product of operators is the Kronecker product of their matrices (eq. 2.50), and a positive
operator's matrix is positive semidefinite, so this states the exercise at the matrix level.

## N&C ↦ Mathlib dictionary and fidelity

* A **positive operator** `A` — `⟨v, A v⟩` real and `≥ 0` for all `|v⟩` (N&C p. 71) — is
  `ContinuousLinearMap.IsPositive A`, i.e. `A` symmetric together with `0 ≤ re ⟪A x, x⟫` for all
  `x`. Over `ℂ` the reality of `⟨v, A v⟩` for all `v` already forces symmetry (N&C Exercise 2.24),
  so the bundled symmetry is equivalent content, not an extra hypothesis — this is a faithful
  rendering, not a strengthening.
* The **tensor product of operators** `A ⊗ B` is `TensorProduct.mapL A B`, the continuous-linear
  tensor map on `E ⊗[ℂ] F`.
* N&C works with finite-dimensional complex Hilbert spaces throughout Chapter 2; the
  statement's `[FiniteDimensional ℂ E] [FiniteDimensional ℂ F]` (with completeness) hypotheses are
  exactly this setting — finite dimensionality supplies the completeness and the operator square
  roots the proof uses. No dimension is fixed and `A`, `B` may act on different spaces, so the
  statement is faithfully general, not a specialisation.
-/
