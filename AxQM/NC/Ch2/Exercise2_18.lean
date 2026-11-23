/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.UnitaryEigenvalue

/-!
# Nielsen & Chuang, Exercise 2.18 (Eigenvalues of a unitary matrix have modulus 1)

Show all eigenvalues of a unitary matrix have modulus 1.

A **unitary** operator `U` satisfies `U†U = UU† = I`; equivalently it preserves inner products and
hence norms, `‖U|v⟩‖ = ‖|v⟩‖` (N&C p. 71). If `U|v⟩ = λ|v⟩` for an eigenvector `|v⟩ ≠ 0`, then
`‖|v⟩‖ = ‖U|v⟩‖ = ‖λ|v⟩‖ = |λ| · ‖|v⟩‖`, so `|λ| = 1`: the eigenvalue lies on the unit circle,
`λ = e^{iθ}`.

Compare the adjoint exercises 2.13, 2.14 and 2.15.

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/UnitaryEigenvalue.lean`:

* `Module.End.HasEigenvalue.norm_eq_one_of_mem_unitary` — the direct form of the exercise: for
  `U ∈ unitary (H →L[𝕜] H)` on a Hilbert space `H` over `𝕜` (`RCLike 𝕜`), if
  `Module.End.HasEigenvalue (U : H →ₗ[𝕜] H) μ` then `‖μ‖ = 1`.
* `Module.End.HasEigenvalue.norm_eq_one_of_norm_map` — the core it is built from: any
  eigenvalue of a *norm-preserving* linear endomorphism of a normed space has modulus one. This
  isolates the only property actually used (isometry), so the unitary case is a one-line
  specialization.

## N&C ↦ Mathlib dictionary and fidelity

* `U` is N&C's unitary matrix; here it is a unitary operator `U ∈ unitary (H →L[𝕜] H)` on a Hilbert
  space `H` over `𝕜` (`RCLike 𝕜`, i.e. `ℝ` or `ℂ`; N&C's `ℂ` is the special case). N&C's
  *unitary matrix* on `ℂⁿ` is the finite-dimensional instance `H = EuclideanSpace 𝕜 (Fin n)`, where
  finite dimensionality supplies the completeness Mathlib requires. This is a faithful
  generalisation, not a weakening — no dimension is fixed and no hypothesis beyond unitarity is
  added.
* An **eigenvalue** `λ` with eigenvector `|v⟩ ≠ 0` and `U|v⟩ = λ|v⟩` is `Module.End.HasEigenvalue`
  (`Module.End.mem_eigenspace_iff`: `x ∈ eigenspace f μ ↔ f x = μ • x`, with the nonzero
  eigenvector supplied by `Module.End.HasEigenvalue.exists_hasEigenvector`). The unitary operator is
  coerced to a `Module.End 𝕜 H = H →ₗ[𝕜] H` via `ContinuousLinearMap.coe_coe`.
* **Modulus** `|λ|` is the field norm `‖μ‖` on `𝕜`; "modulus 1" is `‖μ‖ = 1`. The `e^{iθ}` form N&C
  mentions is the equivalent polar description of a complex number of modulus one and carries no
  extra content, so `‖μ‖ = 1` is the faithful statement.
* **Norm preservation** `‖U|v⟩‖ = ‖|v⟩‖` — the crux of the elementary argument — is Mathlib's
  `ContinuousLinearMap.norm_map_of_mem_unitary`. The proof cancels `‖v‖ ≠ 0` from
  `‖μ‖ · ‖v‖ = ‖v‖`.

Mathlib already contains the C\*-algebraic spectral form `spectrum.norm_eq_one_of_unitary` (the
*spectrum* of a unitary element lies on the unit circle). These declarations are the
complementary *eigenvalue* (`Module.End.HasEigenvalue`) idiom N&C's exercise is phrased in, proved
directly from norm preservation rather than through the continuous functional calculus — so the
elementary content of the exercise is captured, not merely its spectral restatement.
-/
