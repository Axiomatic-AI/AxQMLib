/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.PolarNormal

/-!
# Nielsen & Chuang, Exercise 2.49 (polar decomposition of a normal matrix in outer-product form)

Express the polar decomposition of a normal matrix in outer product form.

For a normal operator `A`, the spectral theorem (N&C Theorem 2.1) writes it diagonally in an
orthonormal eigenbasis `{bᵢ}` as `A = ∑ᵢ μᵢ |bᵢ⟩⟨bᵢ|`. Splitting each eigenvalue into modulus and
phase, `μᵢ = ‖μᵢ‖ · phase(μᵢ)`, the polar decomposition (N&C Theorem 2.3) `A = U J = J U` of such
an `A` is exhibited in the *same* eigenbasis:

* the positive factor is `J = |A| = ∑ᵢ ‖μᵢ‖ |bᵢ⟩⟨bᵢ|`;
* the unitary factor is `U = ∑ᵢ phase(μᵢ) |bᵢ⟩⟨bᵢ|`.

Because `J` and `U` share `A`'s eigenbasis they commute, so the left (`A = UJ`) and right (`A = JU`)
polar decompositions coincide — the distinguishing feature of the normal case.

These are statements about operators on a (finite-dimensional, complex) inner product space: the
spectral and polar decompositions.

Compare Exercise 2.48 and Theorems 2.1 (spectral decomposition) and 2.3 (polar decomposition).

## The declarations

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/PolarNormal.lean`.

The **outer-product diagonal operator** and its algebra :

* `OrthonormalBasis.diagonalOperator b w = ∑ᵢ wᵢ • |bᵢ⟩⟨bᵢ|` — the operator diagonal in an
  orthonormal basis `b` with diagonal entries `w`;
* `OrthonormalBasis.diagonalOperator_comp` (`diag w ∘L diag w' = diag (w * w')`),
  `diagonalOperator_adjoint` (`(diag w)† = diag (star w)`), `diagonalOperator_one` (`diag 1 = 1`),
  `diagonalOperator_mem_unitary` (unitary when `‖wᵢ‖ = 1`),
  `diagonalOperator_isPositive_of_nonneg` (positive when `0 ≤ wᵢ`),
  `diagonalOperator_isStarNormal` (every `diag w` is normal — the converse spectral fact);
* `RCLike.phase` — the unit-modulus part `phase z = z/‖z‖` (`phase 0 = 1`), with
  `RCLike.norm_phase` (`‖phase z‖ = 1`) and `RCLike.phase_mul_norm` / `norm_mul_phase`
  (`z = ‖z‖ · phase z`).

The **polar decomposition of `A = b.diagonalOperator μ`** (the exercise proper):

* `OrthonormalBasis.diagonalOperator_eq_phase_comp_norm` — `A = U ∘L J` (left);
* `OrthonormalBasis.diagonalOperator_eq_norm_comp_phase` — `A = J ∘L U` (right);
* `OrthonormalBasis.diagonalOperator_phase_mem_unitary` — `U` is unitary;
* `OrthonormalBasis.diagonalOperator_norm_isPositive` — `J` is positive;
* `OrthonormalBasis.diagonalOperator_norm_eq_absoluteValue` — `J = |A| = √(A† A)`, identifying the
  outer-product positive factor with the canonical `|A|` of N&C Theorem 2.3.

The statement tying it to an arbitrary normal operator:

* `IsStarNormal.exists_eq_diagonalOperator` — every normal `A : E →L[ℂ] E` equals
  `b.diagonalOperator μ` for an orthonormal eigenbasis `b` and eigenvalues `μ` (the forward
  spectral theorem in outer-product form), so the polar decomposition above applies to any normal
  operator;
* `ContinuousLinearMap.isStarNormal_toLinearMap` — the supporting bridge: normality transfers
  from a continuous linear map to its underlying `E →ₗ[𝕜] E` coercion (over any `RCLike 𝕜`),
  connecting the `→L` polar API to the `→ₗ`-stated normal spectral theorem.
-/
