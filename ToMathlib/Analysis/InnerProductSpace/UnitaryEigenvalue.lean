/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenvalues of a unitary operator have modulus one

Let `H` be a complex (or, more generally, `RCLike`) Hilbert space. This file records that every
eigenvalue of a unitary operator on `H` has modulus one — Nielsen & Chuang, Exercise 2.18.

The argument is entirely elementary and rests on a single geometric fact: a unitary operator is an
isometry, `‖U x‖ = ‖x‖`. If `U x = μ • x` for a nonzero eigenvector `x`, then
`‖x‖ = ‖U x‖ = ‖μ • x‖ = ‖μ‖ * ‖x‖`, and cancelling `‖x‖ ≠ 0` gives `‖μ‖ = 1`. Only norm
preservation is used, so the core lemma is stated for an arbitrary norm-preserving endomorphism of a
normed space and the unitary case is a specialization via
`ContinuousLinearMap.norm_map_of_mem_unitary`.

## Main results

* `Module.End.HasEigenvalue.norm_eq_one_of_norm_map`: any eigenvalue of a norm-preserving linear
  endomorphism of a normed space has modulus one — the reusable core.
* `Module.End.HasEigenvalue.norm_eq_one_of_mem_unitary`: any eigenvalue of a unitary operator
  `U ∈ unitary (H →L[𝕜] H)` on a Hilbert space has modulus one — the direct form of the exercise.

Mathlib already contains the C\*-algebraic spectral form `spectrum.norm_eq_one_of_unitary`
(the *spectrum* of a unitary element lies on the unit circle). The results here are the
complementary *eigenvalue* (`Module.End.HasEigenvalue`) idiom, obtained directly from norm
preservation rather than through the continuous functional calculus, and requiring no completeness
for the general core.
-/

@[expose] public section

namespace Module.End

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **An eigenvalue of a norm-preserving endomorphism has modulus one.** If a linear endomorphism
`T` of a normed space preserves norms (`‖T x‖ = ‖x‖` for all `x`, i.e. `T` is a linear isometry),
then every eigenvalue `μ` of `T` satisfies `‖μ‖ = 1`.

This is the reusable core behind Nielsen & Chuang's Exercise 2.18: for an eigenvector `x ≠ 0` with
`T x = μ • x`, norm preservation gives `‖μ‖ * ‖x‖ = ‖T x‖ = ‖x‖`, and cancelling `‖x‖ ≠ 0` yields
the claim. -/
theorem HasEigenvalue.norm_eq_one_of_norm_map {T : Module.End 𝕜 E} (hT : ∀ x, ‖T x‖ = ‖x‖) {μ : 𝕜}
    (hμ : T.HasEigenvalue μ) : ‖μ‖ = 1 := by
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hx0 : x ≠ 0 := (hasEigenvector_iff.mp hx).2
  refine mul_right_cancel₀ (norm_ne_zero_iff.mpr hx0) ?_
  rw [one_mul, ← norm_smul, ← hx.apply_eq_smul, hT]

/-- **Nielsen & Chuang, Exercise 2.18.** Every eigenvalue of a unitary operator on a Hilbert space
has modulus one: if `U ∈ unitary (H →L[𝕜] H)` and `μ` is an eigenvalue of `U`, then `‖μ‖ = 1`.

A unitary operator is an isometry (`ContinuousLinearMap.norm_map_of_mem_unitary`), so this is the
specialization of `Module.End.HasEigenvalue.norm_eq_one_of_norm_map` to `U`. N&C's *unitary matrix*
is the finite-dimensional instance `H = EuclideanSpace 𝕜 (Fin n)`. -/
theorem HasEigenvalue.norm_eq_one_of_mem_unitary {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] {U : H →L[𝕜] H} {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (U : H →ₗ[𝕜] H) μ) (hU : U ∈ unitary (H →L[𝕜] H)) : ‖μ‖ = 1 :=
  hμ.norm_eq_one_of_norm_map fun x => U.norm_map_of_mem_unitary hU x

end Module.End
