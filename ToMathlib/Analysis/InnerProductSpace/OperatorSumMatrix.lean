/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSum
public import ToMathlib.Analysis.CStarAlgebra.Matrix

/-!
# The Kraus (operator-sum) map of a matrix family under `Matrix.toEuclideanCLM`

The `⋆`-algebra isomorphism `Matrix.toEuclideanCLM : Matrix n n ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ n →L[ℂ]
EuclideanSpace ℂ n)` intertwines the **operator-sum (Kraus) map** `krausSumₗ` of a family of
operators with the **matrix conjugation sum** `B ↦ ∑ₖ Aₖ B Aₖ†`: transporting a matrix family
`A : ι → Matrix n n ℂ` to operators and forming its Kraus map is the same as forming the matrix
conjugation sum and then transporting.

* `ContinuousLinearMap.krausSumₗ_toEuclideanCLM` —
  `krausSumₗ (toEuclideanCLM ∘ A) (toEuclideanCLM B) = toEuclideanCLM (∑ₖ Aₖ B Aₖ†)`.

This is the bridge that lets one compute a matrix operator-sum (e.g. a random-unitary / Kraus qubit
channel, or the Bloch-sphere action of a unital channel) entirely at the concrete matrix level, and
transport the result across `toEuclideanCLM` — the two `⋆`-algebra facts `map_mul` and `map_star`
(adjoint `↔` conjugate transpose) doing all the work.
-/

@[expose] public section

open scoped Matrix

namespace ContinuousLinearMap

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-- **The Kraus map of a matrix family, transported through `Matrix.toEuclideanCLM`, is the matrix
conjugation sum.** For a finite family of matrices `A : ι → Matrix n n ℂ` and a matrix `B`, the
operator-sum map of the transported family `k ↦ toEuclideanCLM (Aₖ)` applied to `toEuclideanCLM B`
equals `toEuclideanCLM (∑ₖ Aₖ B Aₖ†)`. Each summand `Eₖ (toEuclideanCLM B) Eₖ†` with
`Eₖ = toEuclideanCLM Aₖ` becomes `toEuclideanCLM (Aₖ B Aₖ†)` via the `⋆`-algebra structure
(`map_mul`; the adjoint `Eₖ†` is `toEuclideanCLM (Aₖᴴ)` by `map_star` and `star_eq_adjoint`). -/
theorem krausSumₗ_toEuclideanCLM (A : ι → Matrix n n ℂ) (B : Matrix n n ℂ) :
    krausSumₗ (fun k => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) (A k))
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) B)
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) (∑ k, A k * B * (A k)ᴴ) := by
  rw [krausSumₗ_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, ← Matrix.star_eq_conjTranspose, map_star, star_eq_adjoint,
    ← mul_def, ← mul_def]
  exact (mul_assoc _ _ _).symm

end ContinuousLinearMap
