/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Additional facts about Gram matrices

Congruence of the Gram matrix under a linear recombination of the family, and a bound on its
rank by the dimension of the ambient space.
-/

open RCLike Real Matrix

open scoped InnerProductSpace ComplexOrder ComplexConjugate

@[expose] public section

variable {E n α 𝕜 : Type*}

namespace Matrix

variable [RCLike 𝕜]

section SemiInnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The Gram matrix transforms by congruence under a linear recombination of the family.** If a
new family `wⱼ = ∑ᵢ Mᵢⱼ • vᵢ` is formed by recombining `v : n → E` with the columns of a matrix
`M : Matrix n m 𝕜`, its Gram matrix is `Mᴴ * gram 𝕜 v * M`. Immediate from the sesquilinearity of
the inner product; the `Mᴴ` on the left carries the conjugate coming from the first slot. -/
theorem gram_smul_sum [Fintype n] {m : Type*} (M : Matrix n m 𝕜) (v : n → E) :
    gram 𝕜 (fun j => ∑ i, M i j • v i) = Mᴴ * gram 𝕜 v * M := by
  ext j k
  simp only [gram_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end SemiInnerProductSpace

section NormedInnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Finite n]

omit [Finite n] in
/-- **The rank of a Gram matrix is at most the dimension of the ambient space.** For a finite family
`v : n → E` in a finite-dimensional inner product space `E`, `rank (gram 𝕜 v) ≤ dim E`.

Writing `gram 𝕜 v = mᴴ * m` for the coordinate matrix `m` of `v` in an orthonormal basis
(`gram_eq_conjTranspose_mul`), `rank (mᴴ * m) ≤ rank m` (`rank_mul_le_right`), and `rank m` is at
most its number of rows, `dim E`. -/
theorem rank_gram_le [FiniteDimensional 𝕜 E] [Finite n] (v : n → E) :
    (gram 𝕜 v).rank ≤ Module.finrank 𝕜 E := by
  classical
  cases nonempty_fintype n
  let b := stdOrthonormalBasis 𝕜 E
  rw [gram_eq_conjTranspose_mul b v]
  refine (rank_mul_le_right _ _).trans ?_
  refine (rank_le_card_height _).trans_eq ?_
  exact (Module.finrank_eq_card_basis b.toBasis).symm

end NormedInnerProductSpace

end Matrix
