/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# `Matrix.toEuclideanCLM` intertwines conjugate transpose with the operator adjoint
-/

@[expose] public section

open scoped Matrix

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜]
variable [Fintype n] [DecidableEq n]

/-- `Matrix.toEuclideanCLM` intertwines conjugate transpose with the operator adjoint:
`toEuclideanCLM Aᴴ = (toEuclideanCLM A)†`. The continuous-linear-map (`⋆`-algebra-equivalence)
analogue of `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`, using that `toEuclideanCLM` is a
`⋆`-isomorphism (`map_star`), the star on operators is the adjoint
(`ContinuousLinearMap.star_eq_adjoint`), and `star A = Aᴴ` on matrices
(`Matrix.star_eq_conjTranspose`). -/
lemma toEuclideanCLM_conjTranspose_eq_adjoint (A : Matrix n n 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) Aᴴ
      = ContinuousLinearMap.adjoint (toEuclideanCLM (n := n) (𝕜 := 𝕜) A) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, Matrix.star_eq_conjTranspose]

end Matrix
