/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.CStarAlgebra.Matrix
public import ToMathlib.Analysis.InnerProductSpace.Positive

/-!
# Positivity, trace, and continuity of `Matrix.toEuclideanCLM`

`Matrix.toEuclideanCLM` is the `⋆`-algebra equivalence sending a square matrix `A : Matrix n n 𝕜`
to the continuous linear endomorphism of `EuclideanSpace 𝕜 n` it represents in the standard
orthonormal basis. This file records several of its properties:

* `Matrix.isPositive_toEuclideanCLM_iff` — `Matrix.toEuclideanCLM A` is a positive operator iff `A`
  is positive semidefinite (the continuous-linear-map counterpart of the existing
  `Matrix.isPositive_toEuclideanLin_iff`);
* `Matrix.trace_toEuclideanCLM` — the operator trace of `Matrix.toEuclideanCLM A` equals the matrix
  trace `A.trace`.
* `Matrix.toEuclideanCLM_vecMulVec` — `Matrix.toEuclideanCLM (vecMulVec x (star y))` is the rank-one
  operator `|x⟩⟨y|` (`InnerProductSpace.rankOne`); the continuous-linear-map counterpart of the
  `Matrix.toEuclideanLin` identity `InnerProductSpace.symm_toEuclideanLin_rankOne`.
* `Matrix.continuous_toEuclideanCLM` — `Matrix.toEuclideanCLM` is continuous (as a map from
  `Matrix n n 𝕜` with the product topology to the operators with the operator-norm topology).

The first three (positivity, trace, outer product) are immediate from the coercion
`Matrix.coe_toEuclideanCLM_eq_toEuclideanLin` to `Matrix.toEuclideanLin`, together with the
corresponding facts for `toEuclideanLin` (`Matrix.isPositive_toEuclideanLin_iff` for positivity;
`Matrix.toEuclideanLin_eq_toLin_orthonormal` and `Matrix.trace_toLin_eq` for the trace;
`InnerProductSpace.symm_toEuclideanLin_rankOne` for the outer product). Continuity holds because a
`𝕜`-linear map out of a finite-dimensional space over a complete field is continuous
(`LinearMap.continuous_of_finiteDimensional`).
-/

open scoped InnerProductSpace ComplexOrder

@[expose] public section

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **`Matrix.toEuclideanCLM A` is positive iff `A` is positive semidefinite.** The
continuous-linear-map counterpart of `Matrix.isPositive_toEuclideanLin_iff`: positivity of the
operator `A` represents on `EuclideanSpace 𝕜 n` is exactly positive semidefiniteness of `A`. -/
theorem isPositive_toEuclideanCLM_iff (A : Matrix n n 𝕜) :
    (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := n) A).IsPositive ↔ A.PosSemidef := by
  rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, coe_toEuclideanCLM_eq_toEuclideanLin,
    isPositive_toEuclideanLin_iff]

/-- **The operator trace of `Matrix.toEuclideanCLM A` is the matrix trace `A.trace`.** The operator
`Matrix.toEuclideanCLM A` is `A` in the standard orthonormal basis, so its
basis-independent trace agrees with `A.trace`. -/
theorem trace_toEuclideanCLM (A : Matrix n n 𝕜) :
    LinearMap.trace 𝕜 (EuclideanSpace 𝕜 n) ↑(Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := n) A)
      = A.trace := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_eq_toLin_orthonormal, trace_toLin_eq]

/-- **`Matrix.toEuclideanCLM` of an outer product is the rank-one operator.**
`Matrix.toEuclideanCLM (vecMulVec x (star y)) = |x⟩⟨y|` (`InnerProductSpace.rankOne 𝕜 x y`), for
`x y : EuclideanSpace 𝕜 n`. The continuous-linear-map counterpart of the `Matrix.toEuclideanLin`
identity `InnerProductSpace.symm_toEuclideanLin_rankOne`
(`toEuclideanLin.symm (rankOne 𝕜 x y) = vecMulVec x (star y)`), transported across the coercion
`Matrix.coe_toEuclideanCLM_eq_toEuclideanLin`. -/
theorem toEuclideanCLM_vecMulVec (x y : EuclideanSpace 𝕜 n) :
    Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := n) (Matrix.vecMulVec x.ofLp (star y.ofLp))
      = InnerProductSpace.rankOne 𝕜 x y := by
  apply ContinuousLinearMap.coe_injective
  rw [coe_toEuclideanCLM_eq_toEuclideanLin, ← InnerProductSpace.symm_toEuclideanLin_rankOne,
    LinearEquiv.apply_symm_apply]

/-- **`Matrix.toEuclideanCLM` is continuous.** The `⋆`-algebra isomorphism
`Matrix.toEuclideanCLM : Matrix n n 𝕜 ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)` is a
`𝕜`-linear map between finite-dimensional spaces — the domain `Matrix n n 𝕜` carries the product
topology, the codomain the operator-norm topology — so it is continuous by
`LinearMap.continuous_of_finiteDimensional`, viewing it as a `LinearMap` through its
`⋆`-algebra → algebra → linear-map coercion `toAlgEquiv.toLinearMap`. -/
theorem continuous_toEuclideanCLM :
    Continuous (fun M : Matrix n n 𝕜 => Matrix.toEuclideanCLM (𝕜 := 𝕜) M) :=
  LinearMap.continuous_of_finiteDimensional
    (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := n)).toAlgEquiv.toLinearMap

end Matrix
