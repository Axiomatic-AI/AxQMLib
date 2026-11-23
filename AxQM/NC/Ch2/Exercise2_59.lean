/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Qubit
import AxQM.Postulates.API.Variance

/-!
# Nielsen & Chuang, Exercise 2.59

For qubit |0> measure observable X: find average value and standard deviation.

## The answer

* **Average value** `⟪X⟫ = ⟨0|X|0⟩ = 0`. Because `X|0⟩ = |1⟩` is orthogonal to `|0⟩`, the
  diagonal matrix element `⟨0|X|0⟩` (the `(0,0)` entry of `X`) vanishes.
* **Mean square** `⟪X²⟫ = ⟨0|X²|0⟩ = 1`. Since `X² = 1` (Exercise 2.52 / the Pauli involution),
  `⟨0|X²|0⟩ = ⟨0|0⟩ = 1`.
* **Standard deviation** `Δ(X) = √(⟪X²⟫ - ⟪X⟫²) = √(1 - 0²) = 1`.

This matches N&C's remark (Box 2.4, Eq. 2.109) that `Δ(X)` for the state `|0⟩` is strictly
positive — here exactly `1`.

## The formalisation

* `expectation_pauliX_qubitBasis_zero` — the average value `⟪X⟫ = 0`.
* `expectation_sq_pauliX_qubitBasis_zero` — the mean square `⟪X²⟫ = 1`.
* `stdDev_pauliX_qubitBasis_zero` — the standard deviation `Δ(X) = 1`.

The state `|0⟩` (`qubitBasis 0`), the observable `X` (`pauliXObservable`), and the involution
`X² = 1` (`pauliXObservable_op_mul_self`) are provided in
`AxQM/Postulates/API/Qubit.lean`. The generic variance / standard-deviation generators
(`PureState.variance`, `PureState.stdDev`, `Observable.sq`) live in
`AxQM/Postulates/API/Variance.lean` — the shared measurement-statistics infrastructure
introduced by Exercise 2.58, on which this item **depends**: this exercise reuses those
generators rather than re-deriving them.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Average value of `X` in `|0⟩` is `0`** (Nielsen & Chuang, Exercise 2.59). The expectation
`⟪X⟫ = ⟨0|X|0⟩` is the `(0,0)` matrix element of `X = Concrete.pauliX = !![0, 1; 1, 0]`, which is
`0`: applying `X` to `|0⟩` gives `|1⟩`, orthogonal to `|0⟩`. -/
theorem expectation_pauliX_qubitBasis_zero :
    (qubitBasis 0).expectation pauliXObservable = 0 := by
  rw [PureState.expectation, qubitBasis_vec, pauliXObservable_op]
  -- Restate the inner product over the model space `EuclideanSpace ℂ (Fin 2)` (defeq to the
  -- qubit's state space) so the `EuclideanSpace`/matrix lemmas apply.
  change (inner ℂ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX)
        (EuclideanSpace.single 0 1))).re = 0
  rw [EuclideanSpace.inner_single_left, Matrix.ofLp_toEuclideanCLM]
  -- The `(0,0)` entry of `X = !![0, 1; 1, 0]` is `0`.
  simp [Matrix.mulVec, dotProduct, Concrete.pauliX]

/-- **Mean square of `X` in `|0⟩` is `1`** (Nielsen & Chuang, Exercise 2.59). Since `X² = 1`
(`pauliXObservable_op_mul_self`, the Pauli involution), `⟪X²⟫ = ⟨0|X²|0⟩ = ⟨0|0⟩ = 1` using
that `|0⟩` is normalized. -/
theorem expectation_sq_pauliX_qubitBasis_zero :
    (qubitBasis 0).expectation pauliXObservable.sq = 1 := by
  rw [PureState.expectation, Observable.sq_op, pow_two, pauliXObservable_op_mul_self,
    one_apply_eq_self, inner_self_eq_norm_sq_to_K, (qubitBasis 0).normalized]
  norm_num

/-- **Standard deviation of `X` in `|0⟩` is `1`** (Nielsen & Chuang, Exercise 2.59). Combining
the average value `⟪X⟫ = 0` and the mean square `⟪X²⟫ = 1`, the variance is
`⟪X²⟫ - ⟪X⟫² = 1 - 0² = 1`, so `Δ(X) = √1 = 1`. -/
theorem stdDev_pauliX_qubitBasis_zero :
    (qubitBasis 0).stdDev pauliXObservable = 1 := by
  rw [PureState.stdDev, PureState.variance, expectation_sq_pauliX_qubitBasis_zero,
    expectation_pauliX_qubitBasis_zero]
  norm_num

end AxQM
