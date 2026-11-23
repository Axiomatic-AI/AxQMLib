/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Eigenstate
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# AxQM.Postulates.API — variance and standard deviation of an observable

Definitions of the *statistics* of an observable in a pure state, built on
the expectation value `PureState.expectation` (of `AxQM/Postulates/Observable.lean`) and the
eigenstate predicate of `AxQM/Postulates/API/Eigenstate.lean` (`Observable.HasEigenstate`,
`PureState.expectation_of_hasEigenstate`). N&C, §2.2.5 (page 88) reads these off a projective
measurement of the observable `M`:

* `Observable.sq` (`M²`) — the **square of an observable**: the observable whose operator is
  `M.op ^ 2`. Self-adjoint because a natural power of a self-adjoint operator is self-adjoint
  (`IsSelfAdjoint.pow`). The lemma `Observable.sq_op` gives its operator.
* `PureState.variance` (`[Δ(M)]²`) — the **variance** `⟪M²⟫ − ⟪M⟫²`, N&C's formula (2.115) for the
  mean square spread. Defined from `expectation` and `sq`.
* `PureState.stdDev` (`Δ(M)`) — the **standard deviation** `√(variance)`, N&C's `Δ(M) =
  √(⟪M²⟫ − ⟪M⟫²)`. Taking `√` of the (a-priori possibly negative) formula is faithful to N&C, which
  states exactly this formula; the general nonnegativity `⟪M²⟫ ≥ ⟪M⟫²` is a separate fact not
  needed here.
* `Observable.HasEigenstate.sq` — an eigenstate of `M` with eigenvalue `m` is an eigenstate of `M²`
  with eigenvalue `m²`. The step feeding the standard-deviation computation.

The consuming Nielsen–Chuang item (Exercise 2.58) states its answers — average `= m`, standard
deviation `= 0` — as theorems in `AxQM/NC/Ch2/Exercise2_58.lean`, using
`PureState.expectation_of_hasEigenstate` for the average.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Square of an observable** `M²`: the observable of the same system with operator `M.op ^ 2`.
Self-adjoint because a natural power of a self-adjoint operator is self-adjoint
(`IsSelfAdjoint.pow`). The observable measured when computing the mean square value `⟪M²⟫`. -/
def Observable.sq (A : Observable S) : Observable S where
  op := A.op ^ 2
  selfAdjoint := A.selfAdjoint.pow 2

@[simp]
theorem Observable.sq_op (A : Observable S) : A.sq.op = A.op ^ 2 := rfl

namespace PureState

/-- **Variance** `[Δ(M)]²_ψ = ⟪M²⟫_ψ − ⟪M⟫_ψ²` of an observable `A` in the pure state `ψ`
(N&C (2.115)): the mean square spread of the measured values of `A`. -/
def variance (ψ : PureState S) (A : Observable S) : ℝ :=
  ψ.expectation A.sq - (ψ.expectation A) ^ 2

/-- **Standard deviation** `Δ(M)_ψ = √(⟪M²⟫_ψ − ⟪M⟫_ψ²)` of an observable `A` in the pure state `ψ`
(N&C, page 88): the square root of the variance, measuring the typical spread of the observed
values of `A`. -/
def stdDev (ψ : PureState S) (A : Observable S) : ℝ := Real.sqrt (ψ.variance A)

end PureState

/-- An eigenstate of `A` with eigenvalue `m` is an eigenstate of `A²` with eigenvalue `m²`:
`A² ψ = A (A ψ) = A (m • ψ) = m • (A ψ) = m² • ψ`. Feeds the mean-square value `⟪A²⟫ = m²` in the
standard-deviation computation, phrased on the shared `Observable.HasEigenstate` predicate. -/
theorem Observable.HasEigenstate.sq {A : Observable S} {m : ℝ} {ψ : PureState S}
    (h : A.HasEigenstate m ψ) : A.sq.HasEigenstate (m ^ 2) ψ := by
  rw [Observable.HasEigenstate, Observable.sq_op, pow_two, mul_apply_eq_comp, h,
    map_smul, h, smul_smul]
  module

end AxQM
