/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.StabilizerMeasurement
import AxQM.Postulates.API.RelativePhase

/-!
# AxQM.Postulates.API — the six-state protocol states, bases, and measurement

The infrastructure behind the **six-state** quantum-key-distribution protocol
(Nielsen & Chuang Exercise 12.29, p. 591; Bruß 1998), the three-basis generalization of BB84
(`Postulates/API/BB84.lean`). Alice's six encoding states — the eigenstates of the three Pauli
observables `X`, `Y`, `Z` — the three mutually conjugate measurement bases, and Bob's projective
measurement in a chosen basis. Like the BB84 apparatus, this is a thin bundling of the concrete
Pauli data into states and measurements, on which the Nielsen & Chuang probabilities of
`NC/Ch12/Exercise12_29.lean` are a direct application of the stabilizer measurement-update rules of
`StabilizerMeasurement`.

* `sixStateObservable i` — the observable Bob measures for basis index `i : Fin 3`: the Pauli `X`
  observable for `i = 0`, `Y` for `i = 1`, `Z` for `i = 2`. Each is a self-adjoint involution
  (`sixStateObservable_op_mul_self`), and any two distinct bases **anticommute**
  (`sixStateObservable_op_anticomm`) — the algebraic heart of "three mutually conjugate bases",
  the mutual unbiasedness that makes a measurement in the wrong basis uninformative.
* `sixStateState i s` — Alice's encoding of data bit `s : Fin 2` in basis `i`: `|+⟩, |−⟩` for the
  `X` basis (`i = 0`), `|+i⟩, |−i⟩` for the `Y` basis (`i = 1`), and `|0⟩, |1⟩` for the `Z` basis
  (`i = 2`). Each is the `(-1)^s`-eigenstate of `sixStateObservable i`.
* `sixStateMeasurement i` — Bob's two-outcome projective measurement of the `±1` observable
  `sixStateObservable i` (`Observable.signMeasurement`, outcome `0 ↔ +1`, `1 ↔ −1`). Its outcome
  index is Bob's result bit.

The pairwise anticommutation of the three bases (`sixStateObservable_op_anticomm`) is assembled from
the Pauli anticommutation trio (`pauliXObservable_op_anticomm_pauliZObservable_op`,
`pauliYObservable_op_anticomm_pauliZObservable_op`,
`pauliXObservable_op_anticomm_pauliYObservable_op`) in `Postulates/API/Qubit.lean`.

This extends the `±1`-observable measurement family of `PauliMeasurement` /
`StabilizerMeasurement` / `BB84`. The Nielsen & Chuang probabilities (Exercise 12.29) are in
`AxQM/NC/Ch12/Exercise12_29.lean`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The six-state measurement bases -/

/-- **The six-state measurement observable for basis index `i`.** Bob measures the Pauli `X`
observable when `i = 0` (the `{|+⟩, |−⟩}` basis), `Y` when `i = 1` (the `{|+i⟩, |−i⟩}` basis), and
`Z` when `i = 2` (the computational basis `{|0⟩, |1⟩}`) — the three mutually conjugate bases of the
protocol (N&C Exercise 12.29). -/
def sixStateObservable (i : Fin 3) : Observable qubit :=
  ![pauliXObservable, pauliYObservable, pauliZObservable] i

@[simp] theorem sixStateObservable_zero : sixStateObservable 0 = pauliXObservable := rfl

@[simp] theorem sixStateObservable_one : sixStateObservable 1 = pauliYObservable := rfl

@[simp] theorem sixStateObservable_two : sixStateObservable 2 = pauliZObservable := rfl

/-- Each six-state basis observable is a self-adjoint **involution**: `(sixStateObservable i)² = 1`.
All of `X² = 1`, `Y² = 1`, `Z² = 1` (`pauli{X,Y,Z}Observable_op_mul_self`), so its projective
measurement is a genuine two-outcome `signMeasurement`. -/
theorem sixStateObservable_op_mul_self (i : Fin 3) :
    (sixStateObservable i).op * (sixStateObservable i).op = 1 := by
  fin_cases i
  · simpa using pauliXObservable_op_mul_self
  · simpa using pauliYObservable_op_mul_self
  · simpa using pauliZObservable_op_mul_self

/-- **Any two distinct six-state bases anticommute:** for `i ≠ j`, `(sixStateObservable i)
(sixStateObservable j) = −(sixStateObservable j) (sixStateObservable i)`. This is the pairwise
anticommutation of `X`, `Y`, `Z` (N&C eq. 2.40) read through the `i ↦ {X, Y, Z}` assignment — the
algebraic content of "three mutually conjugate bases" that makes a measurement in the wrong basis
uninformative (its expectation vanishes). -/
theorem sixStateObservable_op_anticomm {i j : Fin 3} (h : i ≠ j) :
    (sixStateObservable i).op * (sixStateObservable j).op
      = -((sixStateObservable j).op * (sixStateObservable i).op) := by
  -- Nine `(i, j)` cases: the three diagonal are `absurd`; each off-diagonal bullet is a direct
  -- `exact` of the matching Pauli anticommutation lemma — forward as-is, and reversed via
  -- `(neg_eq_iff_eq_neg.mpr ·).symm` (`b a = -(a b)` from `a b = -(b a)`). Every bullet unifies
  -- with the `sixStateObservable`-phrased goal by `exact`'s defeq (`sixStateObservable i` unfolds
  -- to the concrete Pauli observable), so no `change`/`rw` is needed.
  fin_cases i <;> fin_cases j
  · exact absurd rfl h
  · exact pauliXObservable_op_anticomm_pauliYObservable_op
  · exact pauliXObservable_op_anticomm_pauliZObservable_op
  · exact (neg_eq_iff_eq_neg.mpr pauliXObservable_op_anticomm_pauliYObservable_op).symm
  · exact absurd rfl h
  · exact pauliYObservable_op_anticomm_pauliZObservable_op
  · exact (neg_eq_iff_eq_neg.mpr pauliXObservable_op_anticomm_pauliZObservable_op).symm
  · exact (neg_eq_iff_eq_neg.mpr pauliYObservable_op_anticomm_pauliZObservable_op).symm
  · exact absurd rfl h

/-! ### Alice's encoding states -/

/-- **Alice's six-state encoding state** of data bit `s` in basis `i`: the `(-1)^s`-eigenstate of
`sixStateObservable i`. For the `X` basis (`i = 0`), `|+⟩` (`s = 0`) and `|−⟩` (`s = 1`); for the
`Y` basis (`i = 1`), `|+i⟩` and `|−i⟩`; for the `Z` basis (`i = 2`), `|0⟩` and `|1⟩`. These are the
six eigenstates of `X`, `Y`, `Z` — the states of Exercise 12.29. -/
def sixStateState (i : Fin 3) (s : Fin 2) : PureState qubit :=
  ![![qubitPlus, qubitMinus], ![qubitPlusI, qubitMinusI], ![qubitKet0, qubitBasis 1]] i s

@[simp] theorem sixStateState_zero_zero : sixStateState 0 0 = qubitPlus := rfl

@[simp] theorem sixStateState_zero_one : sixStateState 0 1 = qubitMinus := rfl

@[simp] theorem sixStateState_one_zero : sixStateState 1 0 = qubitPlusI := rfl

@[simp] theorem sixStateState_one_one : sixStateState 1 1 = qubitMinusI := rfl

@[simp] theorem sixStateState_two_zero : sixStateState 2 0 = qubitKet0 := rfl

@[simp] theorem sixStateState_two_one : sixStateState 2 1 = qubitBasis 1 := rfl

/-! ### Bob's measurement -/

/-- **Bob's six-state measurement in basis `i`:** the two-outcome projective measurement of the `±1`
observable `sixStateObservable i` (`Observable.signMeasurement`, outcome `0 ↔ +1`, `1 ↔ −1`). The
outcome index is Bob's result bit. -/
def sixStateMeasurement (i : Fin 3) : Measurement (Fin 2) qubit :=
  (sixStateObservable i).signMeasurement (sixStateObservable_op_mul_self i)

theorem sixStateMeasurement_eq (i : Fin 3) :
    sixStateMeasurement i
      = (sixStateObservable i).signMeasurement (sixStateObservable_op_mul_self i) :=
  rfl

end AxQM
