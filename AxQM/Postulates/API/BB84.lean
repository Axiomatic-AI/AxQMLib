/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.StabilizerMeasurement
import AxQM.Postulates.API.RelativePhase

/-!
# AxQM.Postulates.API — the BB84 states, bases, and measurement

The infrastructure behind the BB84 quantum-key-distribution protocol (Nielsen &
Chuang §12.6.3, p. 587): Alice's four encoding states `|ψ_{ab}⟩`, the two conjugate measurement
bases (`Z` for `b = 0`, `X` for `b = 1`), and Bob's projective measurement in a chosen basis.
Exercise 12.26 is a thin application of the stabilizer measurement-update rules of
`StabilizerMeasurement`.

* `bb84Observable b` — the observable Bob measures for basis bit `b`: the Pauli `Z` observable for
  `b = 0` (computational basis) and the Pauli `X` observable for `b = 1` (Hadamard basis). Both are
  self-adjoint involutions (`bb84Observable_op_mul_self`), and the two bases **anticommute**
  (`bb84Observable_op_anticomm`) — the algebraic heart of the "conjugate bases" of BB84.
* `bb84State a b` — Alice's encoding of data bit `a` in basis `b`: `|0⟩, |1⟩` for `b = 0` and
  `|+⟩, |−⟩` for `b = 1` (N&C eqs. 12.180–12.183). Each is the `(-1)^a`-eigenstate of
  `bb84Observable b`.
* `bb84Measurement b` — Bob's two-outcome projective measurement of `bb84Observable b`, the
  `Observable.signMeasurement` of that `±1` observable (outcome `0 ↔ +1`, `1 ↔ −1`). Its outcome
  index is Bob's result bit `a'`.

The arbitrary-eigenvalue vanishing-expectation engine
`Observable.expectation_eq_zero_of_anticomm_eigenstate` this consumes — needed because Alice's
`a = 1` states are `−1` (not `+1`) eigenstates of their basis — lives with its `μ = 1` sibling in
`AxQM/Postulates/API/StabilizerMeasurement.lean`.

This extends the `±1`-observable measurement family of `PauliMeasurement` /
`StabilizerMeasurement`. The Nielsen & Chuang probabilities (Exercise 12.26) are recorded in
`AxQM/NC/Ch12/Exercise12_26.lean`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The BB84 measurement bases -/

/-- **The BB84 measurement observable for basis bit `b`.** Bob measures the Pauli `Z` observable
when `b = 0` (the computational basis `{|0⟩, |1⟩}`) and the Pauli `X` observable when `b = 1` (the
Hadamard basis `{|+⟩, |−⟩}`) — the two conjugate bases of the protocol (N&C §12.6.3). -/
def bb84Observable (b : Fin 2) : Observable qubit := ![pauliZObservable, pauliXObservable] b

@[simp] theorem bb84Observable_zero : bb84Observable 0 = pauliZObservable := rfl

@[simp] theorem bb84Observable_one : bb84Observable 1 = pauliXObservable := rfl

/-- Each BB84 basis observable is a self-adjoint **involution**: `(bb84Observable b)² = 1`. Both
`Z² = 1` (`pauliZObservable_op_mul_self`) and `X² = 1` (`pauliXObservable_op_mul_self`), so its
projective measurement is a genuine two-outcome `signMeasurement`. -/
theorem bb84Observable_op_mul_self (b : Fin 2) :
    (bb84Observable b).op * (bb84Observable b).op = 1 := by
  fin_cases b
  · simpa using pauliZObservable_op_mul_self
  · simpa using pauliXObservable_op_mul_self

/-- **The two BB84 bases anticommute:** for `b ≠ b'`, `(bb84Observable b) (bb84Observable b') =
−(bb84Observable b') (bb84Observable b)`. This is `X Z = −Z X` (N&C eq. 2.75) read through the
`b ↦ {Z, X}` assignment — the algebraic content of "`Z` and `X` are conjugate bases" that makes a
measurement in the wrong basis uninformative. -/
theorem bb84Observable_op_anticomm {b b' : Fin 2} (h : b ≠ b') :
    (bb84Observable b).op * (bb84Observable b').op
      = -((bb84Observable b').op * (bb84Observable b).op) := by
  fin_cases b <;> fin_cases b'
  · exact absurd rfl h
  · change pauliZObservable.op * pauliXObservable.op
        = -(pauliXObservable.op * pauliZObservable.op)
    rw [pauliXObservable_op_anticomm_pauliZObservable_op, neg_neg]
  · change pauliXObservable.op * pauliZObservable.op
        = -(pauliZObservable.op * pauliXObservable.op)
    exact pauliXObservable_op_anticomm_pauliZObservable_op
  · exact absurd rfl h

/-! ### Alice's encoding states -/

/-- **Alice's BB84 encoding state `|ψ_{ab}⟩`** of data bit `a` in basis `b` (N&C eqs.
12.180–12.183): `|ψ_{00}⟩ = |0⟩`, `|ψ_{10}⟩ = |1⟩` in the computational basis (`b = 0`), and
`|ψ_{01}⟩ = |+⟩`, `|ψ_{11}⟩ = |−⟩` in the Hadamard basis (`b = 1`). Each is the `(-1)^a`-eigenstate
of the basis
observable `bb84Observable b`. -/
def bb84State (a b : Fin 2) : PureState qubit :=
  ![![qubitKet0, qubitPlus], ![qubitBasis 1, qubitMinus]] a b

@[simp] theorem bb84State_zero_zero : bb84State 0 0 = qubitKet0 := rfl

@[simp] theorem bb84State_zero_one : bb84State 0 1 = qubitPlus := rfl

@[simp] theorem bb84State_one_zero : bb84State 1 0 = qubitBasis 1 := rfl

@[simp] theorem bb84State_one_one : bb84State 1 1 = qubitMinus := rfl

/-! ### Bob's measurement -/

/-- **Bob's BB84 measurement in basis `b`:** the two-outcome projective measurement of the `±1`
observable `bb84Observable b` (`Observable.signMeasurement`, outcome `0 ↔ +1`, `1 ↔ −1`). The
outcome index is Bob's result bit `a'`. -/
def bb84Measurement (b : Fin 2) : Measurement (Fin 2) qubit :=
  (bb84Observable b).signMeasurement (bb84Observable_op_mul_self b)

theorem bb84Measurement_eq (b : Fin 2) :
    bb84Measurement b = (bb84Observable b).signMeasurement (bb84Observable_op_mul_self b) := rfl

end AxQM
