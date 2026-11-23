/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliMeasurement
import AxQM.Postulates.API.RelativePhase
import AxQM.Postulates.API.PhaseFlipCode

/-!
# AxQM.Postulates.API — the B92 protocol apparatus (Nielsen & Chuang §12.6.3)

Model of the B92 quantum-key-distribution protocol (N&C pp. 588–591), the
infrastructure behind Exercise 12.28 (`AxQM/NC/Ch12/Exercise12_28.lean`). Alice's
non-orthogonal signal states, Bob's two measurement bases, his projective sign measurement, and
the resulting Born probability of the outcome `b = 1`.

* `b92AliceState a` — Alice's signal `|ψ_a⟩`: `|0⟩` (`qubitKet0`) if `a = 0`, `|+⟩` (`qubitPlus`) if
  `a = 1`.
* `b92BobObservable a'` — Bob's `±1` observable: Pauli `Z` (computational basis) if `a' = 0`, Pauli
  `X` (the `|±⟩` basis) if `a' = 1`.
* `b92Measurement a'` — Bob's two-outcome projective sign measurement `Observable.signMeasurement`
  of `b92BobObservable a'` (outcome `0 ↔ +1`, `1 ↔ −1`); the involution `A² = 1` it needs is the
  Pauli involution `pauliZObservable_op_mul_self` / `pauliXObservable_op_mul_self`.
* `b92ProbB1 a a'` — the Born probability `P(b = 1 | a, a')` of Bob obtaining `b = 1` (the `−1`
  eigenstate, `Fin 2` index `1`).
* `expectation_pauliX_qubitKet0` / `expectation_pauliZ_qubitPlus` — `⟪X⟫_{|0⟩} = ⟪Z⟫_{|+⟩} = 0`:
  Alice's state is *unbiased* in Bob's mismatched basis, the inputs that give the `1/2` outcome.

`b92Measurement` bundles the concrete Pauli observable into a `Measurement`, so its
completeness obligation is the operator identity `A.op * A.op = 1`. The theorems of Exercise 12.28
are stated in terms of `b92ProbB1`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-! ### The B92 protocol data -/

/-- **Alice's state `|ψ_a⟩`** as a function of her classical bit `a` (`false ↔ 0`, `true ↔ 1`):
`|ψ_0⟩ = |0⟩` (`qubitKet0`) and `|ψ_1⟩ = |+⟩` (`qubitPlus`). The two non-orthogonal states of the
B92 protocol. -/
def b92AliceState (a : Bool) : PureState qubit := cond a qubitPlus qubitKet0

/-- **Bob's `±1` observable** as a function of his basis-choice bit `a'` (`false ↔ 0`, `true ↔ 1`):
the Pauli `Z` observable (measuring in the computational basis `{|0⟩, |1⟩}`) if `a' = 0`, the Pauli
`X` observable (measuring in the `{|+⟩, |-⟩}` basis) if `a' = 1`. -/
def b92BobObservable (a' : Bool) : Observable qubit := cond a' pauliXObservable pauliZObservable

/-- **Bob's measurement** for basis choice `a'`: the two-outcome projective sign measurement of his
`±1` observable `b92BobObservable a'` (`Observable.signMeasurement`, outcome `0 ↔ +1`, `1 ↔ −1`).
The involution `A² = 1` needed to build it is the Pauli involution `pauliZObservable_op_mul_self`
/ `pauliXObservable_op_mul_self`. -/
def b92Measurement (a' : Bool) : Measurement (Fin 2) qubit :=
  (b92BobObservable a').signMeasurement <| by
    cases a'
    · exact pauliZObservable_op_mul_self
    · exact pauliXObservable_op_mul_self

/-- **The Born probability `P(b = 1 | a, a')`** of Bob obtaining outcome `b = 1` (the `−1`
eigenstate, `Fin 2` index `1`) when Alice sends `|ψ_a⟩` and Bob measures in basis `a'`. -/
def b92ProbB1 (a a' : Bool) : ℝ := (b92Measurement a').bornProb (b92AliceState a).toState 1

/-- **B92 Born probability as an expectation:** `P(b = 1 | a, a') = (1 − ⟪A⟫)/2`, the
sign-measurement Born rule (`bornProb_signMeasurement_minus`) specialised to Bob's observable
`b92BobObservable a'` on Alice's state `b92AliceState a`. The bridge for computing
the `b = 1` probability without unfolding `b92Measurement`. -/
theorem b92ProbB1_eq (a a' : Bool) :
    b92ProbB1 a a' = (1 - (b92AliceState a).expectation (b92BobObservable a')) / 2 := by
  unfold b92ProbB1 b92Measurement
  rw [Observable.bornProb_signMeasurement_minus]

/-! ### Alice's state is unbiased in Bob's mismatched basis -/

/-- **`⟪X⟫_{|0⟩} = 0`:** the state `|0⟩` is unbiased for a Pauli `X` measurement. The `X`-component
`(1, 0, 0)₃ = 0` of `pauliObservable_expectation_qubitKet0`. -/
theorem expectation_pauliX_qubitKet0 : qubitKet0.expectation pauliXObservable = 0 := by
  have h := pauliObservable_expectation_qubitKet0 ![1, 0, 0]
  rw [pauliXObservable]
  simpa using h

/-- **The Pauli `Z` observable sends `|+⟩` to `|−⟩`:** `Z|+⟩ = |−⟩` at operator level, the
observable-level companion of `pauliZGate_op_qubitPlus`. Both operators are the same
`Matrix.toEuclideanCLM Concrete.pauliZ` (`pauliZObservable_op` / `pauliZGate_op`), so this reduces
structurally to the gate-level fact — no matrix computation. -/
theorem pauliZObservable_op_qubitPlus :
    pauliZObservable.op qubitPlus.vec = qubitMinus.vec := by
  rw [pauliZObservable_op, ← pauliZGate_op, pauliZGate_op_qubitPlus]

/-- **`⟪Z⟫_{|+⟩} = 0`:** the state `|+⟩` is unbiased for a Pauli `Z` measurement. Since `Z|+⟩ = |-⟩`
(`pauliZObservable_op_qubitPlus`) and `⟨+|-⟩ = 0`, the expectation `⟪+|Z|+⟩ = ⟨+|-⟩ = 0`. -/
theorem expectation_pauliZ_qubitPlus : qubitPlus.expectation pauliZObservable = 0 := by
  rw [PureState.expectation, pauliZObservable_op_qubitPlus, inner_qubitPlus_qubitMinus,
    Complex.zero_re]

end AxQM
