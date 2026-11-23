/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BellExpectation

/-!
# Nielsen & Chuang, Exercise 2.70 (Bell states are locally indistinguishable)

Show <psi|E⊗I|psi> is same for all four Bell states; can Eve infer Alice's bits?

The claim is about the one-sided expectation value `⟪E ⊗ I⟫` of the two-qubit system in each of
the four Bell states `|β_xy⟩` (N&C eq. (2.134)–(2.137)).

`bellState_expectation_tmul_id_eq` is the exercise's claim: for **any** observable `E` on Alice's
qubit, the expectation of `E ⊗ I` is the *same* in every Bell state — `⟪E⊗I⟫_{β_xy}` is independent
of the classical bits `x, y`. It is stated for `PureState.expectation`, `Observable.tmul` (`⊗`),
`Observable.id` (`I`) and the Bell-state family `bellState`. It follows from the computation
`bellState_expectation_tmul_id` (`AxQM/Postulates/API/BellExpectation.lean`), which evaluates each
expectation to the *common* value `½(⟪0|E|0⟫ + ⟪1|E|1⟫) = ½ Tr E`.

## The declarations

The formalisation of Exercise 2.70 is the *set* of declarations below, not a single theorem in
this file.

* `bellState (x y : Fin 2)` (`AxQM/Postulates/API/BellBasis.lean`, Exercise 2.69) — the indexed
  family of all four Bell states `|β_xy⟩` (N&C eqs. (2.134)–(2.137)).
* `Observable.id` (`AxQM/Postulates/API/Observable.lean`) — the identity effect `I` on the second
  qubit.
* `bellState_expectation_tmul_id` (`AxQM/Postulates/API/BellExpectation.lean`) — each one-sided
  expectation `⟪E⊗I⟫_{β_xy}` equals the common value `½(⟪0|E|0⟫ + ⟪1|E|1⟫) = ½ Tr E`.
* `bellState_expectation_tmul_id_eq` (this file) — that common value is literally
  *Bell-state-independent*, `⟪E⊗I⟫_{β_xy} = ⟪E⊗I⟫_{β_x'y'}` for all `x, y, x', y'` — the
  exercise's "takes the same value for any of the four Bell states".

Together these are the exercise's first (formal) part; the second part is the informal reading
recorded under *"Why the value is Bell-independent"* below.

## Notes on the statement

* **The `∀ x y x' y'` shape.** N&C's "takes the same value for any of the four Bell states" is one
  claim of Bell-state independence; it is recorded as the single universally-quantified equality
  over the indexed Bell family `bellState (x y : Fin 2)` (of `AxQM/Postulates/API/BellBasis.lean`,
  Exercise 2.69), rather than an ad-hoc conjunction of the four states. The shared value `½ Tr E`
  is computed in `AxQM/Postulates/API/BellExpectation.lean`, and only the equality is stated here.
* **General observable vs. positive operator.** N&C states the result for a *positive* operator `E`
  (a measurement effect). We prove it for an arbitrary observable `E` (a self-adjoint operator):
  the equality holds for every observable and positivity is never used, so this is a faithful
  generalisation, not a weakening — it *includes* N&C's positive case, which is exactly what the
  physical conclusion below needs (Eve's measurement effects are positive operators, hence
  observables).
* **Why the value is Bell-independent — and the informal second part.** The common value is
  `½ Tr E = Tr(E · I/2)`: the reduced state of every Bell state on Alice's qubit is the *maximally
  mixed* state `I/2`, so Alice's qubit alone carries the same statistics regardless of the two
  encoded bits. Since Eve, intercepting only Alice's qubit, can measure nothing beyond such
  `⟪E ⊗ I⟫` expectations, and these are identical for all four Bell states, **Eve can infer
  nothing** about which of `00, 01, 10, 11` Alice is sending — the message is revealed only once Bob
  holds both qubits and can measure in the (globally distinguishing) Bell basis (`bellBasis`,
  Exercise 2.69). `bellState_expectation_tmul_id_eq` is the formal core of this argument; the "can
  Eve infer anything" discussion is its physical reading.
-/

open scoped InnerProductSpace

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.70.** For any observable `E` on Alice's qubit, the one-sided
expectation `⟪E ⊗ I⟫` takes the *same* value in every Bell state `|β_xy⟩` (N&C eq.
(2.134)–(2.137)): `⟪E⊗I⟫_{β_xy} = ⟪E⊗I⟫_{β_x'y'}` for all `x, y, x', y'`. Hence Eve, who intercepts
only Alice's qubit in the superdense coding protocol, sees Bell-state-independent statistics and
can infer nothing about Alice's two bits.

Proved by evaluating each expectation to the common value `½(⟪0|E|0⟫ + ⟪1|E|1⟫) = ½ Tr E`
(`bellState_expectation_tmul_id`), the trace of `E` against the maximally mixed reduced state
`I/2`. -/
theorem bellState_expectation_tmul_id_eq (E : Observable qubit) (x y x' y' : Fin 2) :
    (bellState x y).expectation (E ⊗ Observable.id qubit)
      = (bellState x' y').expectation (E ⊗ Observable.id qubit) := by
  rw [bellState_expectation_tmul_id, bellState_expectation_tmul_id]

end AxQM
