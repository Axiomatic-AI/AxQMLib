/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.B92Protocol
import AxQM.Postulates.API.StabilizerMeasurement
import AxQM.NC.Ch4.Exercise4_1

/-!
# Nielsen & Chuang, Exercise 12.28 (B92: `b = 1` forces perfect correlation of `a` and `a'`)

*(N&C p. 591.)*

B92: show when b=1, a and a' are perfectly correlated.

## The B92 protocol (N&C §12.6.3, pp. 588–591)

Alice prepares a random classical bit `a` and sends Bob the qubit

  `|ψ_a⟩ = |0⟩`   if `a = 0`,     `|ψ_a⟩ = |+⟩ = (|0⟩ + |1⟩)/√2`   if `a = 1`.

Bob generates a random bit `a'` and measures the qubit he receives in the `Z` basis `{|0⟩, |1⟩}`
(if `a' = 0`) or the `X` basis `{|+⟩, |-⟩}` (if `a' = 1`), obtaining `b ∈ {0, 1}`, where `b = 1`
corresponds to the `−1` eigenstate (`|1⟩` resp. `|-⟩`) and `b = 0` to the `+1` eigenstate. Bob
announces `b`; Alice and Bob keep only the pairs `{a, a'}` for which `b = 1`.

The physics N&C states: *"when `a = a'`, then `b = 0` always. Only if `a' = 1 − a` will Bob obtain
`b = 1`, and that occurs with probability `1/2`."* The Born probability of `b = 1` is therefore
`0` when `a = a'` (Alice's state is a `+1` eigenstate of Bob's observable) and `1/2` when `a ≠ a'`
(Alice's state is *unbiased* in Bob's basis, `⟪A⟫ = 0`). Hence observing `b = 1` (an event of
positive probability) is only possible when `a ≠ a'`: `a` and `a'` are then **perfectly
(anti-)correlated** — each determines the other, `a' = 1 − a`. Since the final key is `a` for Alice
and `1 − a'` for Bob (N&C), this is exactly the agreement of their keys.

## Formalisation

Classical bits are modelled by `Bool` (`false ↔ 0`, `true ↔ 1`); Bob's measurement outcome is the
`Fin 2` index of `Observable.signMeasurement` (`0 ↔ +1`, `1 ↔ −1`), so `b = 1` is outcome `1`.

The **protocol apparatus** — `b92AliceState`, `b92BobObservable`, `b92Measurement`, `b92ProbB1`, and
the unbiasedness facts `expectation_pauliX_qubitKet0` / `expectation_pauliZ_qubitPlus` — is in
`AxQM/Postulates/API/B92Protocol.lean`: `b92Measurement` bundles a concrete Pauli observable into a
`Measurement`, whose completeness is `A.op * A.op = 1`. The theorems below name only
`b92ProbB1 : ℝ` and `Bool`:

* `b92ProbB1_eq_zero_of_eq` / `b92ProbB1_eq_half_of_ne` — the two probability values `0` (matched
  bases) and `1/2` (mismatched bases).
* `b92_perfectly_correlated` — **the exercise:** `P(b = 1 | a, a') ≠ 0 ↔ a ≠ a'`; observing `b = 1`
  happens exactly when `a` and `a'` differ, so `b = 1` pins them into perfect correlation.
* `b92_key_agreement` — the payoff for QKD: when `b = 1`, Alice's key `a` equals Bob's key `1 − a'`
  (`a = !a'`).

The proofs apply the sign-measurement Born rule (`bornProb_signMeasurement_minus`, in
`AxQM/Postulates/API/PauliMeasurement.lean` alongside `bornProb_signMeasurement_plus`) and the
eigenstate facts `qubitKet0_hasEigenstate_pauliZ` / `qubitPlus_hasEigenstate_pauliX` (Ex 4.1) for
the four `(state, basis)` combinations.
-/

noncomputable section

namespace AxQM

/-- **Matched bases give `b = 0` with certainty:** `P(b = 1 | a, a) = 0`. When Bob's basis matches
Alice's state (`a = a'`), Alice's state is a `+1` eigenstate of Bob's observable (`Z|0⟩ = |0⟩`,
`X|+⟩ = |+⟩`), so the `−1` outcome `b = 1` is impossible. -/
theorem b92ProbB1_eq_zero_of_eq (a : Bool) : b92ProbB1 a a = 0 := by
  cases a
  · exact pauliZObservable.bornProb_signMeasurement_minus_of_hasEigenstate_one
      pauliZObservable_op_mul_self qubitKet0 qubitKet0_hasEigenstate_pauliZ
  · exact pauliXObservable.bornProb_signMeasurement_minus_of_hasEigenstate_one
      pauliXObservable_op_mul_self qubitPlus qubitPlus_hasEigenstate_pauliX

/-- **Mismatched bases give `b = 1` with probability `1/2`:** `P(b = 1 | a, a') = 1/2` when
`a ≠ a'`. Alice's state is unbiased in Bob's basis (`⟪X⟫_{|0⟩} = ⟪Z⟫_{|+⟩} = 0`), so by the `−1`
Born rule `p(−1) = (1 − ⟪A⟫)/2 = 1/2`. -/
theorem b92ProbB1_eq_half_of_ne {a a' : Bool} (h : a ≠ a') : b92ProbB1 a a' = 1 / 2 := by
  rw [b92ProbB1_eq]
  cases a <;> cases a' <;>
    simp_all [b92AliceState, b92BobObservable, expectation_pauliX_qubitKet0,
      expectation_pauliZ_qubitPlus]

/-- **Exercise 12.28.** When `b = 1`, the bits `a` and `a'` are **perfectly correlated**: the event
`b = 1` has positive Born probability exactly when `a ≠ a'`. Observing `b = 1` therefore certifies
`a ≠ a'` (equivalently `a' = 1 − a`), so each of Alice's and Bob's bits determines the other. The
`←` direction is `b92ProbB1_eq_half_of_ne` (probability `1/2 ≠ 0`); the `→` direction is the
contrapositive of `b92ProbB1_eq_zero_of_eq` (matched bases give probability `0`). -/
theorem b92_perfectly_correlated {a a' : Bool} : b92ProbB1 a a' ≠ 0 ↔ a ≠ a' := by
  constructor
  · intro hne heq
    subst heq
    exact hne (b92ProbB1_eq_zero_of_eq a)
  · intro hne
    rw [b92ProbB1_eq_half_of_ne hne]
    norm_num

/-- **Key agreement.** When `b = 1`, Alice's final key `a` equals Bob's final key `1 − a'` (`!a'`):
the perfect correlation `a ≠ a'` (`b92_perfectly_correlated`) is exactly `a = !a'`. This is why B92
lets Alice and Bob extract a shared secret bit from the pairs they keep. -/
theorem b92_key_agreement {a a' : Bool} (h : b92ProbB1 a a' ≠ 0) : a = !a' := by
  have hne : a ≠ a' := b92_perfectly_correlated.mp h
  cases a <;> cases a' <;> simp_all

end AxQM
