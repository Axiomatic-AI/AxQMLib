/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SixStateProtocol
import AxQM.NC.Ch4.Exercise4_1

/-!
# Nielsen & Chuang, Exercise 12.29 — the six-state protocol

*(N&C p. 591.)*

Give six-state protocol; argue security; discuss noise/eavesdropping sensitivity.

## The six-state protocol (N&C §12.6.3; Bruß 1998)

The six-state protocol is the three-basis generalization of BB84 (Exercise 12.26). Alice picks a
random basis `i ∈ {X, Y, Z}` and a random data bit `s ∈ {0, 1}`, and sends Bob the
`(-1)^s`-eigenstate of the Pauli observable of basis `i` — one of the **six** eigenstates of `X`,
`Y`, `Z`:

  `X`: `|+⟩, |−⟩`,   `Y`: `|+i⟩, |−i⟩`,   `Z`: `|0⟩, |1⟩`.

Bob picks a random basis `j ∈ {X, Y, Z}` and measures the qubit in that basis. Over a public
channel they announce their bases and keep (sift) only the rounds where `i = j`; from the kept
rounds they extract correlated bit strings, then apply information reconciliation and privacy
amplification exactly as in BB84/B92.

**Why it is secure.** Security rests, as in BB84 and B92, on the impossibility of extracting Alice's
bit without disturbing her state. Concretely:

* When Bob's basis matches Alice's (`i = j`), Alice's state is an eigenstate of Bob's observable, so
  his outcome is **deterministic** and equals her bit `s` — the protocol works
  (`sixState_bornProb_matchedBasis`).
* When Bob (or an eavesdropper Eve) measures in a **different** basis (`i ≠ j`), the measured Pauli
  observable *anticommutes* with the one that prepared Alice's state, so the state is **mutually
  unbiased** for it: its expectation vanishes (`sixStateState_expectation_eq_zero_of_ne`) and each
  outcome is a fair coin (`sixState_bornProb_mismatchedBasis`), carrying no information about `s`
  (`sixState_bornProb_mismatchedBasis_uncorrelated`). An eavesdropper who guesses the wrong basis —
  which now happens with probability `2/3`, versus `1/2` in BB84 — thus learns nothing and
  necessarily disturbs the state, and is detected in the sifted check bits.

These are exactly the formalisable facts behind "give a protocol using six states, and argue why it
is also secure": the six states, their role as `±1` Pauli eigenstates
(`sixStateState_hasEigenstate`), the matched-basis correctness, and the mismatched-basis mutual
unbiasedness. The remaining clause — *discuss the sensitivity to noise and eavesdropping in
comparison with BB84 and B92* — is a qualitative comparison with no free-standing proposition to
prove; the physics it points at is that the extra, symmetric third basis forces an eavesdropper to
guess among three bases (wrong with probability `2/3`), tightening the disturbance an intercept-
resend attack induces and so raising the tolerable error rate relative to BB84 and B92. The
formalised mutual-unbiasedness content above is the quantitative core of that discussion.

## Formalisation

`signEigenvalue s = (-1)^s` (`+1` for `s = 0`, `−1` for `s = 1`) is the eigenvalue Alice's data bit
selects — the protocol-neutral sign selector shared with BB84, in
`AxQM/Postulates/API/PauliMeasurement.lean`. The protocol objects — `sixStateObservable`,
`sixStateState`, `sixStateMeasurement` — and the vanishing-expectation / fair-coin engines
(`Observable.expectation_eq_zero_of_anticomm_eigenstate`,
`Observable.bornProb_signMeasurement_*_of_anticomm_eigenstate`) are in
`AxQM/Postulates/API/SixStateProtocol.lean`. The theorems below are stated with
`Measurement.bornProb`, `PureState.expectation`, `Observable.HasEigenstate` and the protocol
definitions. The Pauli-eigenstate identifications they consume
(`qubit{Plus,Minus,PlusI,MinusI,Ket0}` / `qubitBasis 1` are the `±1` eigenstates of `X, Y, Z`) are
the content of N&C Exercise 4.1.
-/

noncomputable section

namespace AxQM

/-- **Each of the six states is the `(-1)^s`-eigenstate of its basis observable.** For the `X` basis
`X|+⟩ = |+⟩`, `X|−⟩ = −|−⟩`; for `Y`, `Y|+i⟩ = |+i⟩`, `Y|−i⟩ = −|−i⟩`; for `Z`, `Z|0⟩ = |0⟩`,
`Z|1⟩ = −|1⟩` — the Pauli-eigenstate content of N&C Exercise 4.1 (`qubit{Plus,Minus,PlusI,MinusI,
Ket0}_hasEigenstate_pauli*`, `qubitBasis_one_hasEigenstate_pauliZ`). This certifies that the six
protocol states really are the eigenstates of `X`, `Y`, and `Z`. -/
theorem sixStateState_hasEigenstate (i : Fin 3) (s : Fin 2) :
    (sixStateObservable i).HasEigenstate (signEigenvalue s) (sixStateState i s) := by
  fin_cases i <;> fin_cases s
  · exact qubitPlus_hasEigenstate_pauliX
  · exact qubitMinus_hasEigenstate_pauliX
  · exact qubitPlusI_hasEigenstate_pauliY
  · exact qubitMinusI_hasEigenstate_pauliY
  · exact qubitKet0_hasEigenstate_pauliZ
  · exact qubitBasis_one_hasEigenstate_pauliZ

/-- **Mutual unbiasedness (the security core).** When Bob's basis differs from Alice's (`i ≠ j`),
the observable `sixStateObservable j` he measures has **vanishing expectation** in Alice's state
`sixStateState i s`: `⟪sixStateObservable j⟫ = 0`. Because Alice's state is a nonzero-eigenvalue
eigenstate of `sixStateObservable i` while the measured `sixStateObservable j` anticommutes with it
(`sixStateObservable_op_anticomm`), the vanishing-expectation engine
`Observable.expectation_eq_zero_of_anticomm_eigenstate` applies. This is the precise sense in which
the three eigenbases are *mutually unbiased* — a wrong-basis measurement finds Alice's state
perfectly balanced, hence learns nothing about it. -/
theorem sixStateState_expectation_eq_zero_of_ne (i j : Fin 3) (s : Fin 2) (h : i ≠ j) :
    (sixStateState i s).expectation (sixStateObservable j) = 0 :=
  Observable.expectation_eq_zero_of_anticomm_eigenstate (sixStateObservable j)
    (sixStateObservable i) (sixStateState i s) (signEigenvalue_ne_zero s)
    (sixStateState_hasEigenstate i s) (sixStateObservable_op_anticomm (Ne.symm h))

/-- **Matched bases: Bob recovers Alice's bit with certainty.** When Bob measures in the same basis
Alice prepared (`j = i`), his outcome equals Alice's data bit `s` with probability one:
`p(outcome = s) = 1`. Because `sixStateState i s` is the `(-1)^s`-eigenstate of `sixStateObservable
i`, the outcome is deterministic — the `s = 0` (`+1`) and `s = 1` (`−1`) sub-cases are the
deterministic-outcome rules `Observable.bornProb_signMeasurement_plus_of_hasEigenstate_one` and
`..._minus_of_hasEigenstate_neg_one` of N&C §10.5.3. This is the correctness of the sifted key. -/
theorem sixState_bornProb_matchedBasis (i : Fin 3) (s : Fin 2) :
    (sixStateMeasurement i).bornProb (sixStateState i s).toState s = 1 := by
  rw [sixStateMeasurement_eq]
  fin_cases s
  · refine Observable.bornProb_signMeasurement_plus_of_hasEigenstate_one _ _ _ ?_
    simpa using sixStateState_hasEigenstate i 0
  · refine Observable.bornProb_signMeasurement_minus_of_hasEigenstate_neg_one _ _ _ ?_
    simpa using sixStateState_hasEigenstate i 1

/-- **Mismatched bases: Bob's result is a fair coin, `p(outcome = o) = 1/2`.** When Bob measures in
a different basis (`i ≠ j`), each outcome `o ∈ {0, 1}` occurs with probability exactly `1/2`.
Because `sixStateState i s` is a nonzero-eigenvalue eigenstate of `sixStateObservable i` while the
measured `sixStateObservable j` anticommutes with it, the measured observable has vanishing
expectation (`sixStateState_expectation_eq_zero_of_ne`); each outcome is then a fair coin via the
random-outcome rules `Observable.bornProb_signMeasurement_plus_of_anticomm_eigenstate` /
`..._minus_of_anticomm_eigenstate`. This is why a wrong-basis measurement is uninformative. -/
theorem sixState_bornProb_mismatchedBasis (i j : Fin 3) (s o : Fin 2) (h : i ≠ j) :
    (sixStateMeasurement j).bornProb (sixStateState i s).toState o = 1 / 2 := by
  rw [sixStateMeasurement_eq]
  fin_cases o
  · exact Observable.bornProb_signMeasurement_plus_of_anticomm_eigenstate _ (sixStateObservable i)
      _ _ (signEigenvalue_ne_zero s) (sixStateState_hasEigenstate i s)
      (sixStateObservable_op_anticomm (Ne.symm h))
  · exact Observable.bornProb_signMeasurement_minus_of_anticomm_eigenstate _ (sixStateObservable i)
      _ _ (signEigenvalue_ne_zero s) (sixStateState_hasEigenstate i s)
      (sixStateObservable_op_anticomm (Ne.symm h))

/-- **Mismatched bases: Bob's result is uncorrelated with Alice's bit.** When Bob measures in the
wrong basis, the distribution of his outcome is independent of Alice's data bit `s`: for any two
bits `s₁, s₂` and any outcome `o`, the probabilities agree. Both equal `1/2`
(`sixState_bornProb_mismatchedBasis`), so a wrong-basis measurement carries no information about
Alice's bit — the six-state analogue of BB84's "completely uncorrelated". -/
theorem sixState_bornProb_mismatchedBasis_uncorrelated (i j : Fin 3) (s₁ s₂ o : Fin 2)
    (h : i ≠ j) :
    (sixStateMeasurement j).bornProb (sixStateState i s₁).toState o
      = (sixStateMeasurement j).bornProb (sixStateState i s₂).toState o := by
  rw [sixState_bornProb_mismatchedBasis i j s₁ o h, sixState_bornProb_mismatchedBasis i j s₂ o h]

end AxQM
