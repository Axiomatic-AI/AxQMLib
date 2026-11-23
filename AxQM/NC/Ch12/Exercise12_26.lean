/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BB84
import AxQM.NC.Ch4.Exercise4_1

/-!
# Nielsen & Chuang, Exercise 12.26 — BB84 measurement outcomes

*(N&C p. 588.)*

BB84: when b'_k != b_k, a'_k random & uncorrelated with a_k; when equal, a'_k=a_k.

In BB84 (N&C §12.6.3) Alice encodes data bit `a_k` in a basis chosen by bit `b_k`: `|ψ_{a0}⟩` is the
computational-basis state `|a⟩` and `|ψ_{a1}⟩` the Hadamard-basis state `|±⟩` (eqs. 12.180–12.183).
Bob measures each qubit in the `Z` (`b′ = 0`) or `X` (`b′ = 1`) basis, obtaining his bit `a′_k`. The
whole exercise is the qubit instance of the stabilizer measurement-update dichotomy (N&C §10.5.3,
formalised in `AxQM/Postulates/API/StabilizerMeasurement.lean`), applied to the four BB84 states:

* **Matched bases (`b′ = b`):** `|ψ_{ab}⟩` is the `(-1)^a`-eigenstate of the measured observable,
  so the outcome is *deterministic* and equals `a` — `bb84_bornProb_matchedBasis`
  (`p(a′ = a) = 1`).
* **Mismatched bases (`b′ ≠ b`):** the measured observable *anticommutes* with the basis that
  prepared `|ψ_{ab}⟩`, so `⟪measured observable⟫ = 0` and both outcomes are equiprobable —
  `bb84_bornProb_mismatchedBasis` (`p(a′ = j) = 1/2` for each `j`). The probability does not depend
  on `a`: `bb84_bornProb_mismatchedBasis_uncorrelated` — `a′_k` is "completely uncorrelated with
  `a_k`".

The reusable protocol objects — `bb84State`, `bb84Observable`, `bb84Measurement`, and the
arbitrary-eigenvalue vanishing-expectation lemma
`Observable.expectation_eq_zero_of_anticomm_eigenstate` — are in
`AxQM/Postulates/API/BB84.lean`. This file states the Nielsen & Chuang probabilities, in terms
of `Measurement.bornProb`. The "noiseless channel with no eavesdropping" is exactly
the assumption that Bob measures Alice's undisturbed state, which these statements model; the
"randomness" of `a′_k` is `p = 1/2` and the "no correlation with `a_k`" is the independence of the
outcome distribution from `a`.
-/

noncomputable section

namespace AxQM

/-- **Alice's state `|ψ_{ab}⟩` is the `(-1)^a`-eigenstate of its basis observable.** For `b = 0`
this is `Z|0⟩ = |0⟩`, `Z|1⟩ = −|1⟩` (`qubitKet0_hasEigenstate_pauliZ`,
`qubitBasis_one_hasEigenstate_pauliZ`); for `b = 1`, `X|+⟩ = |+⟩`, `X|−⟩ = −|−⟩`
(`qubitPlus_hasEigenstate_pauliX`, `qubitMinus_hasEigenstate_pauliX`) — the Pauli-eigenstate content
of N&C Exercise 4.1. -/
theorem bb84State_hasEigenstate (a b : Fin 2) :
    (bb84Observable b).HasEigenstate (signEigenvalue a) (bb84State a b) := by
  fin_cases a <;> fin_cases b
  · exact qubitKet0_hasEigenstate_pauliZ
  · exact qubitPlus_hasEigenstate_pauliX
  · exact qubitBasis_one_hasEigenstate_pauliZ
  · exact qubitMinus_hasEigenstate_pauliX

/-- **Matched bases: Bob recovers Alice's bit with certainty, `a′ = a`.** When Bob measures in the
same basis Alice prepared (`b′ = b`), the outcome equals Alice's data bit `a` with probability one:
`p(a′ = a) = 1`. Because `|ψ_{ab}⟩` is the `(-1)^a`-eigenstate of `bb84Observable b`, the outcome is
deterministic — the `a = 0` (`+1`) and `a = 1` (`−1`) sub-cases are the deterministic-outcome rules
`Observable.bornProb_signMeasurement_plus_of_hasEigenstate_one` and
`..._minus_of_hasEigenstate_neg_one` of N&C §10.5.3. This is N&C's "when `b′_k = b_k`,
`a′_k = a_k`". -/
theorem bb84_bornProb_matchedBasis (a b : Fin 2) :
    (bb84Measurement b).bornProb (bb84State a b).toState a = 1 := by
  rw [bb84Measurement_eq]
  fin_cases a
  · refine Observable.bornProb_signMeasurement_plus_of_hasEigenstate_one _ _ _ ?_
    simpa using bb84State_hasEigenstate 0 b
  · refine Observable.bornProb_signMeasurement_minus_of_hasEigenstate_neg_one _ _ _ ?_
    simpa using bb84State_hasEigenstate 1 b

/-- **Mismatched bases: Bob's result is random, `p(a′ = j) = 1/2`.** When Bob measures in the wrong
basis (`b′ ≠ b`), each outcome `j ∈ {0, 1}` occurs with probability exactly `1/2`. Because
`|ψ_{ab}⟩` is a nonzero (`signEigenvalue a`) eigenstate of `bb84Observable b` while the measured
`bb84Observable b′` anticommutes with it (`bb84Observable_op_anticomm`), the measured observable has
vanishing expectation; each outcome is then a fair coin via the shared random-outcome rules
`Observable.bornProb_signMeasurement_plus_of_anticomm_eigenstate` /
`..._minus_of_anticomm_eigenstate` (the arbitrary-eigenvalue form of N&C §10.5.3). This is N&C's
"when `b′_k ≠ b_k`, `a′_k` is random". -/
theorem bb84_bornProb_mismatchedBasis (a b b' j : Fin 2) (h : b ≠ b') :
    (bb84Measurement b').bornProb (bb84State a b).toState j = 1 / 2 := by
  rw [bb84Measurement_eq]
  fin_cases j
  · exact Observable.bornProb_signMeasurement_plus_of_anticomm_eigenstate _ (bb84Observable b) _ _
      (signEigenvalue_ne_zero a) (bb84State_hasEigenstate a b)
      (bb84Observable_op_anticomm (Ne.symm h))
  · exact Observable.bornProb_signMeasurement_minus_of_anticomm_eigenstate _ (bb84Observable b) _ _
      (signEigenvalue_ne_zero a) (bb84State_hasEigenstate a b)
      (bb84Observable_op_anticomm (Ne.symm h))

/-- **Mismatched bases: `a′_k` is completely uncorrelated with `a_k`.** When Bob measures in the
wrong basis, the distribution of his result bit `a′` is independent of Alice's data bit `a`: for any
two data bits `a₁, a₂` and any outcome `j`, the probabilities agree. Both equal `1/2`
(`bb84_bornProb_mismatchedBasis`), so Bob's outcome carries no information about `a` — N&C's
"completely uncorrelated with `a_k`". -/
theorem bb84_bornProb_mismatchedBasis_uncorrelated (a₁ a₂ b b' j : Fin 2) (h : b ≠ b') :
    (bb84Measurement b').bornProb (bb84State a₁ b).toState j
      = (bb84Measurement b').bornProb (bb84State a₂ b).toState j := by
  rw [bb84_bornProb_mismatchedBasis a₁ b b' j h, bb84_bornProb_mismatchedBasis a₂ b b' j h]

end AxQM
