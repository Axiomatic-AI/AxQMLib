/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GeneralizedDepolarizingChannel

/-!
# Nielsen & Chuang, Exercise 8.19 (Generalized depolarizing channel)

*(N&C p. 379.)*

Find an operator-sum representation for the generalized depolarizing channel on d-dim Hilbert space.

## The formalisation

The **generalized depolarizing channel** (N&C eq. 8.106) on a `d`-dimensional system replaces the
state with the completely mixed state `I/d` with probability `p`, and leaves it untouched otherwise:
`E(ρ) = p (I/d) + (1 - p) ρ`.
The exercise asks for an **operator-sum representation** `E(ρ) = ∑ₖ Eₖ ρ Eₖ†` with
`∑ₖ Eₖ† Eₖ = I`.

The **answer**: the `d`-dimensional generalization of the qubit twirl
`I/2 = (ρ + XρX + YρY + ZρZ)/4` (N&C eq. 8.101). The completely-depolarizing part `ρ ↦ (tr ρ) I/d`
is the uniform average of conjugations by the `2ᵈ d!` **depolarizing-design unitaries** `Uⱼ`
(sign flips × basis permutations), so the operation elements are

`E₀ = √(1-p) · I`,   `E_{(ε,σ)} = √(p / 2ᵈd!) · U_{(ε,σ)}`   (one per depolarizing unitary),

a manifestly *random-unitary* representation (mixture of the unitaries `Uⱼ` with a probability
distribution). This reproduces `E(ρ) = ∑ₖ Eₖ ρ Eₖ†` and obeys the completeness relation
`∑ₖ Eₖ† Eₖ = I`.

The operator-sum construction — the operation elements `genDepolarizingKraus`, the representation
`genDepolarizingChannel_op_eq_krausSum` (`E(ρ) = ∑ₖ Eₖ ρ Eₖ†`), and the completeness relation
`genDepolarizingKraus_completeness` (`∑ₖ Eₖ† Eₖ = I`) — is in
`AxQM/Postulates/API/GeneralizedDepolarizingChannel.lean`. This file contains the consequence
that the channel is a genuine quantum channel (`IsChannel`):

* `AxQM.genDepolarizingChannel_isChannel` — the generalized depolarizing channel is a
  genuine **CPTP quantum channel** (`IsChannel`), certified by the operator-sum representation via
  the operator-sum ⟹ channel constructor (N&C Theorem 8.1). This is what makes "`{Eₖ}` is an
  operator-sum representation of the channel" a complete claim: the elements form a *bona fide*
  quantum operation.

## Supporting results

* `AxQM/Postulates/API/GeneralizedDepolarizingChannel.lean` — the channel
  `genDepolarizingChannel`, its operation elements `genDepolarizingKraus`, the **operator-sum
  representation** `genDepolarizingChannel_op_eq_krausSum` and **completeness relation**
  `genDepolarizingKraus_completeness` (the exercise's answer), built on the twirl
  `OrthonormalBasis.sum_conjStarAlgEquiv_depolarizingUnitary`.

## Notes on the statement

* The channel is stated at full generality: arbitrary dimension `d ≥ 1` and
  arbitrary probability `0 ≤ p ≤ 1` (the physical range for which the operation elements are real
  and the map is completely positive), with no simplifying hypothesis. The operator-sum identity
  reproduces `E(ρ) = p (I/d) + (1-p) ρ` exactly.
* **The depolarizing `1`-design.** The completely-depolarizing average `∑ⱼ Uⱼ ρ Uⱼ†/2ᵈd!
  = (tr ρ) I/d` is exactly `OrthonormalBasis.sum_conjStarAlgEquiv_depolarizingUnitary`,
  so no bespoke operator basis is introduced. The random-unitary flavour matches the qubit Pauli
  channel of Problem 8.3 (`pauliChannel`), of which this is the `d`-dimensional analogue.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {d : ℕ}

/-- **The generalized depolarizing channel is a genuine CPTP quantum channel** (`IsChannel`). Its
operator-sum representation `E(ρ) = ∑ₖ Eₖ ρ Eₖ†` (`genDepolarizingChannel_op_eq_krausSum`) with the
completeness relation `∑ₖ Eₖ† Eₖ = I` (`genDepolarizingKraus_completeness`) satisfies the hypotheses
of the operator-sum ⟹ channel constructor (Nielsen & Chuang Theorem 8.1, trace-preserving
direction). -/
theorem genDepolarizingChannel_isChannel [NeZero d] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsChannel (genDepolarizingChannel d p hp0 hp1) :=
  isChannel_of_kraus (genDepolarizingKraus d p) (genDepolarizingKraus_completeness p hp0 hp1)
    (genDepolarizingChannel_op_eq_krausSum p hp0 hp1)

end AxQM
