/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CompletelyDepolarizingChannel

/-!
# Nielsen & Chuang, Exercise 10.11 (Operation elements mapping every state to `I/2`)

*(N&C p. 441.)*

Construct operation elements for a single-qubit operation mapping any rho to I/2.

## The formalisation

The channel asked for is the **completely depolarizing channel** — the `p = 1` case of the qubit
depolarizing channel `E(ρ) = (1-p)ρ + p(I/2)`. Its **operation elements** are the four *half-Paulis*
(N&C eq. 8.101):

`E₀ = ½ I`,   `E₁ = ½ X`,   `E₂ = ½ Y`,   `E₃ = ½ Z`.

The operator sum reproduces the qubit Pauli twirl
`∑ₖ Eₖ ρ Eₖ† = ¼(ρ + XρX + YρY + ZρZ) = (tr ρ / 2) I = I/2`
(using `tr ρ = 1`), and the completeness relation is `∑ₖ Eₖ† Eₖ = ¼·4·I = I` (each Pauli is a
self-adjoint involution), so `E` is a genuine trace-preserving quantum channel. The construction of
the operation elements, their completeness, and the operator-sum computation are in
`AxQM/Postulates/API/CompletelyDepolarizingChannel.lean`. This file states the consequences, in
terms of the predicate `IsChannel` and the state `maximallyMixedState`:

* `AxQM.completelyDepolarizingChannel_isChannel` — the completely depolarizing channel is a
  genuine **CPTP quantum channel** (`IsChannel`), certified by the operator-sum representation via
  the operator-sum ⟹ channel constructor (N&C Theorem 8.1). This is what makes "`{Eₖ}` is a valid
  quantum operation" a complete claim.
* `AxQM.completelyDepolarizingChannel_eq_maximallyMixedState` — the channel maps **every**
  state `ρ` to the completely randomized state `I/2` (`maximallyMixedState qubit`). This is the full
  content of the exercise: not merely that `I/2` is a fixed point (unitality), but that *all*
  information is discarded.

## Where the declarations are

* `AxQM/Postulates/API/CompletelyDepolarizingChannel.lean` — the operation elements
  `completelyDepolarizingKraus` (`= ½ σₖ`, the exercise's answer), the qubit Pauli twirl
  `sum_pauliFamilyOp_conj`, the **completeness relation** `completelyDepolarizingKraus_completeness`
  (`∑ₖ Eₖ† Eₖ = I`), the **operator sum** `completelyDepolarizingKraus_krausSum` (`∑ₖ Eₖ ρ Eₖ† =
  I/2`), and the state-map `completelyDepolarizingChannel`.
* `AxQM/NC/Ch10/Exercise10_11.lean` (this file) — the statements
  `completelyDepolarizingChannel_isChannel` and
  `completelyDepolarizingChannel_eq_maximallyMixedState`.

## Design notes

* **Strength of the statement.** The map is proved to send *every* state to `I/2`, not merely to
  fix `I/2` (which is the weaker unitality). The operation elements are given at full generality —
  the four half-Paulis — with no simplifying restriction on the input state.
* **Reuse.** The Pauli operators are the already-grounded qubit `X, Y, Z` observables, the twirl is
  the concrete matrix identity `Concrete.pauliConjSum_eq`, and the CPTP wrapper is the shared
  operator-sum ⟹ channel constructor `isChannel_of_kraus`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **The completely depolarizing qubit channel is a genuine CPTP quantum channel** (`IsChannel`).
Its operation elements `Eₖ = ½ σₖ` (`completelyDepolarizingKraus`) obey the completeness relation
`∑ₖ Eₖ† Eₖ = I` (`completelyDepolarizingKraus_completeness`), so the operator-sum ⟹ channel
constructor (Nielsen & Chuang Theorem 8.1, trace-preserving direction) exhibits the operator sum
`ρ ↦ ∑ₖ Eₖ ρ Eₖ†` as a completely-positive trace-preserving map. -/
theorem completelyDepolarizingChannel_isChannel : IsChannel completelyDepolarizingChannel :=
  isChannel_of_kraus completelyDepolarizingKraus completelyDepolarizingKraus_completeness
    fun _ => rfl

/-- **The completely depolarizing channel replaces every state with `I/2`** (Nielsen & Chuang,
Exercise 10.11): for every qubit state `ρ`, `E(ρ) = maximallyMixedState qubit = I/2`, the completely
randomized state. This is the full content of the exercise — all input information is discarded —
and follows from the operator-sum computation `completelyDepolarizingKraus_krausSum`
(`∑ₖ Eₖ ρ Eₖ† = I/2`, the qubit Pauli twirl at `tr ρ = 1`). -/
theorem completelyDepolarizingChannel_eq_maximallyMixedState (ρ : State qubit) :
    completelyDepolarizingChannel ρ = maximallyMixedState qubit := by
  apply State.ext
  rw [completelyDepolarizingChannel_op, completelyDepolarizingKraus_krausSum]

end AxQM
