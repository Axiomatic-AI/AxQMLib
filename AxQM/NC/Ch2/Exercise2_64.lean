/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.StateDiscrimination

/-!
# Nielsen & Chuang, Exercise 2.64

Construct a POVM distinguishing linearly independent states with certainty when E_i occurs.

The exercise asks for a **POVM** — a set of positive operators
summing to the identity (N&C §2.2.6) — whose measurement statistics unambiguously discriminate a
family of quantum states. The formalisation uses pure states `PureState` and
the POVM's Born rule: the "probability of outcome `i` on state `ρ`" is `POVM.toPMF ρ.op i`, and
the certainty conclusion is that this probability vanishes on every state but the intended one.

## The formalisation

Indexing the `m` informative outcomes by an arbitrary `Fintype ι` and the single inconclusive
outcome by adjoining `none`, the outcome set is `Option ι` (so `Option (Fin m)` recovers the
`m + 1` elements of the exercise).

* `AxQM.distinguishingPOVM` (in `AxQM/Postulates/API/StateDiscrimination.lean`)
  — the POVM `{E₁, …, E_{m+1}}` as a `POVM (Option ι) ℂ S.space` for a family of pure states
  `ψ : ι → PureState S`. Its mere construction discharges the POVM obligations (each effect
  positive; effects sum to `1`), so its well-formedness *is* the "construct a POVM" half.
* `AxQM.distinguishingPOVM_prob_eq_zero` — the Born probability of the informative
  outcome `some i` on a different state `ψ j` (`j ≠ i`) is `0`: outcome `some i` cannot occur
  unless the input was `ψ i`.
* `AxQM.distinguishingPOVM_prob_pos` — the Born probability of outcome `some i` on its
  own state `ψ i` is strictly positive, N&C's explicit requirement `⟨ψᵢ|Eᵢ|ψᵢ⟩ > 0`. (Requires
  the state vectors to be linearly independent.)
* `AxQM.distinguishingPOVM_certain` — the exercise's conclusion: if outcome `some i` has
  nonzero probability on state `ψ j`, then `j = i`. Hence observing `some i` tells Bob "with
  certainty that he was given the state `|ψᵢ⟩`".

## Design notes

* **POVM, not a full measurement.** N&C's §2.2.6 defines a POVM as *effects only* (positive
  operators summing to `1`), deliberately discarding the post-measurement state; the exercise
  asks for exactly this. The formalisation therefore builds a `POVM` and reads the outcome
  probabilities off `POVM.toPMF`, rather than manufacturing measurement operators `Mᵢ = √Eᵢ`
  (which would demand an operator square root the exercise never needs).
* **The construction.** The linear-algebra core lives in
  `ToMathlib/Analysis/InnerProductSpace/StateDiscrimination.lean` as `POVM.distinguishing`. For
  each `i` it takes the *detector vector* `POVM.detector` — the component of `ψᵢ` orthogonal to
  the span of the other states — which is orthogonal to every `ψⱼ` (`j ≠ i`) and, by linear
  independence, nonzero; the informative effect is a small positive multiple of the rank-one
  projector onto it, and the inconclusive effect `1 - ∑ᵢ Eᵢ` is positive by the choice of scale.
-/
