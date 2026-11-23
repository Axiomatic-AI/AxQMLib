/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MaxEntropyTwirl

/-!
# N&C Exercise 11.19 — the depolarizing twirl and the uniqueness of the maximal-entropy state

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.19, p. 517.

The exercise has two parts:

1. **The twirl.** Show that there exist unitaries `Uⱼ` and a probability distribution `pⱼ` such
   that for **any** matrix `A`, `∑ⱼ pⱼ Uⱼ A Uⱼ† = tr(A) · I/d`, where `d` is the dimension of the
   space.
2. **Uniqueness of the maximal-entropy state.** Use the twirl together with the *strict* concavity
   of the von Neumann entropy to give an alternate proof that the completely mixed state `I/d` is
   the **unique** state of maximal entropy.

## Where the formalisation lives

Part 1's operator identity — "for **any** matrix `A`, `∑ⱼ pⱼ Uⱼ A Uⱼ† = tr(A) I/d`" — is pure
linear algebra. It is `LinearIsometryEquiv.exists_conjStarAlgEquiv_oneDesign` in `ToMathlib/`, the
existential form of the depolarizing `1`-design
`OrthonormalBasis.sum_conjStarAlgEquiv_depolarizingUnitary` (a uniform average over the
`2^d·d!` sign-diagonal/permutation unitaries `Pσ Sε`).

The twirl lifted to states, and the maximal-entropy deduction, are in
`AxQM/Postulates/API/MaxEntropyTwirl.lean`. They re-prove the extremal-entropy characterization
(`State.eq_maximallyMixed_of_vonNeumannEntropy_eq_log_finrank`, in
`AxQM/Postulates/API/EntropyExtremal.lean`) and use the concavity results of Exercise 11.18.

The declarations (all in `AxQM/Postulates/API/MaxEntropyTwirl.lean`):

* `AxQM.exists_randomUnitary_twirl_eq_maximallyMixed` — **part 1**, physics form: there is
  a finite family of unitary evolutions `Uⱼ` and a probability distribution `pⱼ` such that twirling
  *any* state `ρ` yields `∑ⱼ pⱼ Uⱼ ρ Uⱼ† = I/d` (a density operator has unit trace, so the general
  `tr(A) I/d` specialises to `I/d`).
* `AxQM.State.vonNeumannEntropy_le_maximallyMixed` — **part 2, maximality**: every state
  has entropy `S(ρ) ≤ S(I/d)`.
* `AxQM.State.eq_maximallyMixed_of_vonNeumannEntropy_eq` — **part 2, uniqueness**: a state
  whose entropy equals `S(I/d)` *is* `I/d`.
* `AxQM.State.maximallyMixedState_unique_maxEntropy` — the **main statement**: `ρ` maximises the
  von Neumann entropy (`S(σ) ≤ S(ρ)` for all `σ`) **iff** `ρ = I/d`.

## The alternate proof

This is genuinely N&C's *alternate* proof, distinct from the library's other route (which reads
`I/d` off the maximiser of the Shannon entropy of the eigenvalues). For any state `ρ`, the twirl
gives the mixture `I/d = ∑ⱼ pⱼ Uⱼ ρ Uⱼ†`. Concavity of the entropy together with its unitary
invariance (`S(Uⱼ ρ Uⱼ†) = S(ρ)`) yields `S(I/d) ≥ ∑ⱼ pⱼ S(Uⱼ ρ Uⱼ†) = S(ρ)` — maximality. For
uniqueness, `S(ρ) = S(I/d)` saturates the concavity inequality, so **strict** concavity (Exercise
11.18) forces all the `Uⱼ ρ Uⱼ†` to coincide; their common value is their average `I/d`, so
`Uⱼ ρ Uⱼ† = I/d` for some `j`, whence `ρ = Uⱼ† (I/d) Uⱼ = I/d`.
-/
