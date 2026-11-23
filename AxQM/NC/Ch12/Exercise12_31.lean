/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.Problem12_1
import AxQM.Core.HolevoChiBound
import AxQM.Postulates.API.PureMarginalEntropy

/-!
# Nielsen & Chuang, Exercise 12.31 — `S(ρ)` bounds Eve's mutual information

*(N&C p. 594.)*

Show S(rho) bounds Eve's mutual info by giving Eve full control of channel.

**Context (N&C §12.6.5, Lemma 12.19).** Alice and Bob share a (possibly noisy) state `ρ` on their
joint system `AB`, obtained by transmitting halves of EPR pairs over a channel. Lemma 12.19 shows
high fidelity of `ρ` to `|β₀₀⟩^{⊗n}` forces small `S(ρ)`, and N&C then asserts that "by Holevo's
bound, `S(ρ)` is an upper bound on the information accessible to Eve, resulting from Alice and Bob's
measurements of `ρ`." This exercise asks *why* the entropy `S(ρ)` of Alice and Bob's own state
should bound what a third party, Eve, can learn.

**The argument (worst case: Eve controls the channel).** Give Eve the greatest possible advantage:
attribute *all* of the environment interacting with the channel to Eve, so that the global state of
`AB` together with Eve's system `E` is **pure** (`ψ : PureState (AB ⊗ E)` with `ρ = tr_E |ψ⟩⟨ψ|` its
left marginal). This is the worst case — any real environment is a restriction of it. Then:

* Eve's marginal is `ρ_E = tr_{AB} |ψ⟩⟨ψ|`, and because `|ψ⟩` is pure the two marginals are
  isentropic: `S(ρ_E) = S(ρ)` (`PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`,
  N&C Theorem 11.8 via the Schmidt decomposition). This is where "giving Eve all control" enters.
* Whatever Alice and Bob's measurements produce as the key value `k` (with distribution `pₖ`), Eve
  is left holding a conditional state `σₖ`, and consistency forces the ensemble to reconstruct her
  marginal, `∑ₖ pₖ σₖ = ρ_E`. For *any* measurement Eve performs on her system, the classical
  mutual information between the key `k` and her outcome is bounded by the Holevo χ of her ensemble
  (`holevoBound_of_chi_monotone`, N&C eq. 12.6), and `χ ≤ S(∑ₖ pₖ σₖ) = S(ρ_E)`
  (`State.holevoChi_le_vonNeumannEntropy_mix`, since the average entropy `∑ₖ pₖ S(σₖ) ≥ 0`).

Chaining these, Eve's mutual information with the key is at most `χ ≤ S(ρ_E) = S(ρ)`. Because the
bound holds for every ensemble `{pₖ, σₖ}` decomposing `ρ_E` and every measurement, it bounds *any*
strategy Eve may employ — which is the content the exercise asks us to make explicit.

The statement uses `Real.mutualInfo`, `Measurement.bornProb`, `State.holevoChi`,
`State.vonNeumannEntropy`, and the marginals `State.reducedLeft`/`reducedRight`. It rests on the
Holevo bound (Problem 12.1 in `AxQM/NC/Ch12/Problem12_1.lean`, Theorem 12.1 in
`AxQM/NC/Ch12/Theorem12_1.lean`), the entropy bound on χ
(`AxQM/Core/HolevoChiBound.lean`), and the pure-marginal entropy equality
(`AxQM/Postulates/API/PureMarginalEntropy.lean`); the proof below assembles the eavesdropping
conclusion.
-/

noncomputable section

namespace AxQM

/-- **N&C Exercise 12.31 — `S(ρ)` bounds Eve's mutual information with the key.**

Assume the worst about the eavesdropper Eve by giving her all control of the channel: the global
state of Alice and Bob's system `AB` and Eve's system `E` is a *pure* state `ψ`, whose left marginal
is Alice and Bob's shared state `ρ = tr_E |ψ⟩⟨ψ|`. Let `{pₖ, σₖ}` be Eve's ensemble of conditional
states associated with the possible key values `k` produced by Alice and Bob's measurements; by
consistency it reconstructs Eve's marginal, `∑ₖ pₖ σₖ = tr_{AB} |ψ⟩⟨ψ|`. Then for *any* measurement
`m` Eve performs on her system, the classical mutual information between the key `k` and her outcome
is bounded by `S(ρ)`:

`H(K : Eve) ≤ S(ρ)`.

The proof chains the Holevo bound `H(K : Eve) ≤ χ({pₖ, σₖ})` (`holevoBound_of_chi_monotone`), the
entropy bound `χ ≤ S(∑ₖ pₖ σₖ) = S(ρ_E)` (`State.holevoChi_le_vonNeumannEntropy_mix`), and the
purity-driven isentropy of the two marginals `S(ρ_E) = S(ρ)`
(`PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`). Holding for every ensemble decomposing
`ρ_E` and every measurement, it bounds any strategy Eve may employ. -/
theorem PureState.eavesdropper_mutualInfo_le_vonNeumannEntropy
    {AB E : QSystem} (ψ : PureState (AB.compose E))
    {ρ : State AB} (hρ : ψ.toState.reducedLeft = ρ)
    {r : ℕ} [NeZero r] {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (σ : κ → State E) (hσ : State.mix p hp hsum σ = ψ.toState.reducedRight)
    (m : Measurement (Fin r) E) :
    (Real.mutualInfo fun xy => p xy.1 * m.bornProb (σ xy.1) xy.2) ≤ ρ.vonNeumannEntropy :=
  calc (Real.mutualInfo fun xy => p xy.1 * m.bornProb (σ xy.1) xy.2)
      ≤ State.holevoChi p hp hsum σ := holevoBound_of_chi_monotone p hp hsum σ m
    _ ≤ (State.mix p hp hsum σ).vonNeumannEntropy :=
        State.holevoChi_le_vonNeumannEntropy_mix p hp hsum σ
    _ = ψ.toState.reducedRight.vonNeumannEntropy := by rw [hσ]
    _ = ψ.toState.reducedLeft.vonNeumannEntropy :=
        (ψ.vonNeumannEntropy_reducedLeft_eq_reducedRight).symm
    _ = ρ.vonNeumannEntropy := by rw [hρ]

end AxQM
