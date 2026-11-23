/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ChannelHolevoChiPureCard

/-!
# N&C Exercise 12.11 — the HSW χ maximum is achieved by `≤ d²` pure-state ensembles

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 12.11, p. 555.

The Holevo–Schumacher–Westmoreland theorem (Theorem 12.8) computes the product-state capacity of a
channel `E` as its **Holevo χ quantity** (eq. (12.71), the maximum over all input ensembles)

`χ(E) = max_{{pⱼ, ρⱼ}} [ S(E(∑ⱼ pⱼ ρⱼ)) − ∑ⱼ pⱼ S(E(ρⱼ)) ]`.

The maximization is a priori over an unbounded set. Exercise 12.11 asks to tame it in two steps:

1. **Pure states suffice** — the maximum may be achieved using an ensemble of *pure* states;
2. **`≤ d²` suffice** — it further suffices to consider ensembles of at most `d²` pure states,
   where `d` is the dimension of the channel input.

## The formalisation

The channel Holevo χ is `channelHolevoChi E = sSup (channelHolevoChiSet E)`, the supremum of the
output-ensemble Holevo χ over *all* finite input ensembles (`AxQM/Core/ChannelHolevoChi.lean`).

* **Part 1** is the identity `channelHolevoChi E = sSup (channelHolevoChiPureSet E)`
  (`channelHolevoChi_eq_sSup_pureEnsemble`), where `channelHolevoChiPureSet E` restricts the
  supremum to **pure-state** input ensembles: restricting the domain to pure ensembles does not
  lower the supremum. The content — the eigenensemble refinement, using that a channel is affine
  over mixtures and the von Neumann entropy is concave — is the development in
  `AxQM/Core/ChannelHolevoChiPure.lean`.

* **Part 2** is the identity `channelHolevoChi E = sSup (channelHolevoChiPureLeCardSet E)`
  (`channelHolevoChi_eq_sSup_pureLeCardEnsemble`), where `channelHolevoChiPureLeCardSet E` further
  restricts to pure-state ensembles of at most `d² = S.dim ^ 2` elements: the supremum is *still*
  attained. The content — the rank-one projections `|ψⱼ⟩⟨ψⱼ|` are unit-trace self-adjoint operators
  (a `d²`-real-dimensional space), so a hyperplane-refined Carathéodory reduction cuts any pure
  ensemble down to `≤ d²` states without decreasing the output χ — is the development in
  `AxQM/Core/ChannelHolevoChiPureCard.lean`, resting on the `ToMathlib/` convex-geometry core
  `exists_reduced_weights_le_finrank` and the dimension count
  `finrank_real_selfAdjoint_continuousLinearMap`. The `d²` bound is tight (self-adjoint operators,
  not the full `2d²`-real-dimensional operator space), matching N&C.

The statements use `channelHolevoChi`, `channelHolevoChiPureSet`,
`channelHolevoChiPureLeCardSet`, and the channel predicate `IsChannel`. The eigenensemble
refinement, the self-adjoint operator support reduction and the real-trace functional are in
`AxQM/Core/` and `ToMathlib/`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.3.2, Theorem 12.8, eq. (12.71); Exercise 12.11.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang Exercise 12.11, Part 1** (the HSW χ maximum is achieved by pure-state
ensembles): for a channel `E`, the Holevo χ quantity `χ(E)` — the maximum in eq. (12.71) over *all*
input ensembles — equals the supremum of the output Holevo χ over **pure-state** input ensembles
alone,

`χ(E) = sSup (channelHolevoChiPureSet E)`.

Restricting the maximization to pure ensembles is harmless: any ensemble `{pⱼ, ρⱼ}` is refined into
the pure ensemble `{pⱼ λⱼₖ, |ψⱼₖ⟩}` given by the eigen-decompositions `ρⱼ = ∑ₖ λⱼₖ |ψⱼₖ⟩⟨ψⱼₖ|`,
which has the same mixture `∑ⱼ pⱼ ρⱼ` and, by concavity of the entropy along each decomposition and
affineness of the channel over mixtures, output χ at least as large. Discharged by the reusable
reduction `channelHolevoChi_eq_sSup_channelHolevoChiPureSet`
(`AxQM/Core/ChannelHolevoChiPure.lean`). -/
theorem channelHolevoChi_eq_sSup_pureEnsemble {E : State S → State S} (hE : IsChannel E) :
    channelHolevoChi E = sSup (channelHolevoChiPureSet E) :=
  channelHolevoChi_eq_sSup_channelHolevoChiPureSet hE

/-- **Nielsen & Chuang Exercise 12.11, Part 2** (the HSW χ maximum is achieved by an ensemble of
`≤ d²` pure states): for a channel `E`, the Holevo χ quantity `χ(E)` — the maximum in eq. (12.71)
over *all* input ensembles — equals the supremum of the output Holevo χ over **pure-state** input
ensembles of at most `d² = S.dim ^ 2` elements, where `d` is the dimension of the channel input:

`χ(E) = sSup (channelHolevoChiPureLeCardSet E)`.

Combining Part 1 with a cardinality reduction: the rank-one projections `|ψⱼ⟩⟨ψⱼ|` of a pure
ensemble are unit-trace self-adjoint operators, points of the `d²`-real-dimensional space of
Hermitian operators lying on the affine hyperplane `{re ∘ tr = 1}`; a hyperplane-refined
Carathéodory reduction cuts the ensemble to support `≤ d²` while preserving the output mixture and
not increasing the average output entropy, so the output χ does not decrease. Discharged by the
reusable reduction
`channelHolevoChi_eq_sSup_channelHolevoChiPureLeCardSet`
(`AxQM/Core/ChannelHolevoChiPureCard.lean`). -/
theorem channelHolevoChi_eq_sSup_pureLeCardEnsemble {E : State S → State S} (hE : IsChannel E) :
    channelHolevoChi E = sSup (channelHolevoChiPureLeCardSet E) :=
  channelHolevoChi_eq_sSup_channelHolevoChiPureLeCardSet hE

end AxQM
