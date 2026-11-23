/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasurementSimulation
import AxQM.Postulates.API.EvolutionTensorHom
import AxQM.Postulates.API.SchmidtReducedSpectrum
import AxQM.Postulates.API.MeasurementTransportSpectrum
import AxQM.Postulates.API.SchmidtDecomposition
import AxQM.NC.Ch2.Exercise2_80
import AxQM.Core.LOCCProtocol

/-!
# Nielsen & Chuang, Proposition 12.14 (LOCC reduction)

LOCC transform reducible to Alice-measure, send j, Bob-unitary protocol.

## Statement

The proposition's claim is a **reduction** of *any* finite-round two-way LOCC protocol to the
single Alice-measure / Bob-unitary form. The reduction theorem `OneWayLOCC.of_transforms_pureState`
(and its N&C-phrasing corollary `OneWayLOCC.of_exists_transforms_pureState`) at the **bottom of
this file** proves it in full: every finite-round two-way LOCC protocol transforming a bipartite
pure state reduces to the one-way Alice-measure / Bob-unitary form.

The reduction is stated over a genuine formal protocol type, defined in
`AxQM/Core/LOCCProtocol.lean`:

* `LOCCProtocol A B` — a finite-round two-way LOCC protocol on `A ⊗ B` (a tree of local measurements
  and unitaries by either party, interleaved with classical communication: the branching
  continuation `k` is the outcome-dependence);
* `LOCCProtocol.Transforms P ρ σ` — deterministic transformation semantics: every
  nonzero-probability branch of `P` on `ρ` ends in `σ` (N&C's "`ρ → σ` by LOCC regardless of
  outcome");
* `LOCCProtocol.oneWay`/`OneWayLOCC` — the single Alice-measurement / Bob-unitary target form, shown
  to be a genuine protocol (`OneWayLOCC.exists_transforms`), i.e. the reduced-state
  `State.LOCCConvertible` of Theorem 12.15 lifted to joint states.

The reduction theorem is then

> `LOCCProtocol.Transforms P ρ σ → OneWayLOCC ρ σ`,

an induction on the protocol tree `P` whose five constructor cases are exactly five closure
properties of `OneWayLOCC`.

## Outline of the proof of the reduction

1. the `LOCCProtocol` type, the `Transforms` semantics and the `OneWayLOCC` target form
   (`AxQM/Core/LOCCProtocol.lean`).
2. the four *deterministic / Alice-round* closure cases: `OneWayLOCC.refl`
   (`terminal`), `prepend_aliceUnitary`, `prepend_bobUnitary` (`aliceUnitary`/`bobUnitary`), and
   `prepend_aliceMeasure` — the `aliceMeasure` case, combining Alice's rounds into one measurement
   (the dependent Exercise 2.57 cascade).
3. the fifth, `bobMeasure` closure case in the **swap-symmetric normal form**
   (`OneWayLOCC.prepend_bobMeasure_of_swapSymmetric`, below): simulate Bob's measurement by Alice's
   (the crux) and peel the resulting local unitary off with (2), reducing to an Alice round.
4. lift (3) off the swap-symmetric normal form to an *arbitrary* bipartite pure state `S ⊗ T` — the
   Schmidt-basis identification of N&C's Eq. (12.159), routed through the **reduced spectra** (no
   SWAP exists on a genuine `S ⊗ T` with `S ≠ T`), in stages:
   * the reduced-spectrum bridges — a pure state's two marginals are isospectral
     (`ρ_A ≅ ρ_B`) and Schmidt-coefficient equality ⟺ same reduced spectrum (Ex. 12.22)
     (`AxQM/Postulates/API/SchmidtReducedSpectrum.lean`).
   * the post-measurement reduced-operator conjugation identities
     (`Bob`'s marginal `= Mⱼ ρ_B Mⱼ† / p`, `Alice`'s `= Nⱼ ρ_A Nⱼ† / p`,
     `AxQM/Postulates/API/ReducedStateOneFactor.lean`).
   * the general crux and `bobMeasure` closure case in the swap-free form
     (`Measurement.exists_localEvolution_postMeasurement_onRight_of_reducedSpectrum` and
     `OneWayLOCC.prepend_bobMeasure_of_aliceSimulates`, below), which isolate the construction of
     Alice's simulating `{Nⱼ}` as an explicit hypothesis (Alice's measurement matches Bob's Born
     probabilities and its post-measurement marginal is isospectral to Bob's).
   * the linear-algebra core of N&C's `|kᴬ⟩↔|kᴮ⟩` identification: the **cross-synthesis
     partial isometry** `W = ∑ᵢ |aᵢ⟩⟨bᵢ|` of two orthonormal families, with `W bᵢ = aᵢ`,
     `W† W`/`W W†` the span projectors, and the diagonal intertwining `W ∘ D_b = D_a ∘ W`
     (`InnerProductSpace.crossSynthesis`,
     `ToMathlib/Analysis/InnerProductSpace/PartialIsometryOrthonormal.lean`). This is the partial
     isometry `W` used below.
   * the simulating Alice measurement `{Nⱼ}`, built from `W` and the Schmidt data:
     the transported POVM `Measurement.transportPOVM` (effects `W Mⱼ† Mⱼ W†` plus
     the completeness caveat `1 - W W†`), Alice's square-root measurement
     `Measurement.ofPOVM (mB.transportPOVM W hW)` (with `Nⱼ = √(W Mⱼ† Mⱼ W†)`, avoiding the
     dimension-mismatch pitfall of transporting `Mⱼ` naïvely), and the discharge of the three
     simulation facts — **exact** Born-probability matching
     (`Measurement.bornProb_onLeft_ofPOVM_transportPOVM_eq`, `hprob`), the caveat's **zero**
     probability (`Measurement.bornProb_onLeft_ofPOVM_transportPOVM_none_eq_zero`, `hzero` — Alice's
     marginal lives on her Schmidt support `= range (W W†)`, so `1 - W W†` never fires), and the
     post-measurement marginal **isospectrality**
     (`PureState.sameNonzeroSpectrum_transport_postMeasurement_marginal`, `hspec`). These are
     assembled — through the abstract simulation closure — into the unconditional
     `OneWayLOCC.prepend_bobMeasure` (below), the `bobMeasure` induction case with no simulation
     hypotheses.
5. the induction over protocol depth assembling (2)–(4) into the reduction theorem
   `OneWayLOCC.of_transforms_pureState` (carrying purity through the branches, since the
   `bobMeasure` simulation is a pure-state fact) — one case per `LOCCProtocol` constructor, each
   discharged by the matching `OneWayLOCC` closure lemma.

## The crux (the key ingredient of step 5)

The load-bearing linear-algebra fact of N&C's proof (Eq. (12.159)): a measurement Bob performs on
one factor of a bipartite pure state can be *simulated* by a measurement Alice performs on the other
factor, up to a local unitary. The two theorems below establish it in the swap-symmetric normal
form (Alice's and Bob's Schmidt bases identified); step 4 lifts it off that normal form, and step 5
uses it.

### The identification of Alice's and Bob's systems

N&C's construction identifies Alice's Schmidt basis `{|lᴬ⟩}` with Bob's `{|lᴮ⟩}` (the map
`|lᴬ⟩ ↔ |lᴮ⟩`) and defines Alice's operator `Nⱼ` to have "the same matrix" as Bob's `Mⱼ` in these
identified bases. We realise this by taking Alice's and Bob's systems to be a **common** system `C`,
so "the same operator" is literally the same `Mⱼ`, and the basis identification is the `SWAP`
(`Evolution.swap`). The relevant states are then those in Schmidt normal form with respect to the
identified bases — precisely the **swap-symmetric** states `SWAP|ψ⟩ = |ψ⟩`, the hypothesis below.
This is the natural normal form N&C works in (every bipartite pure state becomes swap-symmetric once
its Schmidt bases are identified), not a weakening of the physical content.

## Formalisation

* `AxQM.Measurement.bornProb_onRight_eq_onLeft_of_swapSymmetric` — **equal probabilities.**
  For a swap-symmetric bipartite pure state `ψ` on `C ⊗ C`, Bob measuring `m` on the right factor
  (`m.onRight C`) and Alice measuring the same `m` on the left factor (`m.onLeft C`) give equal
  Born probabilities for every outcome. (N&C: both post-measurement branches occur "with probability
  `∑ₖₗ λₗ|Mⱼₖₗ|²`".)
* `AxQM.Measurement.exists_localEvolution_postMeasurement_onRight_of_swapSymmetric` — the
  **measurement-simulation lemma.** For a swap-symmetric `ψ` and any possible outcome `j`, Bob's
  post-measurement state (measuring on the right) equals Alice's post-measurement state (measuring
  the same `m` on the left) up to a **local unitary** `U ⊗ V`: there exist evolutions `U, V` on `C`
  with `(m.onRight C).post = (U ⊗ V)((m.onLeft C).post)`. This is exactly N&C's conclusion — "Bob
  performing `Mⱼ` is equivalent to Alice performing `Mⱼ` followed by a local unitary" — with the
  local unitary furnished by Exercise 2.80
  (`PureState.exists_evolution_tmul_of_sameSchmidtCoeffs`).

The `SWAP`-naturality identity, the pure post-measurement bridge, and the invariance of Schmidt
coefficients under `SWAP` are in `AxQM/Postulates/API/MeasurementSimulation.lean`.

## Proof

Write `M = m.op j`. Bob's operator on `ψ` is `1 ⊗ M` (`Measurement.onRight_op`) and Alice's is
`M ⊗ 1` (`Measurement.onLeft_op`). Swap-symmetry `SWAP|ψ⟩ = |ψ⟩` and the naturality
`SWAP·(M ⊗ 1) = (1 ⊗ M)·SWAP` (`Evolution.swap_op_mapL`) give the **mirror identity**
`(1 ⊗ M)|ψ⟩ = SWAP((M ⊗ 1)|ψ⟩)`. Since `SWAP` is an isometry, the two unnormalised post-measurement
vectors have equal norm, giving equal Born probabilities; and after normalisation Bob's
post-measurement pure state is `SWAP` applied to Alice's. Swapping the factors preserves Schmidt
coefficients (`PureState.sameSchmidtCoeffs_swap_evolvePure`), so the two post-measurement pure
states have identical Schmidt coefficients, whence Exercise 2.80 supplies the local unitary `U ⊗ V`.
The
pure post-measurement bridge (`Measurement.postMeasurement_pure`) lifts the pure-state identity to
the density-operator `postMeasurement` states via `toState_evolvePure`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap (adjoint)
open InnerProductSpace (crossSynthesis)

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {C : QSystem}

/-- **Proposition 12.14, equal probabilities.** For a swap-symmetric bipartite pure state `ψ` on
`C ⊗ C` (`SWAP|ψ⟩ = |ψ⟩`, the Schmidt normal form with Alice's and Bob's systems identified),
Bob measuring `m` on the right factor and Alice measuring the same `m` on the left factor yield the
same Born probability for every outcome `j`. The mirror identity `(1 ⊗ M)|ψ⟩ = SWAP((M ⊗ 1)|ψ⟩)`
plus the fact that `SWAP` is an isometry. -/
theorem Measurement.bornProb_onRight_eq_onLeft_of_swapSymmetric (m : Measurement ι C)
    {ψ : PureState (C ⊗ C)} (hψ : Evolution.swap.evolvePure ψ = ψ) (j : ι) :
    (m.onRight C).bornProb ψ.toState j = (m.onLeft C).bornProb ψ.toState j := by
  rw [Measurement.bornProb_toState_eq_normSq, Measurement.bornProb_toState_eq_normSq,
    m.onRight_op_apply_eq_swap_onLeft_of_swapSymmetric hψ j, Evolution.norm_op_apply]

/-- **Proposition 12.14, measurement simulation.** For a swap-symmetric bipartite pure state `ψ` on
`C ⊗ C` and any possible outcome `j` of Bob's measurement on the right factor, Bob's
post-measurement state equals Alice's post-measurement state (measuring the *same* `m` on the left
factor) up to a **local unitary** `U ⊗ V`. This is N&C's assertion that a measurement performed by
Bob on a known bipartite pure state can be simulated by a measurement performed by Alice, followed
by a local unitary — the crux that reduces a two-way LOCC protocol to a single Alice-measurement /
Bob-unitary round. The local unitary is produced by Exercise 2.80 from the equality of Schmidt
coefficients of the two post-measurement states. -/
theorem Measurement.exists_localEvolution_postMeasurement_onRight_of_swapSymmetric
    (m : Measurement ι C) {ψ : PureState (C ⊗ C)} (hψ : Evolution.swap.evolvePure ψ = ψ) (j : ι)
    (hp : (m.onRight C).bornProb ψ.toState j ≠ 0) :
    ∃ (U V : Evolution C) (hq : (m.onLeft C).bornProb ψ.toState j ≠ 0),
      (m.onRight C).postMeasurement ψ.toState j hp
        = (U.tmul V).evolve ((m.onLeft C).postMeasurement ψ.toState j hq) := by
  have hq : (m.onLeft C).bornProb ψ.toState j ≠ 0 := by
    rwa [← Measurement.bornProb_onRight_eq_onLeft_of_swapSymmetric m hψ]
  have hnb : ((m.onRight C).op j) ψ.vec ≠ 0 :=
    (m.onRight C).op_ne_zero_of_bornProb_ne_zero ψ j hp
  have hna : ((m.onLeft C).op j) ψ.vec ≠ 0 :=
    (m.onLeft C).op_ne_zero_of_bornProb_ne_zero ψ j hq
  have hmirror := m.onRight_op_apply_eq_swap_onLeft_of_swapSymmetric hψ j
  have hpure : PureState.normalize (((m.onRight C).op j) ψ.vec) hnb
      = Evolution.swap.evolvePure (PureState.normalize (((m.onLeft C).op j) ψ.vec) hna) := by
    apply PureState.ext
    rw [Evolution.evolvePure_vec, PureState.normalize_vec, PureState.normalize_vec,
      Evolution.swap_op_smul, hmirror, Evolution.norm_op_apply]
  have hsame : (PureState.normalize (((m.onRight C).op j) ψ.vec) hnb).SameSchmidtCoeffs
      (PureState.normalize (((m.onLeft C).op j) ψ.vec) hna) := by
    rw [hpure]
    exact PureState.sameSchmidtCoeffs_swap_evolvePure _
  obtain ⟨U, V, hUV⟩ := PureState.exists_evolution_tmul_of_sameSchmidtCoeffs hsame
  refine ⟨U, V, hq, ?_⟩
  rw [(m.onRight C).postMeasurement_pure ψ j hp hnb,
    (m.onLeft C).postMeasurement_pure ψ j hq hna, hUV, toState_evolvePure]

/-- **Proposition 12.14, the `bobMeasure` closure case (swap-symmetric normal form).** The fifth and
last closure property of `OneWayLOCC` (`AxQM/Core/LOCCProtocol.lean`) required by the reduction
induction — alongside the four deterministic/Alice-round cases (`OneWayLOCC.refl`,
`prepend_aliceUnitary`, `prepend_bobUnitary`, `prepend_aliceMeasure`) — here in the swap-symmetric
normal form on `C ⊗ C` (Alice's and Bob's Schmidt bases identified) where the measurement-simulation
crux lives.

If, after Bob measures `m` on his right factor of a swap-symmetric bipartite pure state `ψ` and
obtains any possible outcome `j`, the post-measurement state is one-way LOCC reachable to `σ`, then
`ψ` itself is one-way LOCC reachable to `σ`. This assembles N&C's "a measurement by Bob on a known
pure state can be simulated by a measurement by Alice, up to a unitary transformation by Bob" into
the protocol reduction: by the crux
(`exists_localEvolution_postMeasurement_onRight_of_swapSymmetric`) Bob measuring `m` is equivalent
to Alice measuring the *same* `m` on her left factor followed by the local unitary `U ⊗ V`. Peel
that unitary off with the deterministic closure lemmas — Bob's `V` via `prepend_bobUnitary` after
Alice's `U` via `prepend_aliceUnitary` (using `U ⊗ V = (U ⊗ 1)(1 ⊗ V)`) — so each of Bob's branches
becomes an Alice-`m` branch reachable to `σ`; `prepend_aliceMeasure` then folds Alice's single round
into the one-way protocol.

This is the `bobMeasure` induction case in the swap-symmetric normal form. Lifting it to an
arbitrary bipartite pure state on a general `A ⊗ B` is done by `OneWayLOCC.prepend_bobMeasure`
below; see the outline above. -/
theorem OneWayLOCC.prepend_bobMeasure_of_swapSymmetric {n : ℕ} (m : Measurement (Fin n) C)
    {ψ : PureState (C ⊗ C)} (hψ : Evolution.swap.evolvePure ψ = ψ) {σ : State (C ⊗ C)}
    (h : ∀ j, (hj : (m.onRight C).bornProb ψ.toState j ≠ 0) →
      OneWayLOCC ((m.onRight C).postMeasurement ψ.toState j hj) σ) :
    OneWayLOCC ψ.toState σ := by
  refine OneWayLOCC.prepend_aliceMeasure m (fun j hj => ?_)
  -- `hj : (m.onLeft C).bornProb ψ.toState j ≠ 0`; swap-symmetry equates Bob's and Alice's probs.
  have hjR : (m.onRight C).bornProb ψ.toState j ≠ 0 := by
    rw [Measurement.bornProb_onRight_eq_onLeft_of_swapSymmetric m hψ]; exact hj
  -- The crux: Bob's post-measurement branch `= (U ⊗ V)` applied to Alice's post-measurement branch.
  obtain ⟨U, V, hqA, hsim⟩ :=
    m.exists_localEvolution_postMeasurement_onRight_of_swapSymmetric hψ j hjR
  -- Peel Alice's `U`, then Bob's `V`, leaving Alice's `m`-branch reachable to `σ`; the residual
  -- goal rewrites Bob's branch as `(U ⊗ 1)` after `(1 ⊗ V)` applied to Alice's branch
  -- (`U ⊗ V = (U ⊗ 1)(1 ⊗ V)`, `Evolution.onLeft_comp_onRight`).
  refine OneWayLOCC.prepend_bobUnitary V (OneWayLOCC.prepend_aliceUnitary U ?_)
  rw [← Evolution.evolve_comp, Evolution.onLeft_comp_onRight, ← hsim]
  exact h j hjR

/-! ## The crux and closure case off the swap-symmetric normal form (general `A ⊗ B`)

The two theorems above live in the swap-symmetric normal form on `C ⊗ C`, where the SWAP realises
N&C's identification `|kᴬ⟩ ↔ |kᴮ⟩` of Alice's and Bob's Schmidt bases. The two below are the
**general bipartite** (`S ⊗ T`, Alice = `S`, Bob = `T`, possibly distinct systems) counterparts,
obtained by routing the "same Schmidt coefficients" conclusion through the **reduced spectra**
instead of the SWAP: a bipartite pure state's two marginals are isospectral (`ρ_A ≅ ρ_B`,
`PureState.sameNonzeroSpectrum_reducedLeft_reducedRight`), and Schmidt-coefficient equality is
exactly equality of a marginal's non-zero spectrum (N&C Exercise 12.22,
`PureState.sameSchmidtCoeffs_iff_sameNonzeroSpectrum_reducedLeft`). This is the route the general
lift takes because there is no SWAP on a genuine `S ⊗ T` with `S ≠ T`.

Both theorems take the construction of Alice's simulating operators `Nⱼ` in N&C's Eq. (12.159)
(the "same matrix in the Schmidt basis", with the completeness "caveat" outcome) as an explicit
hypothesis: that Alice's measurement `mA` **simulates** Bob's `mB`, i.e. matches its Born
probabilities (`hprob`) and produces a post-measurement marginal isospectral to Bob's (`hspec`).
This hypothesis is discharged by building `{Nⱼ}` from the Schmidt-support partial isometry in
`OneWayLOCC.prepend_bobMeasure` below. -/

variable {S T : QSystem}

/-- **Proposition 12.14, measurement simulation (general bipartite form).** For a bipartite pure
state `ψ` on `S ⊗ T` (Alice `= S`, Bob `= T`), a Bob outcome `j` (of `mB` on `T`) and an Alice
outcome `k` (of `mA` on `S`, whose outcome set need not match Bob's), if Bob's and Alice's
post-measurement states are **isospectral** — Bob's Alice-facing marginal (his `reducedRight` plays
the rôle of Alice's marginal via the duality below) matches Alice's marginal,
`x.reducedRight ≅ y.reducedLeft` — then Bob's post-measurement state equals Alice's up to a **local
unitary** `U ⊗ V`.

This is the swap-free counterpart of
`Measurement.exists_localEvolution_postMeasurement_onRight_of_swapSymmetric`: writing `x`, `y` for
the (pure) Bob- and Alice-post states, `x.reducedLeft ≅ x.reducedRight`
(`PureState.sameNonzeroSpectrum_reducedLeft_reducedRight`) chains with the hypothesis to give
`x.reducedLeft ≅ y.reducedLeft`, whence `x` and `y` share Schmidt coefficients (Exercise 12.22's
reduced-spectrum bridge `PureState.sameSchmidtCoeffs_of_sameNonzeroSpectrum_reducedLeft`) and
Exercise 2.80 supplies the local unitary. Alice's and Bob's outcome sets are kept independent (the
proof never identifies them) precisely so that Alice's *transported* measurement, indexed by
`Option (Fin n)`, can be matched to Bob's `Fin n` outcomes in `OneWayLOCC.prepend_bobMeasure` below.
The reduced-spectrum hypothesis is exactly what N&C's simulating `Nⱼ` guarantees (`Mⱼ ρ_B Mⱼ†` and
`Nⱼ ρ_A Nⱼ†` isospectral). -/
theorem Measurement.exists_localEvolution_postMeasurement_onRight_of_reducedSpectrum {κ : Type*}
    [Fintype κ] (mB : Measurement ι T) (mA : Measurement κ S) {ψ : PureState (S ⊗ T)} (j : ι)
    (k : κ) (hpB : (mB.onRight S).bornProb ψ.toState j ≠ 0)
    (hpA : (mA.onLeft T).bornProb ψ.toState k ≠ 0)
    (hspec : ((mB.onRight S).postMeasurement ψ.toState j hpB).reducedRight.SameNonzeroSpectrum
      ((mA.onLeft T).postMeasurement ψ.toState k hpA).reducedLeft) :
    ∃ (U : Evolution S) (V : Evolution T),
      (mB.onRight S).postMeasurement ψ.toState j hpB
        = (U.tmul V).evolve ((mA.onLeft T).postMeasurement ψ.toState k hpA) := by
  have hnb : ((mB.onRight S).op j) ψ.vec ≠ 0 :=
    (mB.onRight S).op_ne_zero_of_bornProb_ne_zero ψ j hpB
  have hna : ((mA.onLeft T).op k) ψ.vec ≠ 0 :=
    (mA.onLeft T).op_ne_zero_of_bornProb_ne_zero ψ k hpA
  rw [(mB.onRight S).postMeasurement_pure ψ j hpB hnb,
    (mA.onLeft T).postMeasurement_pure ψ k hpA hna] at hspec ⊢
  -- `hspec : (normalize Bobᵥ).reducedRight ≅ (normalize Aliceᵥ).reducedLeft`; the marginal duality
  -- on Bob's post-state chains to `(normalize Bobᵥ).reducedLeft ≅ (normalize Aliceᵥ).reducedLeft`.
  set φB := PureState.normalize (((mB.onRight S).op j) ψ.vec) hnb
  have hsame : φB.SameSchmidtCoeffs (PureState.normalize (((mA.onLeft T).op k) ψ.vec) hna) :=
    PureState.sameSchmidtCoeffs_of_sameNonzeroSpectrum_reducedLeft
      (φB.sameNonzeroSpectrum_reducedLeft_reducedRight.trans hspec)
  obtain ⟨U, V, hUV⟩ := PureState.exists_evolution_tmul_of_sameSchmidtCoeffs hsame
  refine ⟨U, V, ?_⟩
  rw [hUV, toState_evolvePure]

/-- **Proposition 12.14, the general `bobMeasure` closure case (abstract simulation form).** The
swap-free counterpart of `OneWayLOCC.prepend_bobMeasure_of_swapSymmetric`, on an arbitrary bipartite
system `S ⊗ T` (Alice `= S`, Bob `= T`).

If Alice has a measurement `mA` on her factor (with outcome set `κ`) that **simulates** Bob's
measurement `mB` on his through an outcome map `f : Fin n → κ` — each Bob outcome `j` occurs with
the same probability as Alice's outcome `f j` (`hprob`), Alice's outcomes outside the image of `f`
never occur (`hzero`, the completeness "caveat" outcomes of N&C's construction), and on each matched
pair Alice's post-measurement marginal is isospectral to Bob's (`hspec`) — and after Bob measures
`mB` and obtains any possible outcome `j` the post-measurement state is one-way LOCC reachable to
`σ`, then so is `ψ`. This is N&C's "a measurement by Bob on a known
pure state can be simulated by a measurement by Alice, up to a unitary transformation by Bob",
assembled into the protocol reduction: an Alice outcome `k` of nonzero probability is forced
(`hzero`) to be `f j` for some Bob outcome `j` (with `j` possible by `hprob`); the general crux
(`exists_localEvolution_postMeasurement_onRight_of_reducedSpectrum`) then makes Bob measuring `mB`
and getting `j` equivalent to Alice measuring `mA` and getting `f j` followed by the local unitary
`U ⊗ V`, which peels off via the deterministic closure lemmas (`prepend_bobUnitary` after
`prepend_aliceUnitary`, using `U ⊗ V = (U ⊗ 1)(1 ⊗ V)`); `prepend_aliceMeasure'` then folds Alice's
single (arbitrary-index) round into the one-way protocol.

The hypotheses `hprob`/`hzero`/`hspec` package precisely what N&C's simulating operators `{Nⱼ}` (Eq.
(12.159), the "same matrix in the Schmidt basis" together with the completeness caveat) provide;
they are discharged concretely for the transported square-root measurement in
`OneWayLOCC.prepend_bobMeasure` below; the protocol-tree induction
`LOCCProtocol.Transforms P ρ σ → OneWayLOCC ρ σ` is `OneWayLOCC.of_transforms_pureState`. -/
theorem OneWayLOCC.prepend_bobMeasure_of_aliceSimulates {κ : Type*} [Fintype κ] {n : ℕ}
    (mB : Measurement (Fin n) T) (mA : Measurement κ S) (f : Fin n → κ)
    {ψ : PureState (S ⊗ T)} {σ : State (S ⊗ T)}
    (hprob : ∀ j, (mB.onRight S).bornProb ψ.toState j = (mA.onLeft T).bornProb ψ.toState (f j))
    (hzero : ∀ k, (∀ j, f j ≠ k) → (mA.onLeft T).bornProb ψ.toState k = 0)
    (hspec : ∀ j, (hpB : (mB.onRight S).bornProb ψ.toState j ≠ 0) →
      (hpA : (mA.onLeft T).bornProb ψ.toState (f j) ≠ 0) →
        ((mB.onRight S).postMeasurement ψ.toState j hpB).reducedRight.SameNonzeroSpectrum
          ((mA.onLeft T).postMeasurement ψ.toState (f j) hpA).reducedLeft)
    (h : ∀ j, (hpB : (mB.onRight S).bornProb ψ.toState j ≠ 0) →
      OneWayLOCC ((mB.onRight S).postMeasurement ψ.toState j hpB) σ) :
    OneWayLOCC ψ.toState σ := by
  refine OneWayLOCC.prepend_aliceMeasure' mA (fun k hk => ?_)
  -- `hk` is nonzero, so the caveat (`hzero`) rules out `k ∉ range f`, giving `k = f j`.
  obtain ⟨j, rfl⟩ : ∃ j, f j = k := by
    by_contra hc
    exact hk (hzero k fun j hj => hc ⟨j, hj⟩)
  -- `hk : (mA.onLeft T).bornProb ψ (f j) ≠ 0`; `hprob` makes Bob's outcome `j` possible too.
  have hjB : (mB.onRight S).bornProb ψ.toState j ≠ 0 := by rw [hprob j]; exact hk
  -- The crux: Bob's `j`-branch `= (U ⊗ V)` applied to Alice's `f j`-branch.
  obtain ⟨U, V, hsim⟩ :=
    mB.exists_localEvolution_postMeasurement_onRight_of_reducedSpectrum mA j (f j) hjB hk
      (hspec j hjB hk)
  -- Peel Alice's `U`, then Bob's `V`, leaving Alice's `mA`-branch reachable to `σ`
  -- (`U ⊗ V = (U ⊗ 1)(1 ⊗ V)`, `Evolution.onLeft_comp_onRight`).
  refine OneWayLOCC.prepend_bobUnitary V (OneWayLOCC.prepend_aliceUnitary U ?_)
  rw [← Evolution.evolve_comp, Evolution.onLeft_comp_onRight, ← hsim]
  exact h j hjB

/-- **Proposition 12.14, the unconditional general `bobMeasure` closure case.** The `bobMeasure`
induction case with Alice's simulating measurement *constructed*, on an arbitrary bipartite pure
state `ψ` on `S ⊗ T` (Alice `= S`, Bob `= T`): if after Bob measures `mB` on his factor and obtains
any possible outcome `j` the post-measurement state is one-way LOCC reachable to `σ`, then `ψ`
is. No `hprob`/`hspec` hypothesis — the simulating Alice measurement is built here.

This assembles N&C's Eq. (12.159) simulation completely. Take a Schmidt decomposition
`|ψ⟩ = ∑ᵢ lᵢ |aᵢ⟩|bᵢ⟩` (`PureState.exists_isSchmidtDecomposition`); the cross-synthesis partial
isometry `W = crossSynthesis a b` identifies Bob's Schmidt basis with Alice's, and Alice's
simulating measurement is the square-root ("pretty-good") `ofPOVM (mB.transportPOVM W hW)`
of the transported POVM `{W Mⱼ† Mⱼ W†} ∪ {1 − W W†}` — indexed by `Option (Fin n)`, the outcome
`some j` carrying `√(W Mⱼ† Mⱼ W†)` and the completeness caveat `none` carrying `1 − W W†`. Feed it
to the abstract simulation closure `prepend_bobMeasure_of_aliceSimulates` along `f = some`,
discharging its three hypotheses with the following facts: Born-probability matching
`Measurement.bornProb_onLeft_ofPOVM_transportPOVM_eq` (`hprob`), the caveat's zero probability
`Measurement.bornProb_onLeft_ofPOVM_transportPOVM_none_eq_zero` (`hzero` — the only outcome outside
`range some` is `none`), and the post-measurement marginal isospectrality
`PureState.sameNonzeroSpectrum_transport_postMeasurement_marginal` (`hspec`).

This completes the construction of the simulating operators `{Nⱼ}` (step 4 of the outline); the
protocol-tree induction over `LOCCProtocol.Transforms P ρ σ → OneWayLOCC ρ σ` assembling all five
closure cases is `OneWayLOCC.of_transforms_pureState` (step 5). -/
theorem OneWayLOCC.prepend_bobMeasure {n : ℕ} (mB : Measurement (Fin n) T)
    {ψ : PureState (S ⊗ T)} {σ : State (S ⊗ T)}
    (h : ∀ j, (hpB : (mB.onRight S).bornProb ψ.toState j ≠ 0) →
      OneWayLOCC ((mB.onRight S).postMeasurement ψ.toState j hpB) σ) :
    OneWayLOCC ψ.toState σ := by
  -- Schmidt decomposition `|ψ⟩ = ∑ᵢ lᵢ |aᵢ⟩|bᵢ⟩` and the cross-synthesis coisometry `W`.
  obtain ⟨r, l, a, b, _hpos, ha, hb, _hnorm, hψ⟩ := ψ.exists_isSchmidtDecomposition
  have hW : IsStarProjection ((crossSynthesis ℂ a b).comp (adjoint (crossSynthesis ℂ a b))) := by
    rw [InnerProductSpace.crossSynthesis_comp_adjoint a hb]
    exact InnerProductSpace.isStarProjection_orthonormalProjector ha Finset.univ
  -- Alice's square-root measurement of the transported POVM (indexed by `Option (Fin n)`),
  -- matched to Bob's outcomes along `f = some`.
  refine OneWayLOCC.prepend_bobMeasure_of_aliceSimulates mB
    (Measurement.ofPOVM (mB.transportPOVM (crossSynthesis ℂ a b) hW)) some
    (fun j => (mB.bornProb_onLeft_ofPOVM_transportPOVM_eq ha hb hψ hW j).symm) ?_ ?_ h
  · -- `hzero`: the only Alice outcome outside `range some` is the zero-probability caveat `none`.
    intro o ho
    obtain rfl : o = none := by
      cases o with
      | none => rfl
      | some j => exact absurd rfl (ho j)
    exact mB.bornProb_onLeft_ofPOVM_transportPOVM_none_eq_zero ha hb hψ hW
  · -- `hspec`: Bob's `Mⱼ`-collapsed marginal and Alice's `√Eⱼ`-collapsed marginal are isospectral.
    intro j hpB hpA
    exact PureState.sameNonzeroSpectrum_transport_postMeasurement_marginal mB ha hb hψ hW j hpB hpA

/-! ## The reduction (Proposition 12.14): general LOCC of a pure state collapses to one-way LOCC

The five closure properties of `OneWayLOCC` — reflexivity (`OneWayLOCC.refl`, the `terminal` case),
the two local-unitary absorptions (`prepend_aliceUnitary` / `prepend_bobUnitary`), the
Alice-measurement combination (`prepend_aliceMeasure`, N&C's Ex. 2.57), and the Bob-measurement
simulation (`prepend_bobMeasure`, N&C's Eq. (12.159) crux) — are exactly the five constructor cases
of a structural induction on the protocol tree `P : LOCCProtocol A B`. The induction carries a
**pure** state through every node — necessary because the `bobMeasure` closure is a pure-state fact
(a mixed intermediate state has no Schmidt basis to identify Alice's and Bob's systems): the initial
`ψ` is pure, and a pure state stays pure under a local unitary (`toState_evolvePure`) and under a
post-measurement collapse (`Measurement.postMeasurement_pure`), so every recursive branch is again a
`PureState.toState`. This assembles the whole proposition (step 5 of the outline). -/

variable {A B : QSystem}

/-- **Proposition 12.14 (the reduction).** Every finite-round two-way LOCC protocol `P` that
deterministically transforms a bipartite **pure** state `ψ` into `σ` — i.e. every
nonzero-probability branch of `P` on `ψ` ends in `σ` (`LOCCProtocol.Transforms`) — can be replaced
by a **single-round one-way** protocol: Alice performs one measurement `{Mⱼ}`, sends the outcome `j`
to Bob, who applies a conditional unitary `Vⱼ` (`OneWayLOCC ψ.toState σ`). This is the headline
claim of N&C Proposition 12.14.

Proved by induction on the protocol tree `P`, one case per constructor, each discharged by the
corresponding closure property of `OneWayLOCC` established across `Core/LOCCProtocol.lean` and this
file:

* `terminal` — `σ = ψ.toState`, so `OneWayLOCC.refl`;
* `aliceUnitary U` / `bobUnitary V` — `OneWayLOCC.prepend_aliceUnitary` / `prepend_bobUnitary`
  absorb the leading local unitary into Alice's measurement / Bob's correction, and
  `toState_evolvePure` exhibits the evolved state as a pure state for the inductive hypothesis;
* `aliceMeasure m` — `OneWayLOCC.prepend_aliceMeasure` combines Alice's round into the single
  one-way measurement (N&C's "combine into one measurement, Ex. 2.57"), each post-measurement branch
  being pure by `Measurement.postMeasurement_pure`;
* `bobMeasure m` — `OneWayLOCC.prepend_bobMeasure` simulates Bob's measurement by an Alice
  measurement followed by a Bob unitary (N&C's Eq. (12.159)), again with pure post-measurement
  branches.

The target `σ` is left an arbitrary `State`: the deterministic hypothesis forces it to be pure
anyway, so this generalises N&C's pure `|ϕ⟩` rather than weakening it. -/
theorem OneWayLOCC.of_transforms_pureState :
    ∀ (P : LOCCProtocol A B) (ψ : PureState (A ⊗ B)) (σ : State (A ⊗ B)),
      P.Transforms ψ.toState σ → OneWayLOCC ψ.toState σ := by
  intro P
  induction P with
  | terminal =>
      intro ψ σ h
      rw [LOCCProtocol.terminal_transforms_iff] at h
      rw [← h]
      exact OneWayLOCC.refl _
  | aliceMeasure n m k ih =>
      intro ψ σ h
      rw [LOCCProtocol.aliceMeasure_transforms_iff] at h
      refine OneWayLOCC.prepend_aliceMeasure m (fun j hj => ?_)
      have hv : (m.onLeft B).op j ψ.vec ≠ 0 := (m.onLeft B).op_ne_zero_of_bornProb_ne_zero ψ j hj
      have hpost := (m.onLeft B).postMeasurement_pure ψ j hj hv
      have hk := h j hj
      rw [hpost] at hk ⊢
      exact ih j _ σ hk
  | bobMeasure n m k ih =>
      intro ψ σ h
      rw [LOCCProtocol.bobMeasure_transforms_iff] at h
      refine OneWayLOCC.prepend_bobMeasure m (fun j hj => ?_)
      have hv : (m.onRight A).op j ψ.vec ≠ 0 := (m.onRight A).op_ne_zero_of_bornProb_ne_zero ψ j hj
      have hpost := (m.onRight A).postMeasurement_pure ψ j hj hv
      have hk := h j hj
      rw [hpost] at hk ⊢
      exact ih j _ σ hk
  | aliceUnitary U k ih =>
      intro ψ σ h
      rw [LOCCProtocol.aliceUnitary_transforms_iff, ← toState_evolvePure] at h
      refine OneWayLOCC.prepend_aliceUnitary U ?_
      have := ih ((U.onLeft B).evolvePure ψ) σ h
      rwa [toState_evolvePure] at this
  | bobUnitary V k ih =>
      intro ψ σ h
      rw [LOCCProtocol.bobUnitary_transforms_iff, ← toState_evolvePure] at h
      refine OneWayLOCC.prepend_bobUnitary V ?_
      have := ih ((V.onRight A).evolvePure ψ) σ h
      rwa [toState_evolvePure] at this

/-- **Proposition 12.14, N&C's phrasing.** If a bipartite pure state `ψ` *can be transformed* to `σ`
by some finite-round two-way LOCC protocol (`∃ P, P.Transforms ψ.toState σ`), then the
transformation is achievable by a one-way protocol — Alice measures once, sends the outcome to Bob,
who applies a conditional unitary (`OneWayLOCC ψ.toState σ`). This is N&C's statement verbatim:
"Suppose `|ψ⟩` can be transformed to `|ϕ⟩` by LOCC. Then this transformation can be achieved by a
protocol involving just … Alice performs a single measurement …, sends the result `j` to Bob, who
performs a unitary operation `Uⱼ`." The existential over protocols is the hypothesis's "by LOCC";
`OneWayLOCC` is the reduced one-way form. Immediate from the per-protocol reduction
`OneWayLOCC.of_transforms_pureState`. -/
theorem OneWayLOCC.of_exists_transforms_pureState (ψ : PureState (A ⊗ B)) (σ : State (A ⊗ B))
    (h : ∃ P : LOCCProtocol A B, P.Transforms ψ.toState σ) : OneWayLOCC ψ.toState σ := by
  obtain ⟨P, hP⟩ := h
  exact OneWayLOCC.of_transforms_pureState P ψ σ hP

end AxQM
