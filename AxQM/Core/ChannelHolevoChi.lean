/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.HolevoChiBound
import AxQM.Postulates.API.QuantumChannel

/-!
# The Holevo χ quantity of a quantum channel (N&C eq. (12.71))

The **Holevo χ quantity** of a trace-preserving quantum operation `E` is the left-hand side of the
Holevo–Schumacher–Westmoreland (HSW) theorem (Nielsen & Chuang, Theorem 12.8, eq. (12.71)):

`χ(E) ≡ max_{{pⱼ, ρⱼ}} [ S(E(∑ⱼ pⱼ ρⱼ)) − ∑ⱼ pⱼ S(E(ρⱼ)) ]`,

the maximum, over all input ensembles `{pⱼ, ρⱼ}`, of the Holevo χ of the corresponding *output*
ensemble `{pⱼ, E(ρⱼ)}`. The HSW theorem states that `χ(E)` equals the product-state capacity
`C⁽¹⁾(E)` of the channel; this file defines the χ(E) quantity itself and proves its foundational
properties.

## Design

`χ(E)` is defined as the Holevo χ (`State.holevoChi`, N&C eq. (12.208)) of the *output* ensemble
`{pⱼ, E(ρⱼ)}`, maximized over input ensembles. This form:

* directly reuses the ensemble Holevo χ, inheriting its bounds
  (`holevoChi_nonneg`, `holevoChi_le_vonNeumannEntropy_mix`); and
* **equals N&C's eq. (12.71) form** `S(E(∑ⱼ pⱼ ρⱼ)) − ∑ⱼ pⱼ S(E(ρⱼ))` whenever `E` is a channel,
  because a channel is affine over probabilistic mixtures — the entropy of the output mixture
  `S(∑ⱼ pⱼ E(ρⱼ))` equals the entropy of the channel applied to the input mixture
  `S(E(∑ⱼ pⱼ ρⱼ))`. This is exactly `holevoChi_comp_eq_of_isChannel` (the fidelity bridge),
  resting on `map_mix_of_isChannel`.

The maximization is a supremum over ensembles indexed by `Fin n` for arbitrary `n : ℕ`; restricting
to `Fin n` is without loss of generality (any finite ensemble reindexes to a `Fin n` one with the
same χ value, since χ depends on the ensemble only through the mixture and the weighted-average
entropy). The supremum is well defined: the value set is bounded above (each element is
`≤ S(mixture) ≤ log d`, `channelHolevoChiSet_bddAbove`) and `χ(E) ≥ 0` (each output-ensemble χ is
non-negative; the empty case gives `sSup ∅ = 0`, `channelHolevoChi_nonneg`).

## Main definitions and results

* `AxQM.channelHolevoChi` — the Holevo χ quantity `χ(E)` of a channel.
* `AxQM.map_mix_of_isChannel` — a channel is affine over mixtures,
  `E(∑ⱼ pⱼ ρⱼ) = ∑ⱼ pⱼ E(ρⱼ)`.
* `AxQM.holevoChi_comp_eq_of_isChannel` — the fidelity bridge: for a channel, the
  per-ensemble summand equals N&C's eq. (12.71) expression.
* `AxQM.le_channelHolevoChi` — each input ensemble's output Holevo χ is `≤ χ(E)`.
* `AxQM.channelHolevoChi_nonneg` — `0 ≤ χ(E)`.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A quantum channel is affine over probabilistic mixtures**: for a channel `E` and an ensemble
`{pᵢ, ρᵢ}`, `E(∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ E(ρᵢ)`. A channel is the restriction to states of a *linear*
superoperator `Φ` (`IsChannel`), and linearity commutes with the convex combination defining the
mixture `State.mix`. -/
theorem map_mix_of_isChannel {E : State S → State S} (hE : IsChannel E)
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (ρ : ι → State S) :
    E (State.mix p hp hsum ρ) = State.mix p hp hsum (fun i => E (ρ i)) := by
  obtain ⟨Φ, _, _, hΦ⟩ := hE
  apply State.ext
  rw [hΦ, State.mix_op, State.mix_op, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hΦ]

/-- The set of Holevo χ values `χ({pⱼ, E(ρⱼ)})` of the *output* ensemble obtained by pushing a
finite input ensemble `{pⱼ, ρⱼ}` (indexed by `Fin n`, WLOG for finite ensembles) through `E`. Its
supremum is the channel Holevo χ quantity `channelHolevoChi E`. -/
def channelHolevoChiSet (E : State S → State S) : Set ℝ :=
  {x | ∃ (n : ℕ) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : Fin n → State S),
      x = State.holevoChi p hp hsum (fun i => E (ρ i))}

/-- **The Holevo χ quantity of a quantum channel** `E` (Nielsen & Chuang, eq. (12.71)): the maximum
Holevo χ of the output ensemble `{pⱼ, E(ρⱼ)}` over all input ensembles `{pⱼ, ρⱼ}`,
`χ(E) = max_{{pⱼ,ρⱼ}} [S(E(∑ⱼ pⱼ ρⱼ)) − ∑ⱼ pⱼ S(E(ρⱼ))]`. It is the left-hand side of the HSW
theorem `χ(E) = C⁽¹⁾(E)`. Realized as the supremum of `channelHolevoChiSet E`. -/
def channelHolevoChi (E : State S → State S) : ℝ :=
  sSup (channelHolevoChiSet E)

/-- The output-ensemble Holevo χ of any input ensemble is a member of `channelHolevoChiSet E`. -/
theorem holevoChi_comp_mem_channelHolevoChiSet (E : State S → State S) {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : Fin n → State S) :
    State.holevoChi p hp hsum (fun i => E (ρ i)) ∈ channelHolevoChiSet E :=
  ⟨n, p, hp, hsum, ρ, rfl⟩

/-- `channelHolevoChiSet E` is bounded above: every output-ensemble Holevo χ is at most the entropy
of its output mixture (`holevoChi_le_vonNeumannEntropy_mix`), which is at most `log d`. -/
theorem channelHolevoChiSet_bddAbove (E : State S → State S) :
    BddAbove (channelHolevoChiSet E) := by
  refine ⟨Real.log (Module.finrank ℂ S.space), ?_⟩
  rintro x ⟨n, p, hp, hsum, ρ, rfl⟩
  exact (State.holevoChi_le_vonNeumannEntropy_mix p hp hsum _).trans
    (State.vonNeumannEntropy_le_log_finrank _)

/-- `channelHolevoChiSet E` is nonempty: the trivial one-state ensemble contributes a value (hence
the `[Nonempty (State S)]` hypothesis). The companion of `channelHolevoChiSet_bddAbove`. -/
theorem channelHolevoChiSet_nonempty [Nonempty (State S)] (E : State S → State S) :
    (channelHolevoChiSet E).Nonempty :=
  ⟨_, holevoChi_comp_mem_channelHolevoChiSet E (fun _ : Fin 1 => 1) (fun _ => zero_le_one)
    (by simp) (fun _ => Classical.arbitrary (State S))⟩

/-- **The maximization property of `χ(E)`**: for every input ensemble `{pⱼ, ρⱼ}`, the Holevo χ of
the output ensemble `{pⱼ, E(ρⱼ)}` is at most `χ(E)`. -/
theorem le_channelHolevoChi (E : State S → State S) {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : Fin n → State S) :
    State.holevoChi p hp hsum (fun i => E (ρ i)) ≤ channelHolevoChi E :=
  le_csSup (channelHolevoChiSet_bddAbove E) (holevoChi_comp_mem_channelHolevoChiSet E p hp hsum ρ)

/-- **Non-negativity of the channel Holevo χ quantity**: `0 ≤ χ(E)`. Each output-ensemble Holevo χ
is non-negative (`State.holevoChi_nonneg`), and if there are no ensembles at all the supremum of the
empty set is `0`. -/
theorem channelHolevoChi_nonneg (E : State S → State S) : 0 ≤ channelHolevoChi E := by
  rcases (channelHolevoChiSet E).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · rw [channelHolevoChi, h, Real.sSup_empty]
  · obtain ⟨n, p, hp, hsum, ρ, rfl⟩ := hx
    exact le_csSup_of_le (channelHolevoChiSet_bddAbove E)
      (holevoChi_comp_mem_channelHolevoChiSet E p hp hsum ρ) (State.holevoChi_nonneg p hp hsum _)

/-- **Fidelity bridge to N&C eq. (12.71).** For a **channel** `E`, the per-ensemble summand defining
`χ(E)` — the Holevo χ of the output ensemble `{pⱼ, E(ρⱼ)}` — equals Nielsen & Chuang's eq. (12.71)
expression `S(E(∑ⱼ pⱼ ρⱼ)) − ∑ⱼ pⱼ S(E(ρⱼ))`, the entropy of the channel applied to the *input*
mixture minus the average output entropy. The two forms agree because a channel is affine over
mixtures (`map_mix_of_isChannel`), so `S(∑ⱼ pⱼ E(ρⱼ)) = S(E(∑ⱼ pⱼ ρⱼ))`. -/
theorem holevoChi_comp_eq_of_isChannel {E : State S → State S} (hE : IsChannel E)
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (ρ : ι → State S) :
    State.holevoChi p hp hsum (fun i => E (ρ i)) =
      (E (State.mix p hp hsum ρ)).vonNeumannEntropy - ∑ i, p i * (E (ρ i)).vonNeumannEntropy := by
  rw [State.holevoChi_def, map_mix_of_isChannel hE]

end AxQM
