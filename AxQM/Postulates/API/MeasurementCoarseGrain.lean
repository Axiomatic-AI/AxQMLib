/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SquareRootMeasurement
import ToMathlib.Analysis.InnerProductSpace.POVMMap

/-!
# Coarse-graining the outcomes of a measurement

Given a measurement `m : Measurement ι S` and a function `g : ι → κ` on the outcome index, the
**coarse-grained measurement** `m.coarseGrain g : Measurement κ S` groups (merges) the original
outcomes according to `g`: measuring `m.coarseGrain g` and obtaining `k` has the summed Born
probability of all original outcomes lying over `k`,

`(m.coarseGrain g).bornProb ρ k = ∑_{i : g i = k} m.bornProb ρ i`   (`coarseGrain_bornProb`).

It is realised as the **square-root measurement** (`Measurement.ofPOVM`) of the pushforward POVM
`m.toPOVM.map g` (`POVM.map`): the induced POVM effect at `k` is the fibre-sum `∑_{g i = k} Eᵢ` of
`m`'s effects, and `ofPOVM` supplies canonical measurement operators (the operator square roots)
realising it.  Since the physically observable content of a measurement is its Born rule (the
induced POVM), this is *the* coarse-graining: `reindexOutcome` (relabelling along an equivalence)
is the special case where `g` is a bijection and every fibre is a singleton.

The intended use is the **achievability half of the Holevo–Schumacher–Westmoreland theorem**
(`χ(E) = C⁽¹⁾(E)`, Nielsen & Chuang Theorem 12.8): the *expurgation* step (N&C eq. (12.83)) passes
from a code with small **average** error to a subcode with small **maximum** error by discarding
the worst messages.  The subcode's decoder is the original decoder with the outcomes announcing a
discarded message folded into the inconclusive outcome — exactly a coarse-graining along a
function `Option (Fin K) → Option (Fin K')` that carries each retained message to itself.
`coarseGrain_bornProb_of_filter_eq_singleton` records that such a *retained* (singleton-fibre)
outcome keeps its original Born probability, so the retained messages' error probabilities are
preserved.

## Main definitions / results

* `AxQM.Measurement.coarseGrain` — the coarse-grained measurement along `g : ι → κ`.
* `AxQM.Measurement.coarseGrain_bornProb` — its Born rule,
  `(m.coarseGrain g).bornProb ρ k = ∑_{i : g i = k} m.bornProb ρ i`.
* `AxQM.Measurement.coarseGrain_bornProb_of_filter_eq_singleton` — a retained
  (singleton-fibre) outcome keeps its Born probability,
  `(m.coarseGrain g).bornProb ρ k = m.bornProb ρ i₀`.

-/

open scoped BigOperators

noncomputable section

namespace AxQM

namespace Measurement

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ] {S : QSystem}

/-- **Coarse-graining the outcomes of a measurement.** For a measurement `m : Measurement ι S` and a
function `g : ι → κ`, `m.coarseGrain g` is the measurement on `S` with outcome set `κ` that merges
the original outcomes along `g`.  It is the square-root measurement (`Measurement.ofPOVM`) of the
pushforward POVM `m.toPOVM.map g`, whose effect at `k` is the fibre-sum `∑_{i : g i = k} Eᵢ`
of `m`'s effects.  Its Born rule is the grouped Born rule `coarseGrain_bornProb`. -/
def coarseGrain (m : Measurement ι S) (g : ι → κ) : Measurement κ S :=
  Measurement.ofPOVM (m.toPOVM.map g)

/-- **Born rule of the coarse-grained measurement.** The probability that `m.coarseGrain g` assigns
to the merged outcome `k` on a state `ρ` is the sum of the probabilities `m` assigns to the original
outcomes lying over `k`: `(m.coarseGrain g).bornProb ρ k = ∑_{i : g i = k} m.bornProb ρ i`.
Combines the square-root measurement's Born rule (`ofPOVM_bornProb`) with the pushforward POVM's
Born rule
(`POVM.map_toPMF`); the summand `m.toPOVM.toPMF ρ.op i` is `m.bornProb ρ i` by definition. -/
theorem coarseGrain_bornProb (m : Measurement ι S) (g : ι → κ) (ρ : State S) (k : κ) :
    (m.coarseGrain g).bornProb ρ k =
      ∑ i ∈ Finset.univ.filter (fun i => g i = k), m.bornProb ρ i := by
  rw [coarseGrain, Measurement.ofPOVM_bornProb, POVM.map_toPMF]
  rfl

/-- **A retained (singleton-fibre) outcome keeps its Born probability.** If the fibre of `g`
over `k` is the single outcome `i₀` (its `filter` is `{i₀}`), then `m.coarseGrain g` assigns `k`
exactly the
Born probability `m` assigned to `i₀`: `(m.coarseGrain g).bornProb ρ k = m.bornProb ρ i₀`.  This is
the outcome-preservation used by HSW expurgation, where each retained message's decoding outcome has
a singleton fibre. -/
theorem coarseGrain_bornProb_of_filter_eq_singleton (m : Measurement ι S) (g : ι → κ) (ρ : State S)
    (k : κ) (i₀ : ι) (h : Finset.univ.filter (fun i => g i = k) = {i₀}) :
    (m.coarseGrain g).bornProb ρ k = m.bornProb ρ i₀ := by
  rw [coarseGrain_bornProb, h, Finset.sum_singleton]

end Measurement

end AxQM
