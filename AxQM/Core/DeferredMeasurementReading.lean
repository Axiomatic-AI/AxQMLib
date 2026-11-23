/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Measurement
import AxQM.Postulates.API.Evolution

/-!
# Deferring a *composition* of gates past a measurement, at the reading level

The operator-level results `Measurement.{bornProb,postMeasurement}_evolve_prod_of_forall_comm`
(`AxQM/Postulates/API/DeferredMeasurement.lean`) defer a whole composition `(Us.map V).prod` of
gates past a measurement `m` from the *operator* commutations `Mᵢ (V a) = (W a i) Mᵢ`.

For gates and measurements such as `qtowerSingleWire` past `qtowerMeasurement`, the per-gate
commutation is not available as an operator identity. What one does have is each gate's two
*readings* — Born-probability invariance and post-measurement deferral. This file is the
**reading-level analog** of the operator-level results: it composes those readings down a list, so
a whole composition of gates — each individually invisible-to / deferring-past a measurement —
defers past it as one, with **no** operator commutation needed.

If every gate `V a` is invisible to the statistics of `m` (`hb`) and defers past `m` to a branch
gate `W a i` (`hpm`), then:

* `Measurement.bornProb_evolve_prod_of_forall_defers` — the whole composition `(Us.map V).prod` is
  invisible to the statistics of `m`;
* `Measurement.postMeasurement_evolve_prod_of_forall_defers` — the whole composition defers past `m`
  to the composed branch gates `(Us.map (fun a => W a i)).prod`.

Both are plain `List` inductions chaining the single-gate readings; the collapse induction
transports the measured state across the peel with `Measurement.postMeasurement_congr_state`
(post-measurement states depend only on the state measured, not on the possibility proof). The
statements involve only `Measurement.bornProb`, `Measurement.postMeasurement` and
`Evolution.evolve`, and they subsume the several reading-level cascade deferrals that would
otherwise be proved separately for each item.
-/

noncomputable section

namespace AxQM

variable {α : Type*} {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- **Post-measurement states depend only on the measured state, not on the possibility proof.** If
`ρ = ρ'` then the collapsed states agree (once both outcomes are possible), by `subst` and proof
irrelevance of the `bornProb … ≠ 0` argument. This lets a deferral induction rewrite the *state*
being measured across a peeling step without dependent-cast friction. -/
theorem postMeasurement_congr_state (m : Measurement ι S) {ρ ρ' : State S} (h : ρ = ρ') {i : ι}
    (hp : m.bornProb ρ i ≠ 0) (hp' : m.bornProb ρ' i ≠ 0) :
    m.postMeasurement ρ i hp = m.postMeasurement ρ' i hp' := by
  subst h; rfl

/-- **Outcome probabilities are unchanged when a whole composition of gates is deferred** (Postulate
3), from the per-gate *reading* (not operator commutation). If every gate `V a` is invisible to the
statistics of `m` — `m.bornProb ((V a).evolve ρ) i = m.bornProb ρ i` (`hb`) — then so is their whole
composition `(Us.map V).prod`. A plain `List` induction: the empty composition is the identity gate
(`Evolution.evolve_id`), and each `cons` peels the head gate off the front via
`Evolution.evolve_comp` and applies `hb` then the inductive hypothesis. The reading-level analog of
`bornProb_evolve_prod_of_forall_comm`, usable when no per-gate operator commutation is available. -/
theorem bornProb_evolve_prod_of_forall_defers (m : Measurement ι S) (V : α → Evolution S)
    (hb : ∀ (a : α) (ρ : State S) (i : ι), m.bornProb ((V a).evolve ρ) i = m.bornProb ρ i)
    (Us : List α) (ρ : State S) (i : ι) :
    m.bornProb ((Us.map V).prod.evolve ρ) i = m.bornProb ρ i := by
  induction Us with
  | nil => rw [List.map_nil, List.prod_nil, Evolution.one_def, Evolution.evolve_id]
  | cons a t ih =>
      rw [List.map_cons, List.prod_cons, Evolution.mul_def, Evolution.evolve_comp, hb a]
      exact ih

/-- **The post-measurement state defers a whole composition of gates** (Postulate 4), from the
per-gate *readings*. If every gate `V a` is invisible to the statistics of `m` (`hb`) and defers
past `m` to a branch gate `W a i` — `postMeas((V a) ρ (V a)†, i) = (W a i) · postMeas(ρ, i)`
(`hpm`) — then the whole composition `(Us.map V).prod` defers past `m` to the composed branch gates
`(Us.map (fun a => W a i)).prod`:

  `postMeas((Vₖ ⋯ V₁) ρ (Vₖ ⋯ V₁)†, i) = (Wₖ ⋯ W₁)ᵢ · postMeas(ρ, i)`.

A `List` induction peeling the head gate off the front (`Evolution.evolve_comp`): the tail
composition defers by the inductive hypothesis, then the head gate defers by `hpm`, chained by
`postMeasurement_congr_state` (which moves the measured state across the peel without dependent-cast
friction). The reading-level analog of `postMeasurement_evolve_prod_of_forall_comm`, usable when no
per-gate operator commutation is available. -/
theorem postMeasurement_evolve_prod_of_forall_defers (m : Measurement ι S) (V : α → Evolution S)
    (W : α → ι → Evolution S)
    (hb : ∀ (a : α) (ρ : State S) (i : ι), m.bornProb ((V a).evolve ρ) i = m.bornProb ρ i)
    (hpm : ∀ (a : α) (ρ : State S) (i : ι) (hρ : m.bornProb ρ i ≠ 0)
        (hρ' : m.bornProb ((V a).evolve ρ) i ≠ 0),
        m.postMeasurement ((V a).evolve ρ) i hρ' = (W a i).evolve (m.postMeasurement ρ i hρ))
    (Us : List α) (ρ : State S) (i : ι) (hp : m.bornProb ρ i ≠ 0)
    (hp' : m.bornProb ((Us.map V).prod.evolve ρ) i ≠ 0) :
    m.postMeasurement ((Us.map V).prod.evolve ρ) i hp'
      = (Us.map (fun a => W a i)).prod.evolve (m.postMeasurement ρ i hp) := by
  revert hp'
  induction Us with
  | nil =>
      intro hp'
      have hnil : (([] : List α).map V).prod.evolve ρ = ρ := by
        rw [List.map_nil, List.prod_nil, Evolution.one_def, Evolution.evolve_id]
      rw [postMeasurement_congr_state m hnil hp' hp,
          List.map_nil, List.prod_nil, Evolution.one_def, Evolution.evolve_id]
  | cons a t ih =>
      intro hp'
      have hp_rest : m.bornProb ((t.map V).prod.evolve ρ) i ≠ 0 := by
        rw [bornProb_evolve_prod_of_forall_defers m V hb t ρ i]; exact hp
      have hp'' : m.bornProb ((V a).evolve ((t.map V).prod.evolve ρ)) i ≠ 0 := by
        rw [hb a]; exact hp_rest
      have hcons : ((a :: t).map V).prod.evolve ρ
          = (V a).evolve ((t.map V).prod.evolve ρ) := by
        rw [List.map_cons, List.prod_cons, Evolution.mul_def, Evolution.evolve_comp]
      rw [postMeasurement_congr_state m hcons hp' hp'',
          hpm a ((t.map V).prod.evolve ρ) i hp_rest hp'', ih hp_rest,
          List.map_cons, List.prod_cons, Evolution.mul_def, Evolution.evolve_comp]

end Measurement

end AxQM
