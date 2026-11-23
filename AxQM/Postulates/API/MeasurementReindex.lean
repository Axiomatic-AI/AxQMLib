/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CascadedMeasurement

/-!
# Relabelling the outcomes of a measurement

Given a measurement `m : Measurement ι S` and an equivalence `e : Y ≃ ι` between outcome sets, the
**outcome relabelling** `m.reindexOutcome e : Measurement Y S` is the same POVM read through `e`:
its operator at `y` is `m.op (e y)`. Relabelling the outcomes of a measurement leaves the physics
untouched — the Born probability of a relabelled outcome `y` equals that of the original outcome
`e y` (`Measurement.reindexOutcome_bornProb`).

This is the tool that lets a result proved for a measurement with `Fin r` outcomes be applied to
a measurement whose outcomes are packaged as some other finite type: relabel the latter along the
canonical `Fintype.equivFin` (or `finSuccEquiv`, …) and transport the Born probabilities. It is
used in the HSW converse (`AxQM/NC/Ch12/Theorem12_8.lean`) to feed a product-state code's
`Option (Fin K)`-valued decoder into the single-letterisation bound, which is phrased over
`Fin (K + 1)` outcomes.

-/

open ContinuousLinearMap InnerProductSpace
open scoped BigOperators

noncomputable section

namespace AxQM

namespace Measurement

variable {ι Y : Type*} [Fintype ι] [Fintype Y] {S : QSystem}

/-- **Relabelling the outcomes of a measurement.** For a measurement `m : Measurement ι S` and an
equivalence `e : Y ≃ ι` of outcome sets, `m.reindexOutcome e` is the measurement on `S` with outcome
set `Y` whose operator at `y` is `m.op (e y)`. Completeness transfers along `e` because summing the
POVM effects over `Y` reindexes to the sum over `ι` (`Equiv.sum_comp`). -/
def reindexOutcome (m : Measurement ι S) (e : Y ≃ ι) : Measurement Y S where
  op y := m.op (e y)
  complete := by
    rw [Equiv.sum_comp e fun i => (adjoint (m.op i)).comp (m.op i)]
    exact m.complete

@[simp]
theorem reindexOutcome_op (m : Measurement ι S) (e : Y ≃ ι) (y : Y) :
    (m.reindexOutcome e).op y = m.op (e y) := rfl

/-- **Relabelling preserves Born probabilities.** The Born probability that the relabelled
measurement `m.reindexOutcome e` assigns to outcome `y` on a state `ρ` equals the Born probability
`m` assigns to the corresponding original outcome `e y`:

`(m.reindexOutcome e).bornProb ρ y = m.bornProb ρ (e y)`.

Born probabilities depend only on the outcome operator (`Measurement.bornProb_congr`), and
`(m.reindexOutcome e).op y = m.op (e y)` by construction. -/
theorem reindexOutcome_bornProb (m : Measurement ι S) (e : Y ≃ ι) (ρ : State S) (y : Y) :
    (m.reindexOutcome e).bornProb ρ y = m.bornProb ρ (e y) :=
  Measurement.bornProb_congr rfl ρ

/-- **Relabelling preserves the post-measurement state.** The state after the relabelled measurement
`m.reindexOutcome e` collapses on outcome `y` equals the state after `m` collapses on the
corresponding original outcome `e y`:

`(m.reindexOutcome e).postMeasurement ρ y hy = m.postMeasurement ρ (e y) _`.

Post-measurement states depend only on the outcome operator (`Measurement.postMeasurement_congr`),
and `(m.reindexOutcome e).op y = m.op (e y)` by construction (`reindexOutcome_op`) — the Postulate-4
sibling of `reindexOutcome_bornProb`. -/
theorem reindexOutcome_postMeasurement (m : Measurement ι S) (e : Y ≃ ι) (ρ : State S) (y : Y)
    (hy : (m.reindexOutcome e).bornProb ρ y ≠ 0) :
    (m.reindexOutcome e).postMeasurement ρ y hy
      = m.postMeasurement ρ (e y) (by rwa [reindexOutcome_bornProb] at hy) :=
  Measurement.postMeasurement_congr (reindexOutcome_op m e y) ρ hy _

end Measurement

end AxQM
