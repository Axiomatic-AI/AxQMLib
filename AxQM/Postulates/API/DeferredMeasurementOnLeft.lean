/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DeferredMeasurement
import AxQM.Postulates.API.MeasurementPrecompose

/-!
# Deferring a right-factor gate past a left-factor measurement (the disjoint-factor commutation)

The deferred-measurement engine (`DeferredMeasurement.lean`, N&C §4.4 / Exercise 4.35) commutes a
gate `g` past a measurement `m` on a system `S` whenever `Mᵢ g = Wᵢ Mᵢ` (operator commutation). The
sibling `DeferredMeasurementOnRight.lean` handles the case where a gate and a measurement act on the
*same* right factor; this file handles the complementary **disjoint-factor** case, where the gate
and the measurement touch *different* tensor factors.

Nielsen & Chuang's measured quantum Fourier transform (Problem 5.2) reads `qftEvolution` off the
qubit tower `qubit ⊗ S` and measures the head wire with `controlMeasurement S = m.onLeft S` (a
*left*-factor measurement). Its Figure 5.1 head-layer peel leaves the recursive tail QFT
`(qftTowerEvolution n).onRight qubit` (a *right*-factor gate `1 ⊗ V`, idle on the head wire) applied
*after* the head control cascade. To measure the head wire the reduction must first push that head
measurement past the tail QFT — but the tail QFT touches only the right factor, disjoint from the
head, so it defers **unchanged** (its own branch gate on every outcome). This file supplies exactly
that.

Let `m : Measurement ι S` be the left-factor measurement and `V : Evolution T` the right-factor
gate. On `S ⊗ T` the operators are `(m.onLeft T).op i = Mᵢ ⊗ 1` and `(V.onRight S).op = 1 ⊗ V`, and
they commute on disjoint factors (`onLeft_op_comm_onRight_op`):

  `(Mᵢ ⊗ 1)(1 ⊗ V) = Mᵢ ⊗ V = (1 ⊗ V)(Mᵢ ⊗ 1)`.

So `V.onRight S` defers past `m.onLeft T` with the branch family the gate itself (`Wᵢ = V.onRight S`
for every `i`): the two readings are the instances of the single-measurement
`bornProb_evolve_of_comm` / `postMeasurement_evolve_of_comm` at that commutation.

* `Measurement.bornProb_evolve_onLeft_of_comm` — the right-factor gate is **invisible to the
  statistics** of the left-factor measurement (Postulate 3), `p(i ∣ (1⊗V) ρ (1⊗V)†) = p(i ∣ ρ)`.
* `Measurement.postMeasurement_evolve_onLeft_of_comm` — the left-factor **post-measurement state
  defers the right-factor gate** unchanged (Postulate 4),
  `postMeas((1⊗V) ρ (1⊗V)†, i) = (1⊗V) · postMeas(ρ, i)`.

## Generality

The conclusions hold for an arbitrary measurement `m`, gate `V`, extra factor `T`, and state on `S ⊗
T`, no dimension specialized. Unlike the siblings `DeferredMeasurement` /
`DeferredMeasurementOnRight`, the two theorem statements here have no commutation premise `hcomm :
Mᵢ g = Wᵢ Mᵢ`, because the disjoint-factor commutation is *unconditional*: it is discharged inside
the proofs by `onLeft_op_comm_onRight_op` and
`Measurement.{bornProb,postMeasurement}_evolve_of_comm`. The tower-specific application, specialized
to `controlMeasurement (qtower n qubit)`, is `AxQM/Core/QtowerHeadIdleMeasurement.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- **A right-factor gate is invisible to the statistics of a left-factor measurement** (Postulate
3). On `S ⊗ T`, the left-factor measurement `m.onLeft T` (operators `Mᵢ ⊗ 1`) does not see the
right-factor gate `V.onRight S = 1 ⊗ V`: the Born probability of outcome `i` on the evolved state
`(1⊗V) ρ (1⊗V)†` equals that on `ρ`,

  `p(i ∣ (1⊗V) ρ (1⊗V)†) = p(i ∣ ρ)`.

The instance of `bornProb_evolve_of_comm` at the gate `V.onRight S`, whose (self-)commutation with
`m.onLeft T` is the disjoint-factor `onLeft_op_comm_onRight_op` (`Mᵢ ⊗ V` either way). This is the
`hL`-side reading the measured-QFT outer induction uses to push the head-wire measurement past the
recursive tail QFT (N&C Problem 5.2). -/
theorem bornProb_evolve_onLeft_of_comm (m : Measurement ι S) {T : QSystem} (V : Evolution T)
    (ρ : State (S.compose T)) (i : ι) :
    (m.onLeft T).bornProb ((V.onRight S).evolve ρ) i = (m.onLeft T).bornProb ρ i :=
  bornProb_evolve_of_comm (m.onLeft T) (V.onRight S) (fun _ => V.onRight S)
    (fun i => onLeft_op_comm_onRight_op m V i) ρ i

/-- **The post-measurement state defers a right-factor gate past a left-factor measurement**
(Postulate 4). On `S ⊗ T`, the state after measuring outcome `i` of the left-factor measurement
`m.onLeft T` on the right-factor-gate input `(1⊗V) ρ (1⊗V)†` equals that same right-factor gate
`V.onRight S = 1 ⊗ V` applied to the state after measuring `ρ`:

  `postMeas((1⊗V) ρ (1⊗V)†, i) = (1 ⊗ V) · postMeas(ρ, i)`.

The right-factor gate **defers past** the left-factor measurement unchanged (its own branch gate on
every outcome), because they act on disjoint tensor factors and so commute
(`onLeft_op_comm_onRight_op`). The outcome is equally possible after `1⊗V` because the probabilities
agree (`bornProb_evolve_onLeft_of_comm`). The instance of `postMeasurement_evolve_of_comm` at the
gate `V.onRight S` and the constant branch family. This is the collapse reading the measured-QFT
outer induction uses to carry the recursive tail QFT past the head-wire measurement (N&C Problem
5.2). -/
theorem postMeasurement_evolve_onLeft_of_comm (m : Measurement ι S) {T : QSystem} (V : Evolution T)
    (ρ : State (S.compose T)) (i : ι) (hp : (m.onLeft T).bornProb ρ i ≠ 0) :
    (m.onLeft T).postMeasurement ((V.onRight S).evolve ρ) i
        (by rw [bornProb_evolve_onLeft_of_comm]; exact hp)
      = (V.onRight S).evolve ((m.onLeft T).postMeasurement ρ i hp) :=
  postMeasurement_evolve_of_comm (m.onLeft T) (V.onRight S) (fun _ => V.onRight S)
    (fun i => onLeft_op_comm_onRight_op m V i) ρ i hp

end Measurement

end AxQM
