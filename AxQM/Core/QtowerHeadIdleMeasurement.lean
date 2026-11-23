/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QtowerMeasurement
import AxQM.Postulates.API.DeferredMeasurementOnLeft

/-!
# A head-idle gate defers past the terminal measurement's head wire (N&C Problem 5.2)

The measured quantum Fourier transform (Problem 5.2) is assembled by an outer induction over the
tower depth that processes the Figure 5.1 head-layer peel
`qftTowerEvolution (n+1) = Φ · qftTailEvolution n · qftHeadLayer n` one wire at a
time under the terminal per-wire measurement `qtowerMeasurement (n+1)`. That terminal measurement
is a cascade of its **head** factor `controlMeasurement (qtower n qubit)` (measure wire `0`) and the
recursive tail (`qtowerMeasurement_succ`). To defer the head control wire's cascade,
the head-wire measurement must first be pushed leftward past the **recursive tail
QFT** `qftTailEvolution n = (qftTowerEvolution n).onRight qubit` — a right-factor gate `1 ⊗ Q` that
leaves the head wire idle.

That push is a disjoint-factor commutation: the head measurement touches only wire `0` and the tail
QFT only the tail wires, so the tail QFT is **invisible** to the head statistics and **defers past**
the head measurement unchanged. This file records it for an arbitrary head-idle gate `g.onRight
qubit` (the tail QFT is the instance `g = qftTowerEvolution n`), for Born probabilities and for
post-measurement states — thin instances of the disjoint-factor deferral engine
`Measurement.{bornProb,postMeasurement}_evolve_onLeft_of_comm`
(`AxQM/Postulates/API/DeferredMeasurementOnLeft.lean`), since the head measurement
`controlMeasurement (qtower n qubit)` is *by definition* a left-factor measurement
`(·).onLeft (qtower n qubit)`.

Compare the sibling terminal-measurement deferral `AxQM/Core/QtowerPermMeasurement.lean` (the swap
relabelling).
-/

noncomputable section

namespace AxQM

variable {n : ℕ}

/-- **A head-idle gate is invisible to the head-wire statistics.** Measuring the head wire of the
tower (`controlMeasurement (qtower n qubit)`) *after* a right-factor gate `g.onRight qubit = 1 ⊗ g`
that leaves the head wire idle gives, for every outcome `i`, the same Born probability as measuring
the input `ρ` directly: the tail-only gate is invisible to the head-wire measurement. The head
instance of the disjoint-factor engine `Measurement.bornProb_evolve_onLeft_of_comm`, since
`controlMeasurement (qtower n qubit) = (·).onLeft (qtower n qubit)` measures the *left* (head)
factor while `g.onRight qubit = 1 ⊗ g` acts on the *right* (tail) factor. Used by the measured-QFT
outer induction to push the head-wire measurement past the recursive tail QFT `qftTailEvolution n`.
-/
theorem controlMeasurement_onRight_measure_head_bornProb (g : Evolution (qtower n qubit))
    (ρ : State (qubit ⊗ qtower n qubit)) (i : Fin 2) :
    (controlMeasurement (qtower n qubit)).bornProb ((g.onRight qubit).evolve ρ) i
      = (controlMeasurement (qtower n qubit)).bornProb ρ i :=
  Measurement.bornProb_evolve_onLeft_of_comm _ g ρ i

/-- **The head-wire post-measurement state carries a head-idle gate along.** The state after
measuring outcome `i` on the head wire of the tower, applied to the input evolved by a head-idle
right-factor gate `g.onRight qubit = 1 ⊗ g`, equals that same gate applied to the state after
measuring `ρ`:

  `postMeas((1 ⊗ g) ρ (1 ⊗ g)†, i) = (1 ⊗ g) · postMeas(ρ, i)`.

The tail-only gate **defers past** the head-wire measurement unchanged, because it acts on the tail
factor, disjoint from the measured head wire. The head instance of the disjoint-factor engine
`Measurement.postMeasurement_evolve_onLeft_of_comm`; the outcome is equally possible after the gate
because the probabilities agree (`controlMeasurement_onRight_measure_head_bornProb`). Used by the
measured-QFT outer induction to carry the recursive tail QFT `qftTailEvolution n` past the head-wire
measurement before the head control cascade is deferred. -/
theorem controlMeasurement_onRight_measure_head_postMeasurement (g : Evolution (qtower n qubit))
    (ρ : State (qubit ⊗ qtower n qubit)) (i : Fin 2)
    (hp : (controlMeasurement (qtower n qubit)).bornProb ρ i ≠ 0) :
    (controlMeasurement (qtower n qubit)).postMeasurement ((g.onRight qubit).evolve ρ) i
        (by rw [controlMeasurement_onRight_measure_head_bornProb]; exact hp)
      = (g.onRight qubit).evolve
          ((controlMeasurement (qtower n qubit)).postMeasurement ρ i hp) :=
  Measurement.postMeasurement_evolve_onLeft_of_comm _ g ρ i hp

end AxQM
