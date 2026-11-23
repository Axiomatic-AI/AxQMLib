/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QftTowerPeel
import AxQM.Core.QtowerPermMeasurement
import AxQM.Core.QtowerHeadIdleMeasurement
import AxQM.Core.DeferredMeasurementReading

/-!
# Deferrals of the measured-QFT outer induction (N&C Problem 5.2)

The measured quantum Fourier transform (Problem 5.2) is assembled by an outer induction over the
tower depth `n`, processing the Figure 5.1 **head-layer peel**
`qftTowerEvolution (n+1) = Φ · qftTailEvolution n · qftHeadLayer n`
(`qftTowerEvolution_succ_eq_qftHeadLayer_peel`) one control wire at a time under the terminal
per-wire measurement `qtowerMeasurement (n+1)`. Here
`Φ = Evolution.qtowerPermWires (finRotate (n+2)).symm` is the cyclic wire permutation routing the
head-produced output wire into place, and `qftTailEvolution n = (qftTowerEvolution n).onRight qubit`
is the recursive tail QFT on wires `1, …, n+1`, idle on the head wire `0`.

This file records **two steps of that induction** — the ones that need neither the
`Measurement.cascade` split (N&C Ex. 2.57) nor the head-cascade reading engine. They isolate, at the
scale of the whole transported QFT, the two Figure 5.1 gate shapes that carry **no genuine two-qubit
gate** into the semiclassical circuit:

* **The final swap network becomes a classical relabelling of the outcome.** Peeling the head layer
exposes `Φ` as the *outermost* gate before the terminal measurement, and `Φ` — a
  bare wire permutation — defers past that measurement
  (`qtowerPermWires_measure_{bornProb,postMeasurement}`) as a pure relabelling `r ↦ r ∘ σ` of the
  recorded bit-string, `σ = (finRotate (n+2)).symm`. So the measured `(n+1)`-tower QFT reduces to
  the **swap-free** circuit `qftTailEvolution n · qftHeadLayer n` measured, with the outcome read
  through `σ`: `qftTowerEvolution_succ_measure_swapDefer_{bornProb,postMeasurement}`. This is the
  outermost step of the outer induction; it removes the Figure 5.1 swap layer from all further
  reasoning, at no cost of a two-qubit gate.

* **The recursive tail QFT slips past the head-wire measurement.** The terminal measurement's head
  factor is `controlMeasurement (qtower n qubit)` (measure wire `0`; `qtowerMeasurement_succ`), and
  the tail QFT `qftTailEvolution n = (qftTowerEvolution n).onRight qubit = 1 ⊗ Q`
  leaves wire `0` idle, so it is invisible to the head statistics and defers past the head-wire
  measurement unchanged: `qftTailEvolution_measure_head_{bornProb,postMeasurement}`. These are the
  instances at `g = qftTowerEvolution n` of the head-idle disjoint-factor deferral
  (`controlMeasurement_onRight_measure_head_{bornProb,postMeasurement}`), named for the exact gate
  the outer induction pushes the head-wire measurement past before deferring the head control
  cascade and recursing on the tail (`qtowerMeasurement n` after `qftTowerEvolution n`).

Compare the sibling terminal-measurement deferrals in `AxQM/Core/QtowerPermMeasurement.lean` and
`AxQM/Core/QtowerHeadIdleMeasurement.lean`.
-/

noncomputable section

namespace AxQM

variable {n : ℕ}

/-! ### The final swap network defers past the terminal measurement -/

/-- **Problem 5.2 (the swap network becomes a classical relabelling — outcome statistics).**
Measuring every wire (`qtowerMeasurement (n+1)`) after the whole transported quantum Fourier
transform `qftTowerEvolution (n+1)` gives, for every outcome bit-string `r`, the same Born
probability as measuring after only its **swap-free** part `qftTailEvolution n · qftHeadLayer n`,
with the outcome read through the cyclic relabelling `σ = (finRotate (n+2)).symm`:

  `p(r ∣ qftTowerEvolution (n+1)) = p(r ∘ σ ∣ qftTailEvolution n · qftHeadLayer n)`.

The Figure 5.1 head-layer peel (`qftTowerEvolution_succ_eq_qftHeadLayer_peel`)
exposes the cyclic wire permutation `Φ = Evolution.qtowerPermWires σ` as the outermost gate; being a
bare relabelling of the wires it defers past the terminal measurement
(`qtowerPermWires_measure_bornProb`) as a relabelling `r ↦ r ∘ σ` of the recorded
bits — no two-qubit gate. This is the outermost step of the measured-QFT outer induction. -/
theorem qftTowerEvolution_succ_measure_swapDefer_bornProb
    (ρ : State (qtower (n + 1) qubit)) (r : Fin (n + 2) → Fin 2) :
    (qtowerMeasurement (n + 1)).bornProb ((qftTowerEvolution (n + 1)).evolve ρ) r
      = (qtowerMeasurement (n + 1)).bornProb
          ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ))
          (fun j => r ((finRotate (n + 2)).symm j)) := by
  rw [qftTowerEvolution_succ_evolve_peel, qtowerPermWires_measure_bornProb]

/-- **Problem 5.2 (the swap network becomes a classical relabelling — post-measurement state).**
The state after the whole transported quantum Fourier transform `qftTowerEvolution (n+1)` and
*then* measuring every wire, at outcome `r`, equals the cyclic wire permutation
`Φ = Evolution.qtowerPermWires (finRotate (n+2)).symm` applied to the state obtained from the
**swap-free** circuit `qftTailEvolution n · qftHeadLayer n` measured at the relabelled outcome
`r ∘ σ`:

  `postMeas(qftTowerEvolution (n+1) · ρ, r) = Φ · postMeas(swap-free circuit · ρ, r ∘ σ)`.

On the collapsed computational-basis state `Φ` is a pure wire relabelling: the Figure 5.1 swap layer
at the end of the quantum Fourier transform has become a relabelling of the classical measurement
record, no two-qubit gate. The head-layer peel followed by the swap deferral
(`qtowerPermWires_measure_postMeasurement`); the input state is carried across the peel by
`Measurement.postMeasurement_congr_state`. -/
theorem qftTowerEvolution_succ_measure_swapDefer_postMeasurement
    (ρ : State (qtower (n + 1) qubit)) (r : Fin (n + 2) → Fin 2)
    (hp : (qtowerMeasurement (n + 1)).bornProb
        ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ))
        (fun j => r ((finRotate (n + 2)).symm j)) ≠ 0) :
    (qtowerMeasurement (n + 1)).postMeasurement ((qftTowerEvolution (n + 1)).evolve ρ) r
        (by rw [qftTowerEvolution_succ_measure_swapDefer_bornProb]; exact hp)
      = (Evolution.qtowerPermWires (finRotate (n + 2)).symm).evolve
          ((qtowerMeasurement (n + 1)).postMeasurement
            ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ))
            (fun j => r ((finRotate (n + 2)).symm j)) hp) := by
  refine (Measurement.postMeasurement_congr_state (qtowerMeasurement (n + 1))
    (qftTowerEvolution_succ_evolve_peel ρ) _
    (by rw [qtowerPermWires_measure_bornProb]; exact hp)).trans ?_
  exact qtowerPermWires_measure_postMeasurement _ _ r hp

/-! ### The recursive tail QFT slips past the head-wire measurement -/

/-- **Problem 5.2 (the tail QFT is invisible to the head-wire statistics).** Measuring the head wire
of the tower (`controlMeasurement (qtower n qubit)`, the head factor of the terminal measurement
`qtowerMeasurement (n+1)`) *after* the recursive tail QFT
`qftTailEvolution n = (qftTowerEvolution n).onRight qubit = 1 ⊗ Q` gives, for every outcome `i`, the
same Born probability as measuring the input `ρ` directly: the tail QFT leaves the head wire idle
and so is invisible to the head-wire measurement. The instance at `g = qftTowerEvolution n` of the
head-idle deferral (`controlMeasurement_onRight_measure_head_bornProb`); it is the
step the measured-QFT outer induction uses to push the head-wire measurement past the recursive tail
QFT before deferring the head control cascade and recursing on the tail. -/
theorem qftTailEvolution_measure_head_bornProb
    (ρ : State (qubit ⊗ qtower n qubit)) (i : Fin 2) :
    (controlMeasurement (qtower n qubit)).bornProb ((qftTailEvolution n).evolve ρ) i
      = (controlMeasurement (qtower n qubit)).bornProb ρ i := by
  rw [qftTailEvolution]
  exact controlMeasurement_onRight_measure_head_bornProb (qftTowerEvolution n) ρ i

/-- **Problem 5.2 (the head-wire post-measurement state carries the tail QFT along).** The state
after measuring outcome `i` on the head wire of the tower, applied to the input evolved by the
recursive tail QFT `qftTailEvolution n = (qftTowerEvolution n).onRight qubit = 1 ⊗ Q`, equals that
same tail QFT applied to the state after measuring `ρ`:

  `postMeas((1 ⊗ Q) · ρ, i) = (1 ⊗ Q) · postMeas(ρ, i)`.

The recursive tail QFT **defers past** the head-wire measurement unchanged, because it acts on the
tail factor, disjoint from the measured head wire. The instance at `g = qftTowerEvolution n` of the
head-idle deferral (`controlMeasurement_onRight_measure_head_postMeasurement`); the
outcome is equally possible after the tail QFT because the probabilities agree
(`qftTailEvolution_measure_head_bornProb`). It is the step the measured-QFT outer induction uses to
carry the recursive tail QFT past the head-wire measurement, exposing the tail as
`qtowerMeasurement n` after `qftTowerEvolution n` — the level-`n` measured QFT — for the
recursion. -/
theorem qftTailEvolution_measure_head_postMeasurement
    (ρ : State (qubit ⊗ qtower n qubit)) (i : Fin 2)
    (hp : (controlMeasurement (qtower n qubit)).bornProb ρ i ≠ 0) :
    (controlMeasurement (qtower n qubit)).postMeasurement ((qftTailEvolution n).evolve ρ) i
        (by rw [qftTailEvolution_measure_head_bornProb]; exact hp)
      = (qftTailEvolution n).evolve
          ((controlMeasurement (qtower n qubit)).postMeasurement ρ i hp) := by
  exact controlMeasurement_onRight_measure_head_postMeasurement (qftTowerEvolution n) ρ i hp

end AxQM
