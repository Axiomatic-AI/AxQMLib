/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QtowerHeadPhaseControl
import AxQM.Core.QftTowerPhaseRecursion

/-!
# The quantum Fourier transform's Figure 5.1 head layer (N&C Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) is assembled by an induction over the tower
depth whose one step *peels* the head control wire's Figure 5.1 gates off `qftTowerEvolution (n+1)`
and recurses on the tail. Those head gates are the **head layer**: a Hadamard on the head wire `0`
followed by the head control wire's cascade of controlled-`Rₖ` phase rotations onto every tail wire.
This file computes the head layer's action on a computational tower ket — the computational content
the peel matches — and, crucially, *where* the head layer deposits its phase.

## The head layer produces the *last* output wire

Chunk 3b-v-j established that `qftEvolution` is the **symmetric** DFT: the head Hadamard + cascade
imprint the phase of the *last* output wire, not the head (`qftTowerWirePhase_last`). This file
makes that concrete at the state level. On the input `towerKet (n+1) b`:

* the head Hadamard sends the head wire's basis state `|b 0⟩` to the phased-plus state
  `|+_{π·b 0}⟩` (`hadamardGate_evolvePure_qubitBasis_qubitPhasePlus`), the tail
  `towerKet n (Fin.tail b)` untouched (`qtowerSingleWire_zero_hadamardGate_evolvePure_towerKet`);
* the head control wire's controlled-`Rₖ` phase cascade then advances that phased-plus head by the
  total phase `∑ₜ (Fin.tail b t)·(2π·2^{t.rev}/2ⁿ⁺²)`
  (`qtowerHeadCtrlPhaseCascade_evolvePure_qubitPhasePlus`), the tail still untouched.

So the head layer sends `towerKet (n+1) b` to `|+_{θ}⟩ ⊗ towerKet n (Fin.tail b)` with
`θ = π·(b 0) + ∑ₜ (Fin.tail b t)·(2π·2^{t.rev}/2ⁿ⁺²)` — which is *exactly*
`qftTowerWirePhase (n+1) b (Fin.last (n+1))`, the last output wire's phase
(`qftTowerWirePhase_last`). The head wire ends in the last output wire's phased-plus state, no wire
entangled with the head. This identifies the head-produced content and is why the outer-induction
peel needs a cyclic wire permutation to route the head wire to the last position.

## What is formalised

* `qftHeadRotationList n` — the head control wire's Figure 5.1 rotation phases: for each tail wire
  `t : Fin (n+1)`, the angle `2π·2^{t.rev}/2ⁿ⁺²` (`= 2π/2^{t+2}`, the QFT's `Rₜ₊₂`).
* `qftHeadLayer n` — the **head layer** as an `Evolution` on `qtower (n+1) qubit`: the head control
  wire's controlled-`Rₖ` phase cascade after the head Hadamard.
* `qtowerSingleWire_zero_hadamardGate_evolvePure_towerKet` — the head Hadamard's action on a tower
  ket: `H` on wire `0` sends `towerKet (n+1) b` to `|+_{π·b 0}⟩ ⊗ towerKet n (Fin.tail b)`.
* `qftHeadLayer_evolvePure_towerKet` — the **head layer's action**: it sends `towerKet (n+1) b` to
  `|+_{θ}⟩ ⊗ towerKet n (Fin.tail b)` with `θ = qftTowerWirePhase (n+1) b (Fin.last (n+1))`, the
  last output wire's phase — the head layer produces the last output wire.

It composes the head phase cascade and the phase recursion. The Hadamard-to-phased-plus fact it
uses, `hadamardGate_evolvePure_qubitBasis_qubitPhasePlus`, is a single-qubit identity in
`AxQM/Postulates/API/PhasedPlus.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The QFT head control wire's Figure 5.1 rotation phases.** For each tail wire `t : Fin (n+1)`,
the head control wire drives a controlled phase rotation of angle
`2π·2^{t.rev}/2ⁿ⁺²` (equal to `2π/2^{t+2}`, the quantum Fourier transform's `Rₜ₊₂`). Written in the
`2π·2^{t.rev}/2ⁿ⁺²` form so that the head layer's total advance matches the last output wire's phase
`qftTowerWirePhase_last` term by term. The gates on distinct tail wires are diagonal and commute, so
the list order (here `List.finRange (n+1)`) is immaterial. -/
def qftHeadRotationList (n : ℕ) : List (Fin (n + 1) × ℝ) :=
  (List.finRange (n + 1)).map fun t => (t, 2 * Real.pi * 2 ^ (t.rev : ℕ) / 2 ^ (n + 2))

/-- **The QFT's Figure 5.1 head layer** as an `Evolution` on `qtower (n+1) qubit`: a Hadamard on
the head wire `0` (`Evolution.qtowerSingleWire (n+1) 0 hadamardGate`) followed by the head control
wire's cascade of controlled-`Rₖ` phase gates onto the tail wires — one
`Evolution.qtowerCtrlWire (n+1) 0 t.succ (phaseShiftGate φ)` per `(t, φ)` of
`qftHeadRotationList n`, all controlled on the head wire. These are exactly the Figure 5.1 gates the
head control wire
carries; the head layer is what the outer-induction peel of the measured-QFT reduction reads off
`qftTowerEvolution (n+1)` before recursing on the tail. -/
def qftHeadLayer (n : ℕ) : Evolution (qtower (n + 1) qubit) :=
  ((qftHeadRotationList n).map fun p =>
      Evolution.qtowerCtrlWire (n + 1) 0 p.1.succ (phaseShiftGate p.2)).prod
    * Evolution.qtowerSingleWire (n + 1) 0 hadamardGate

/-- **The head Hadamard's action on a tower ket.** A Hadamard on the head wire `0` sends the
computational tower ket `towerKet (n+1) b` to the phased-plus head `|+_{π·b 0}⟩` tensored with the
untouched tail `towerKet n (Fin.tail b)`:

  `H₀ (towerKet (n+1) b) = |+_{π·(b 0)}⟩ ⊗ towerKet n (Fin.tail b)`.

On wire `0` the single-wire gate is `hadamardGate` on the head factor
(`Evolution.qtowerSingleWire_zero`), and `H|b 0⟩ = |+_{π·(b 0)}⟩`
(`hadamardGate_evolvePure_qubitBasis_qubitPhasePlus`); the tail factor `towerKet n (Fin.tail b)` is
carried through unchanged. This is the input the head control wire's phase cascade then acts on. -/
theorem qtowerSingleWire_zero_hadamardGate_evolvePure_towerKet (n : ℕ) (b : Fin (n + 2) → Fin 2) :
    (Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolvePure (towerKet (n + 1) b)
      = (qubitPhasePlus (Real.pi * ((b 0 : ℕ) : ℝ))).tmul (towerKet n (Fin.tail b)) := by
  rw [Evolution.qtowerSingleWire_zero, towerKet_succ]
  -- the tower head-peel `qtower (n+1) qubit = qubit ⊗ qtower n qubit` is only definitional, so
  -- `onLeft_evolvePure` matches up to reducible defeq (`erw`), not syntactically.
  erw [Evolution.onLeft_evolvePure]
  rw [hadamardGate_evolvePure_qubitBasis_qubitPhasePlus]
  rfl

/-- **Problem 5.2 (the Figure 5.1 head layer produces the last output wire).** The QFT's head layer
`qftHeadLayer n` sends the computational tower ket `towerKet (n+1) b` to the phased-plus head
`|+_{θ}⟩` tensored with the untouched tail `towerKet n (Fin.tail b)`, where
`θ = qftTowerWirePhase (n+1) b (Fin.last (n+1))` is the **last** output wire's QFT phase:

  `qftHeadLayer n (towerKet (n+1) b)
    = |+_{qftTowerWirePhase (n+1) b (Fin.last (n+1))}⟩ ⊗ towerKet n (Fin.tail b)`.

The head Hadamard puts the head wire into `|+_{π·(b 0)}⟩`
(`qtowerSingleWire_zero_hadamardGate_evolvePure_towerKet`) and the head control wire's
controlled-`Rₖ` cascade advances it by `∑ₜ (Fin.tail b t)·(2π·2^{t.rev}/2ⁿ⁺²)`
(`qtowerHeadCtrlPhaseCascade_evolvePure_qubitPhasePlus`), the tail untouched throughout — no wire
entangled with the head. Because `qftEvolution` is the **symmetric** DFT, that total angle is
exactly the *last* output wire's phase (`qftTowerWirePhase_last`), not the head
wire's. This is why the outer-induction peel routes the head-produced wire to the last position by a
cyclic wire
permutation. -/
theorem qftHeadLayer_evolvePure_towerKet (n : ℕ) (b : Fin (n + 2) → Fin 2) :
    (qftHeadLayer n).evolvePure (towerKet (n + 1) b)
      = (qubitPhasePlus (qftTowerWirePhase (n + 1) b (Fin.last (n + 1)))).tmul
          (towerKet n (Fin.tail b)) := by
  rw [qftHeadLayer, Evolution.mul_def, Evolution.evolvePure_comp,
    qtowerSingleWire_zero_hadamardGate_evolvePure_towerKet,
    qtowerHeadCtrlPhaseCascade_evolvePure_qubitPhasePlus, qftTowerWirePhase_last]
  -- The head cascade's total advance is the last output wire's Fourier fraction, term by term.
  have hsum : ((qftHeadRotationList n).map fun p => p.2 * ((Fin.tail b p.1 : ℕ) : ℝ)).sum
      = ∑ t : Fin (n + 1),
          ((Fin.tail b t : ℕ) : ℝ) * (2 * Real.pi * 2 ^ (t.rev : ℕ) / 2 ^ (n + 2)) := by
    rw [qftHeadRotationList, List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  rw [hsum]

end AxQM
