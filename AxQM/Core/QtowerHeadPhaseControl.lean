/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QtowerCtrlWireGate
import AxQM.Postulates.API.ControlledUnitaryPhasePlus
import AxQM.Postulates.API.ControlledUnitaryDecomposition
import AxQM.Postulates.API.TowerProdMultilinear

/-!
# The head control wire's phase cascade rotates a phased-plus head (N&C Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) peels the head control wire's Figure 5.1
gates off `qftTowerEvolution (n+1)`: a Hadamard puts the head wire into a phased-plus superposition,
and then the head wire's cascade of controlled-`Rₖ` phase gates acts on that superposed head with
the tail wires still in the computational basis. This file computes the action of those gates on
exactly such a state — a phased-plus head tensored with a basis tail — the computational heart of
the head layer of the outer-induction peel.

Each Figure 5.1 controlled-`Rₖ` gate the head wire drives is the tower controlled single-wire gate
`Evolution.qtowerCtrlWire (n+1) 0 t.succ (phaseShiftGate φ)` (control the head wire `0`, phase gate
on a tail wire `t.succ`). Since a controlled-*phase* gate is diagonal, on a basis
tail it acts as a scalar phase `e^{iφ·bₜ}` on the target — the "phase kickback" that advances the
control's phased-plus angle rather than entangling the two wires.

## What is formalised

* `qtowerCtrlWire_zero_phaseShiftGate_evolvePure_qubitPhasePlus` — the **single head-controlled
  phase gate** on a phased-plus head:

    `C₀(Rφ on wire t.succ) (|+_α⟩ ⊗ |c⟩) = |+_{α + φ·(c t)}⟩ ⊗ |c⟩`,

  the head wire's angle advancing by `φ` exactly when the target tail wire `t` reads `1`, the tail
  `towerKet n c` returned unchanged.
* `qtowerHeadCtrlPhaseCascade_evolvePure_qubitPhasePlus` — the whole **head phase cascade** on a
  phased-plus head: composing a list `gs` of `(t, φ)` gates advances the head angle by the total
  `∑_{(t,φ)∈gs} φ·(c t)`, the tail `|c⟩` still unchanged — no wire ever entangled with the head.

## Proof

The single gate is `controlledUnitary (Evolution.qtowerSingleWire n t (phaseShiftGate φ))`
(`Evolution.qtowerCtrlWire_ctrl_zero`), and the inner single-wire phase gate acts on the basis tail
`towerKet n c` as the scalar phase `e^{iφ·(c t)}` (the phase gate's diagonal action
`phaseShiftGate_op_apply_qubitBasis` pulled through the product state `towerProd` by its tensor
multilinearity, `towerProd_vec_update_smul`), so the generic
phase-kickback lemma `controlledUnitary_evolvePure_qubitPhasePlus` applies. The cascade is then a
list induction over the single-gate step, the phases summing.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **A single head-controlled phase gate rotates a phased-plus head wire.** The tower controlled
single-wire gate `Evolution.qtowerCtrlWire (n+1) 0 t.succ (phaseShiftGate φ)` — control the head
wire `0`, the phase gate `P(φ)` on the tail wire `t.succ` — sends a phased-plus head tensored with
a basis tail to the phased-plus head with its angle advanced by `φ·(c t)`, the tail unchanged:

  `C₀(P(φ) on t.succ) (|+_α⟩ ⊗ towerKet n c) = |+_{α + φ·(c t)}⟩ ⊗ towerKet n c`.

The gate is `controlledUnitary (Evolution.qtowerSingleWire n t (phaseShiftGate φ))`, and the inner
single-wire phase gate acts diagonally on the basis tail `towerKet n c` as the scalar phase
`e^{iφ·(c t)}`, so the phase-kickback lemma `controlledUnitary_evolvePure_qubitPhasePlus` advances
the control's phased-plus angle by that amount — no entanglement between the head and tail wires. -/
theorem qtowerCtrlWire_zero_phaseShiftGate_evolvePure_qubitPhasePlus (n : ℕ) (t : Fin (n + 1))
    (φ α : ℝ) (c : Fin (n + 1) → Fin 2) :
    (Evolution.qtowerCtrlWire (n + 1) 0 t.succ (phaseShiftGate φ)).evolvePure
        ((qubitPhasePlus α).tmul (towerKet n c))
      = (qubitPhasePlus (α + φ * ((c t : ℕ) : ℝ))).tmul (towerKet n c) := by
  -- The phase gate's diagonal cell `[1, e^{iφ}]_d` is the scalar `e^{iφ·d}`.
  have hcell : ∀ d : Fin 2, (![1, Complex.exp ((φ : ℂ) * Complex.I)] d)
      = Complex.exp (((φ * ((d : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) := by
    intro d; fin_cases d <;> simp
  -- The inner single-wire phase gate acts on the basis tail as the scalar phase `e^{iφ·(c t)}`.
  have hphase : ((phaseShiftGate φ).evolvePure (qubitBasis (c t))).vec
      = Complex.exp (((φ * ((c t : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) • (qubitBasis (c t)).vec := by
    rw [Evolution.evolvePure_vec, phaseShiftGate_op_apply_qubitBasis, hcell (c t)]
  rw [Evolution.qtowerCtrlWire_ctrl_zero]
  apply controlledUnitary_evolvePure_qubitPhasePlus
  -- The inner phase gate scales the wire `t` factor of the basis tail by `e^{iφ·(c t)}`; pull that
  -- scalar out of the whole product via `towerProd`'s tensor multilinearity.
  rw [qtowerSingleWire_evolvePure_towerKet, towerKet_eq_towerProd,
    towerProd_vec_update_smul n (fun j => qubitBasis (c j)) t
      (Complex.exp (((φ * ((c t : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
      ((phaseShiftGate φ).evolvePure (qubitBasis (c t))) hphase]

/-- **The head control wire's whole phase cascade rotates a phased-plus head wire.** Composing the
list `gs` of head-controlled tower phase gates — each `Evolution.qtowerCtrlWire (n+1) 0 p.1.succ
(phaseShiftGate p.2)`, control the head wire `0`, phase gate on tail wire `p.1.succ` — on a
phased-plus head tensored with a basis tail advances the head's phased-plus angle by the total phase
`∑_{(t,φ)∈gs} φ·(c t)`, the tail `towerKet n c` returned unchanged:

  `(∏_{(t,φ)∈gs} C₀(P(φ) on t.succ)) (|+_α⟩ ⊗ towerKet n c)`
    `= |+_{α + ∑ φ·(c t)}⟩ ⊗ towerKet n c`.

Since every gate is a diagonal controlled-phase whose target tail wire stays in the computational
basis, the head wire is never entangled with the tail: the whole cascade acts as a single phase
rotation of the head. A list induction over the single-gate step
(`qtowerCtrlWire_zero_phaseShiftGate_evolvePure_qubitPhasePlus`), the phases summing. This is the
head layer the outer-induction peel of the measured-QFT reduction reads off `qftTowerEvolution`. -/
theorem qtowerHeadCtrlPhaseCascade_evolvePure_qubitPhasePlus (n : ℕ)
    (gs : List (Fin (n + 1) × ℝ)) (α : ℝ) (c : Fin (n + 1) → Fin 2) :
    ((gs.map fun p =>
          Evolution.qtowerCtrlWire (n + 1) 0 p.1.succ (phaseShiftGate p.2)).prod).evolvePure
        ((qubitPhasePlus α).tmul (towerKet n c))
      = (qubitPhasePlus (α + (gs.map fun p => p.2 * ((c p.1 : ℕ) : ℝ)).sum)).tmul
          (towerKet n c) := by
  induction gs with
  | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil, add_zero, Evolution.one_def]
      exact Evolution.id_evolvePure _
  | cons p gs ih =>
      erw [List.map_cons, List.prod_cons, Evolution.mul_def, Evolution.evolvePure_comp, ih,
        qtowerCtrlWire_zero_phaseShiftGate_evolvePure_qubitPhasePlus, List.map_cons, List.sum_cons]
      congr 2
      ring

end AxQM
