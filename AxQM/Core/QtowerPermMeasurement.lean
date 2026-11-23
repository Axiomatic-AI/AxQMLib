/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QtowerWirePermutation
import AxQM.Core.QtowerMeasurement
import AxQM.Postulates.API.DeferredMeasurementReindex

/-!
# AxQM — a wire permutation defers past the terminal measurement (swaps ↦ relabelling)

The wire-permutation gate `Evolution.qtowerPermWires σ` (`AxQM/Core/QtowerWirePermutation.lean`)
defers past the terminal per-wire computational-basis measurement `qtowerMeasurement n`
(`AxQM/Core/QtowerMeasurement.lean`) as a pure **relabelling of the classical outcomes**: measuring
outcome `r` after the permutation is measuring outcome `r ∘ σ` before it, and the collapsed state is
the permutation applied to the collapsed state of that relabelled outcome.

* `qtowerPermWires_measure_bornProb` — the outcome statistics are relabelled:
  `p(r ∣ σ·ρ·σ†) = p(r ∘ σ ∣ ρ)`.
* `qtowerPermWires_measure_postMeasurement` — the collapse defers the permutation:
  `postMeas(σ·ρ·σ†, r) = σ · postMeas(ρ, r ∘ σ)`; on a computational-basis collapsed state the
  permutation is just a wire relabelling.

This is the step of **Nielsen & Chuang, Problem 5.2** that removes the swap network at the end
of the quantum Fourier transform (Figure 5.1): the swaps, applied immediately before the terminal
measurement, contribute only a permutation of the recorded measurement bits — *no two-qubit gate
survives*. The peel `qftTowerEvolution_succ_eq_qftHeadLayer_peel` leaves such a cyclic wire
permutation `Φ` outermost, and the measured-QFT reduction absorbs it here.

## Proof

Each public statement is a one-line projection of the private `qtowerPermWires_measure_defers`,
which applies the reindexing engine
`Measurement.{bornProb,postMeasurement}_evolve_of_reindex_comm`
(`AxQM/Postulates/API/DeferredMeasurementReindex.lean`) to the shared setup.

The shared work is the reindexing commutation `Mᵣ (σ) = (σ) M_{r∘σ}` (`hcomm` below) —
each measurement operator is the rank-one projector onto its tower basis vector `towerKet` (via the
faithfulness `qtowerMeasurement_eq_congr_quditMeasurement`), and the unitary permutation carries the
projector of outcome `r` onto that of the relabelled outcome `r ∘ σ`
(`comp_rankOne_self_comp_adjoint`). The two statements that consume it are bundled into one `∧`
so that this operator-level setup is proved once, as in the sibling `qtowerHeadPhaseCascade`
deferrals of `AxQM/NC/Ch5/`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {n : ℕ}

/-- **Bundled deferral of a wire permutation past the terminal measurement** (private engine). Both
the Born-probability relabelling and the post-measurement deferral, exposed from a *single* proof so
that the operator-level setup they share — the reindexing commutation `Mᵣ (qtowerPermWires σ) =
(qtowerPermWires σ) M_{r∘σ}` (`hcomm`) — is discharged exactly once. The public projections are
`qtowerPermWires_measure_bornProb` and `qtowerPermWires_measure_postMeasurement`. -/
private theorem qtowerPermWires_measure_defers (σ : Equiv.Perm (Fin (n + 1))) :
    (∀ (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2),
        (qtowerMeasurement n).bornProb ((Evolution.qtowerPermWires σ).evolve ρ) r
          = (qtowerMeasurement n).bornProb ρ (fun j => r (σ j)))
    ∧ (∀ (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2)
          (hp : (qtowerMeasurement n).bornProb ρ (fun j => r (σ j)) ≠ 0)
          (hp' : (qtowerMeasurement n).bornProb ((Evolution.qtowerPermWires σ).evolve ρ) r ≠ 0),
        (qtowerMeasurement n).postMeasurement ((Evolution.qtowerPermWires σ).evolve ρ) r hp'
          = (Evolution.qtowerPermWires σ).evolve
              ((qtowerMeasurement n).postMeasurement ρ (fun j => r (σ j)) hp)) := by
  -- The outcome relabelling `e r = r ∘ σ` induced by the wire permutation `σ`.
  let e : (Fin (n + 1) → Fin 2) ≃ (Fin (n + 1) → Fin 2) :=
    { toFun := fun r j => r (σ j)
      invFun := fun r j => r (σ.symm j)
      left_inv := fun r => by funext j; simp
      right_inv := fun r => by funext j; simp }
  -- Each terminal-measurement operator is the rank-one projector onto its tower basis vector, via
  -- the measurement's faithfulness to the register computational-basis measurement.
  have hMop : ∀ b : Fin (n + 1) → Fin 2,
      (qtowerMeasurement n).op b = rankOne ℂ (towerKet n b).vec (towerKet n b).vec := by
    intro b
    have hvec : (quditPowTower n).toIsometry (quditBasis (towerMeasurementOutcomeEquiv n b)).vec
        = (towerKet n b).vec := by
      rw [← PureState.congr_vec,
        show towerMeasurementOutcomeEquiv n b = finFunctionFinEquiv (fun j => b j.rev) from rfl,
        quditPowTower_congr_quditBasis_rev]
    rw [qtowerMeasurement_eq_congr_quditMeasurement, Measurement.reindexOutcome_op,
      Measurement.congr_op, quditMeasurement_op, InnerProductSpace.rankOne_conjStarAlgEquiv, hvec]
  -- The permutation gate on a tower basis vector: `qtowerPermWires σ |b⟩ = |b ∘ σ⁻¹⟩`.
  have hVvec : ∀ b : Fin (n + 1) → Fin 2,
      (Evolution.qtowerPermWires σ).op (towerKet n b).vec
        = (towerKet n (fun i => b (σ.symm i))).vec := by
    intro b
    rw [← Evolution.evolvePure_vec, qtowerPermWires_evolvePure_towerKet]
  -- The reindexing commutation `Mᵢ V = V M_{e i}` the engine consumes.
  have hcomm : ∀ i : Fin (n + 1) → Fin 2,
      ((qtowerMeasurement n).op i).comp (Evolution.qtowerPermWires σ).op
        = (Evolution.qtowerPermWires σ).op.comp ((qtowerMeasurement n).op (fun j => i (σ j))) := by
    intro i
    rw [hMop i, hMop (fun j => i (σ j))]
    have hconj : rankOne ℂ (towerKet n i).vec (towerKet n i).vec
        = (Evolution.qtowerPermWires σ).op.comp
            ((rankOne ℂ (towerKet n (fun j => i (σ j))).vec
                (towerKet n (fun j => i (σ j))).vec).comp
              (adjoint (Evolution.qtowerPermWires σ).op)) := by
      rw [ContinuousLinearMap.comp_rankOne_self_comp_adjoint, hVvec (fun j => i (σ j))]
      simp only [Equiv.apply_symm_apply]
    rw [hconj]
    simp only [ContinuousLinearMap.comp_assoc,
      (Evolution.qtowerPermWires σ).adjoint_comp_self]
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
  refine ⟨fun ρ r => ?_, fun ρ r hp hp' => ?_⟩
  · exact Measurement.bornProb_evolve_of_reindex_comm (qtowerMeasurement n)
      (Evolution.qtowerPermWires σ) (fun _ => Evolution.qtowerPermWires σ) e hcomm ρ r
  · exact Measurement.postMeasurement_evolve_of_reindex_comm (qtowerMeasurement n)
      (Evolution.qtowerPermWires σ) (fun _ => Evolution.qtowerPermWires σ) e hcomm ρ r hp

/-- **Problem 5.2 (the swap network is invisible to the terminal statistics).** Measuring every wire
of the tower (`qtowerMeasurement n`) after the wire-permutation gate `Evolution.qtowerPermWires σ`
gives, for every outcome bit-string `r`, the Born probability of the *relabelled* outcome `r ∘ σ` on
the input `ρ`:

  `p(r ∣ (qtowerPermWires σ) ρ (qtowerPermWires σ)†) = p(r ∘ σ ∣ ρ)`.

The permutation only relabels which wire carries which measured bit — a classical relabelling of the
outcome, no two-qubit gate. -/
theorem qtowerPermWires_measure_bornProb (σ : Equiv.Perm (Fin (n + 1)))
    (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2) :
    (qtowerMeasurement n).bornProb ((Evolution.qtowerPermWires σ).evolve ρ) r
      = (qtowerMeasurement n).bornProb ρ (fun j => r (σ j)) :=
  (qtowerPermWires_measure_defers σ).1 ρ r

/-- **Problem 5.2 (the terminal measurement defers the swap network).** The state after applying the
wire-permutation gate `Evolution.qtowerPermWires σ` and *then* measuring every wire, at outcome `r`,
equals the permutation applied to the state obtained by measuring the *relabelled* outcome `r ∘ σ`
first:

  `postMeas(σ·ρ·σ†, r) = σ · postMeas(ρ, r ∘ σ)`   (`σ = qtowerPermWires σ`).

On the collapsed computational-basis state the permutation is a pure wire relabelling; the swap
network at the end of the quantum Fourier transform (Figure 5.1) has become a relabelling of the
classical measurement record. -/
theorem qtowerPermWires_measure_postMeasurement (σ : Equiv.Perm (Fin (n + 1)))
    (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2)
    (hp : (qtowerMeasurement n).bornProb ρ (fun j => r (σ j)) ≠ 0) :
    (qtowerMeasurement n).postMeasurement ((Evolution.qtowerPermWires σ).evolve ρ) r
        (by rw [qtowerPermWires_measure_bornProb]; exact hp)
      = (Evolution.qtowerPermWires σ).evolve
          ((qtowerMeasurement n).postMeasurement ρ (fun j => r (σ j)) hp) :=
  (qtowerPermWires_measure_defers σ).2 ρ r hp (by rw [qtowerPermWires_measure_bornProb]; exact hp)

end AxQM
