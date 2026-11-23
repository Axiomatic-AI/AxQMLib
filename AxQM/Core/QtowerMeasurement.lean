/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QftTowerBasis
import AxQM.Postulates.API.ControlMeasurementCommute
import AxQM.Postulates.API.CascadedMeasurement
import AxQM.Postulates.API.MeasurementReindex
import AxQM.Postulates.API.MeasurementExt
import AxQM.Postulates.API.QuditMeasurement
import AxQM.Postulates.API.ProjectorCollapse

/-!
# The terminal per-wire measurement on the control tower (N&C Problem 5.2)

The measured quantum Fourier transform (N&C Problem 5.2) ends by measuring **every wire** of the
output register in the computational basis. The QFT unitary and each Figure 5.1 gate are
transported onto the `(n+1)`-qubit control tower `qtower n qubit` in
`AxQM/Core/QftTowerCircuit.lean`; this file constructs the other half of the circuit — the
*terminal measurement* — as a wire-addressed object on the same tower, so the whole-circuit
semiclassical reduction can defer it, wire by wire, past the controlled-`Rₖ` cascades.

## The object

`qtowerMeasurement n : Measurement (Fin (n+1) → Fin 2) (qtower n qubit)` is the joint
computational-basis measurement of all `n+1` wires, built **head-first** to match the tower
recursion `qtower (n+1) qubit = qubit ⊗ qtower n qubit` and the cascade deferral of
`AxQM/NC/Ch5/Problem5_2.lean` (which measures the head control wire with `controlMeasurement`):

* `qtowerMeasurement 0` measures the single wire — the qudit computational measurement
  `quditMeasurement 2` on `qtower 0 qubit = qubit`, its `Fin 2` outcome relabelled to
  `Fin 1 → Fin 2`.
* `qtowerMeasurement (n+1)` is the **cascade** (`Measurement.cascade`, N&C Ex. 2.57) of
  `controlMeasurement (qtower n qubit)` (measure the head wire `0`) with
  `(qtowerMeasurement n).onRight qubit` (measure the remaining `n+1` wires), its
  `Fin 2 × (Fin (n+1) → Fin 2)` outcome relabelled to `Fin (n+2) → Fin 2` by `Fin.consEquiv`. The
  two operators act on disjoint tensor factors, so the cascade order is immaterial.

The recursion makes the head peel `qtowerMeasurement_succ` **definitional**: it exhibits the head
wire's measurement as exactly the `controlMeasurement` that the cascade-deferral theorems
consume, with the rest of the tower measured by the recursive tail — the shape the semiclassical
induction needs.

## Faithfulness

`qtowerMeasurement_eq_congr_quditMeasurement` proves this per-wire measurement **is** the register's
computational-basis measurement: measuring the single `2ⁿ⁺¹`-level register `qudit (2ⁿ⁺¹)` — where
the QFT output lives — in the computational basis `quditMeasurement (2ⁿ⁺¹)`, transported onto the
tower by the register bridge `quditPowTower n`, equals `qtowerMeasurement n` (up to the wire↔index
relabelling `finFunctionFinEquiv ∘ (· ∘ Fin.rev)`, the same little-endian/big-endian reconciliation
`Fin.rev` the gate re-expressions use). So "measure every wire in the computational basis" and
"measure the register in the computational basis" are the same measurement — the measurement N&C
performs after the QFT, now wire-addressed on the tower.

The proof matches the two projective measurements operator-by-operator. Each `qtowerMeasurement`
operator is the rank-one projector onto the tower basis vector `towerKet n b` (`key`, by induction:
the head peel splits it as `|b 0⟩⟨b 0| ⊗ (rest)` via `rankOne_tmul_self`); the transported
`quditMeasurement` operator is the projector onto
`quditPowTower n • |finFunctionFinEquiv (b ∘ rev)⟩ = towerKet n b` (the bridge dictionary
`quditPowTower_congr_quditBasis_apply`, with `rankOne_conjStarAlgEquiv` carrying the projector
through the isometry). Equal operators give equal measurements (`Measurement.ext_op`).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The terminal per-wire computational-basis measurement on the control tower.**
`qtowerMeasurement n` measures all `n+1` wires of `qtower n qubit` in the computational basis,
recording the bit-string `Fin (n+1) → Fin 2` of outcomes. Built head-first to match the tower
recursion: the head wire is measured with `controlMeasurement`, the remaining wires by the recursive
tail, joined by `Measurement.cascade` (with the outcome sets relabelled by `Fin.consEquiv` and, at
the base, `Equiv.funUnique`). This is the measurement the measured-QFT circuit performs after the
transported quantum Fourier transform (`qftTowerEvolution`). -/
def qtowerMeasurement : (n : ℕ) → Measurement (Fin (n + 1) → Fin 2) (qtower n qubit)
  | 0 => (quditMeasurement 2).reindexOutcome (Equiv.funUnique (Fin 1) (Fin 2))
  | n + 1 =>
      ((controlMeasurement (qtower n qubit)).cascade
        ((qtowerMeasurement n).onRight qubit)).reindexOutcome
          (Fin.consEquiv (fun _ : Fin (n + 2) => Fin 2)).symm

/-- Base unfolding: a single-wire tower is measured by the qudit computational measurement. -/
theorem qtowerMeasurement_zero :
    qtowerMeasurement 0 = (quditMeasurement 2).reindexOutcome (Equiv.funUnique (Fin 1) (Fin 2)) :=
  rfl

/-- **Head peel of the terminal measurement** (definitional). `qtowerMeasurement (n+1)` measures the
head control wire `0` with `controlMeasurement (qtower n qubit)` and the remaining wires with the
recursive tail `(qtowerMeasurement n).onRight qubit`, cascaded and relabelled by `Fin.consEquiv`.
This exhibits the terminal all-wire measurement as the `controlMeasurement` of the head wire
followed by the rest — exactly the shape the semiclassical reduction defers past a
control wire's controlled-`Rₖ` cascade (`controlledUnitaryCascade_measure_control_*`). -/
theorem qtowerMeasurement_succ (n : ℕ) :
    qtowerMeasurement (n + 1) =
      ((controlMeasurement (qtower n qubit)).cascade
        ((qtowerMeasurement n).onRight qubit)).reindexOutcome
          (Fin.consEquiv (fun _ : Fin (n + 2) => Fin 2)).symm :=
  rfl

/-- The wire↔register-index relabelling `b ↦ |finFunctionFinEquiv (b ∘ Fin.rev)⟩`: a tower wire
bit-string is read as the little-endian register index after the `Fin.rev` endianness flip (the
same flip the Figure 5.1 gate re-expressions carry). It relabels the register's
`Fin (2ⁿ⁺¹)` outcome set to the tower's `Fin (n+1) → Fin 2` wire outcomes. -/
def towerMeasurementOutcomeEquiv (n : ℕ) : (Fin (n + 1) → Fin 2) ≃ Fin (2 ^ (n + 1)) :=
  (Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin 2))).trans finFunctionFinEquiv

/-- **The terminal per-wire measurement is the register's computational-basis measurement.**
Measuring every wire of the tower in the computational basis (`qtowerMeasurement n`) equals the
single-register computational-basis measurement `quditMeasurement (2ⁿ⁺¹)` — the measurement N&C
performs on the QFT output — transported onto the tower by the register bridge `quditPowTower n`,
with the outcome sets matched by `towerMeasurementOutcomeEquiv`. So "measure each of the `n+1` wires
in the computational basis" *is* "measure the `2ⁿ⁺¹`-level register in the computational basis": the
per-wire object is faithful to the measured quantum Fourier transform, not merely some measurement
on the tower.

The proof matches the two projective measurements operator-by-operator. Each `qtowerMeasurement`
operator is the rank-one projector onto the tower basis vector `towerKet n b` (`key`, by induction:
the head peel `qtowerMeasurement_succ` splits it as `|b 0⟩⟨b 0| ⊗ (rest)` via `rankOne_tmul_self`);
the transported `quditMeasurement` operator is the projector onto
`quditPowTower n • |finFunctionFinEquiv (b ∘ rev)⟩ = towerKet n b` (the bridge dictionary
`quditPowTower_congr_quditBasis_apply`, with `rankOne_conjStarAlgEquiv` carrying the projector
through the isometry). Equal operators give equal measurements. -/
theorem qtowerMeasurement_eq_congr_quditMeasurement (n : ℕ) :
    qtowerMeasurement n =
      (Measurement.congr (quditPowTower n) (quditMeasurement (2 ^ (n + 1)))).reindexOutcome
        (towerMeasurementOutcomeEquiv n) := by
  -- Each `qtowerMeasurement` operator is the projector onto the tower basis vector `towerKet m b`.
  have key : ∀ (m : ℕ) (b : Fin (m + 1) → Fin 2),
      (qtowerMeasurement m).op b = rankOne ℂ (towerKet m b).vec (towerKet m b).vec := by
    intro m
    induction m with
    | zero =>
      intro b
      rw [qtowerMeasurement_zero, Measurement.reindexOutcome_op, quditMeasurement_op, towerKet_zero]
      rw [quditBasis_vec, qubitBasis_vec]
      rfl
    | succ k ih =>
      intro b
      have hstep : (qtowerMeasurement (k + 1)).op b
          = TensorProduct.mapL (rankOne ℂ (qubitBasis (b 0)).vec (qubitBasis (b 0)).vec)
              (rankOne ℂ (towerKet k (fun i => b i.succ)).vec
                (towerKet k (fun i => b i.succ)).vec) := by
        rw [qtowerMeasurement_succ, Measurement.reindexOutcome_op, Measurement.cascade_op,
          Measurement.onRight_op, controlMeasurement_op, ih,
          show ((Fin.consEquiv fun _ : Fin (k + 2) => Fin 2).symm b).1 = b 0 from rfl,
          show ((Fin.consEquiv fun _ : Fin (k + 2) => Fin 2).symm b).2 = fun i => b i.succ from rfl]
        refine (TensorProduct.mapL_comp _ _ _ _).symm.trans ?_
        simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
          ContinuousLinearMap.comp_id]
      rw [hstep, towerKet_succ, PureState.tmul_vec]
      exact (InnerProductSpace.rankOne_tmul_self _ _).symm
  -- Match the two measurements operator-by-operator.
  refine Measurement.ext_op fun b => ?_
  rw [key n b, Measurement.reindexOutcome_op, Measurement.congr_op, quditMeasurement_op,
    InnerProductSpace.rankOne_conjStarAlgEquiv]
  -- The transported register ket is the tower basis vector, by the bridge dictionary.
  have hvec : (quditPowTower n).toIsometry (quditBasis (towerMeasurementOutcomeEquiv n b)).vec
      = (towerKet n b).vec := by
    rw [← PureState.congr_vec,
      show towerMeasurementOutcomeEquiv n b = finFunctionFinEquiv (fun j => b j.rev) from rfl,
      quditPowTower_congr_quditBasis_rev]
  rw [hvec]

/-- **The joint computational-basis measurement collapses any input to its outcome ket.** Measuring
every wire of the tower in the computational basis (`qtowerMeasurement n`) and obtaining the
bit-string `r` leaves the register in the corresponding computational-basis tower state
`towerKet n r` — **independent of the input state** `ρ` (mixed or pure):

  `postMeas(ρ, r) = (towerKet n r).toState`.

A joint computational-basis measurement is projective and rank-one, so every wire is left definite
and the collapsed state remembers nothing of `ρ` beyond the recorded outcome. Its operator at `r` is
the rank-one projector `|towerKet n r⟩⟨towerKet n r|`, obtained here by **reusing** the
already-proven register identity `qtowerMeasurement_eq_congr_quditMeasurement` (rather than
re-running its head-peel `key` induction) and the shared bridge lemma
`quditPowTower_congr_quditBasis_rev`, so the projector collapse
`Measurement.postMeasurement_toState_of_op_eq_rankOne` applies. The reusable
state-update companion of the statistics; applied to `ρ = qftTowerEvolution n · ρ₀`, it gives the
collapsed state of the measured quantum Fourier transform (N&C Problem 5.2). -/
theorem qtowerMeasurement_postMeasurement_eq_towerKet (n : ℕ) (ρ : State (qtower n qubit))
    (r : Fin (n + 1) → Fin 2) (hp : (qtowerMeasurement n).bornProb ρ r ≠ 0) :
    (qtowerMeasurement n).postMeasurement ρ r hp = (towerKet n r).toState := by
  -- The measurement operator at `r` is the rank-one projector onto `towerKet n r`. Obtain it by
  -- reusing the register identity `qtowerMeasurement_eq_congr_quditMeasurement` (avoiding a re-run
  -- of its head-peel `key` induction): push `.op` through the reindex/congr and the register
  -- measurement (`quditMeasurement_op`), then transport the projector along the bridge lemma
  -- `quditPowTower_congr_quditBasis_rev`.
  have hop : (qtowerMeasurement n).op r
      = rankOne ℂ (towerKet n r).vec (towerKet n r).vec := by
    rw [qtowerMeasurement_eq_congr_quditMeasurement, Measurement.reindexOutcome_op,
      Measurement.congr_op, quditMeasurement_op, InnerProductSpace.rankOne_conjStarAlgEquiv]
    have hvec : (quditPowTower n).toIsometry (quditBasis (towerMeasurementOutcomeEquiv n r)).vec
        = (towerKet n r).vec := by
      rw [← PureState.congr_vec, show towerMeasurementOutcomeEquiv n r
        = finFunctionFinEquiv (fun j => r j.rev) from rfl, quditPowTower_congr_quditBasis_rev]
    rw [hvec]
  exact Measurement.postMeasurement_toState_of_op_eq_rankOne _ (towerKet n r) ρ r hop hp

end AxQM
