/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.SystemIso
import AxQM.Postulates.API.KitaevPhaseEstimation

/-!
# Born probability is invariant under system-isomorphism transport

A system isomorphism `e : S ≃ₛ T` is a unitary relabelling of registers; it must not change the
statistics of a measurement. `Measurement.bornProb_congr_congr` records exactly this: transporting
**both** a measurement and the measured pure state along the *same* `e` leaves every Born
probability unchanged,
`(m.congr e).bornProb (ψ.congr e).toState i = m.bornProb ψ.toState i`.

This is the measurement counterpart of the state/observable transport invariance in
`AxQM/Postulates/SystemIso.lean` (`State.expectation_congr`, `PureState.congr_toState`). It is the
bridge that lets a measurement stated on one register be read off a unitarily-relabelled copy —
e.g. reading a single-register computational measurement `quditMeasurement (2ⁿ⁺¹)` off the
`quditPowTower` / `qtowerSplitControl` image of a control register (N&C Problems 5.1, 5.2).

## Proof

The proof reads the Born probability of a pure state as the collapsed
norm `‖Mᵢψ‖²` (`Measurement.bornProb_toState_eq_normSq`) and rides the conjugation identity
`e.conjStarAlgEquiv A (e y) = e (A y)` with the isometry's norm preservation.
-/

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **Born probability is invariant under simultaneous system-isomorphism transport.** For a system
isomorphism `e : S ≃ₛ T`, a measurement `m` on `S`, a pure state `ψ` on `S`, and an outcome `i`,
transporting both the measurement and the state along `e` leaves the Born probability unchanged:
`(m.congr e).bornProb (ψ.congr e).toState i = m.bornProb ψ.toState i`.

A register relabelling is unitary, so it does not change measurement statistics. Proof: the Born
probability of a pure state is the collapsed norm `‖Mᵢψ‖²`
(`Measurement.bornProb_toState_eq_normSq`); transport turns `Mᵢ` into `e.conjStarAlgEquiv Mᵢ` and
`ψ.vec` into `e ψ.vec`, and
`(e.conjStarAlgEquiv Mᵢ) (e ψ.vec) = e (Mᵢ ψ.vec)` (`conjStarAlgEquiv_apply_apply` +
`symm_apply_apply`), whose norm equals `‖Mᵢ ψ.vec‖` since `e` is an isometry (`norm_map`). -/
theorem Measurement.bornProb_congr_congr {ι : Type*} [Fintype ι] (e : S ≃ₛ T)
    (m : Measurement ι S) (ψ : PureState S) (i : ι) :
    (m.congr e).bornProb (ψ.congr e).toState i = m.bornProb ψ.toState i := by
  rw [Measurement.bornProb_toState_eq_normSq, Measurement.bornProb_toState_eq_normSq,
    Measurement.congr_op, PureState.congr_vec,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.norm_map]

end AxQM
