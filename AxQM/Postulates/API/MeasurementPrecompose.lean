/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CompositeMeasurement

/-!
# AxQM — pre-composing a measurement with a unitary, and trivial collapse

Two small measurement facts shared by the **Nielsen & Chuang Proposition 12.14**
LOCC reduction (`AxQM/Core/LOCCProtocol.lean`), where the reduction induction must *absorb* a local
unitary applied just before a measurement into the measurement itself.

* `Measurement.precompose m U` — the measurement with operator `Mᵢ U` for outcome `i` (measure `m`
  *after* first applying the unitary `U`). Its Born probabilities and post-measurement states on a
  state `ρ` coincide with those of `m` on the evolved state `U ρ U†` (`postOp_precompose`,
  `precompose_bornProb`), and it commutes with the left-factor lift (`precompose_onLeft_op`), so an
  Alice-side pre-unitary folds into Alice's measurement operators
  (`onLeft_precompose_bornProb` / `onLeft_precompose_postMeasurement`).
* `Measurement.postMeasurement_eq_self_of_op_eq_one` — a measurement whose operator for a possible
  outcome `i` is the identity (`Mᵢ = 1`) does not disturb the state: `postMeas(ρ, i) = ρ`. This
  makes the identity/`certain`-outcome measurement a "do nothing" round.

-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- **Pre-composing a measurement by a unitary** `U`: the measurement with operators `Mᵢ ↦ Mᵢ U`,
i.e. "apply `U` first, then measure `m`". Still a measurement — the completeness relation is
conjugated, `∑ᵢ (Mᵢ U)† (Mᵢ U) = U† (∑ᵢ Mᵢ† Mᵢ) U = U† · 1 · U = 1` (unitarity `U† U = 1`). Its
statistics on `ρ` are those of `m` on `U ρ U†` (`precompose_bornProb`, `postOp_precompose`). -/
def precompose (m : Measurement ι S) (U : Evolution S) : Measurement ι S where
  op i := (m.op i).comp U.op
  complete := by
    have key : ∀ i, (adjoint ((m.op i).comp U.op)).comp ((m.op i).comp U.op)
        = (adjoint U.op).comp (((adjoint (m.op i)).comp (m.op i)).comp U.op) := by
      intro i
      rw [ContinuousLinearMap.adjoint_comp]
      simp only [ContinuousLinearMap.comp_assoc]
    rw [Finset.sum_congr rfl fun i _ => key i, ← ContinuousLinearMap.comp_finsetSum,
      ← ContinuousLinearMap.finsetSum_comp, m.complete]
    simp only [← ContinuousLinearMap.mul_def, one_mul]
    rw [ContinuousLinearMap.mul_def]
    exact U.adjoint_comp_self

/-- The operators of a pre-composed measurement: `(m.precompose U).op i = Mᵢ U`. -/
@[simp] theorem precompose_op (m : Measurement ι S) (U : Evolution S) (i : ι) :
    (m.precompose U).op i = (m.op i).comp U.op := rfl

/-- **Branch-operator identity for pre-composition.** The unnormalized post-measurement operator of
outcome `i` for `m.precompose U` on `ρ` equals that of `m` on the evolved state `U ρ U†`:
`(Mᵢ U) ρ (Mᵢ U)† = Mᵢ (U ρ U†) Mᵢ†`. Carries both the probability equality and the post-state
equality below. -/
theorem postOp_precompose (m : Measurement ι S) (U : Evolution S) (ρ : State S) (i : ι) :
    ContinuousLinearMap.postOp (m.precompose U).op ρ.op i
      = ContinuousLinearMap.postOp m.op (U.evolve ρ).op i := by
  simp only [ContinuousLinearMap.postOp, precompose_op, Evolution.evolve_op,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

/-- **Pre-composition does not change the outcome statistics** (Postulate 3): measuring
`m.precompose U` on `ρ` has the same Born probabilities as measuring `m` on `U ρ U†`. -/
theorem precompose_bornProb (m : Measurement ι S) (U : Evolution S) (ρ : State S) (i : ι) :
    (m.precompose U).bornProb ρ i = m.bornProb (U.evolve ρ) i := by
  rw [bornProb_eq_re_trace_postOp, bornProb_eq_re_trace_postOp, postOp_precompose]

/-- **Pre-composition, on the post-measurement state** (Postulate 4): the state after measuring
`m.precompose U` on `ρ` equals the state after measuring `m` on the evolved input `U ρ U†`:
`postMeas(m.precompose U, ρ, i) = postMeas(m, U ρ U†, i)`. The Postulate-4 sibling of
`precompose_bornProb`; both follow from the branch-operator identity `postOp_precompose`
(`(Mᵢ U) ρ (Mᵢ U)† = Mᵢ (U ρ U†) Mᵢ†`), which carries the normalization along too. -/
theorem precompose_postMeasurement (m : Measurement ι S) (U : Evolution S) (ρ : State S) (i : ι)
    (hp : (m.precompose U).bornProb ρ i ≠ 0) :
    (m.precompose U).postMeasurement ρ i hp
      = m.postMeasurement (U.evolve ρ) i (by rwa [precompose_bornProb] at hp) := by
  apply State.ext
  rw [postMeasurement_op, postMeasurement_op, ContinuousLinearMap.postState,
    ContinuousLinearMap.postState, postOp_precompose]

/-- **Pre-composition commutes with the left-factor lift** (at the operator level): the measurement
operators of `(m.precompose U).onLeft T` and `(m.onLeft T).precompose (U.onLeft T)` agree — both are
`(Mᵢ ⊗ 1)(U ⊗ 1) = (Mᵢ U) ⊗ 1`. -/
theorem precompose_onLeft_op (m : Measurement ι S) (U : Evolution S) (T : QSystem) :
    ((m.precompose U).onLeft T).op = ((m.onLeft T).precompose (U.onLeft T)).op := by
  funext i
  simp only [onLeft_op, precompose_op, Evolution.onLeft, Evolution.tmul_op, Evolution.id_op]
  exact TensorProduct.mapL_mul_one (m.op i) U.op

/-- **Left-lifted pre-composition, on probabilities**: Alice measuring `(m.precompose U)` (lifted to
the left factor) on `ρ` has the same Born probabilities as Alice measuring `m` on
`(U ⊗ 1) ρ (U ⊗ 1)†` — the local pre-unitary `U` folds into Alice's measurement. -/
theorem onLeft_precompose_bornProb (m : Measurement ι S) (U : Evolution S) (T : QSystem)
    (ρ : State (S.compose T)) (i : ι) :
    ((m.precompose U).onLeft T).bornProb ρ i
      = (m.onLeft T).bornProb ((U.onLeft T).evolve ρ) i := by
  rw [bornProb_eq_re_trace_postOp, bornProb_eq_re_trace_postOp, precompose_onLeft_op,
    postOp_precompose]

/-- **Left-lifted pre-composition, on the post-measurement state**: the state after Alice measures
`(m.precompose U)` (lifted) on `ρ` equals the state after Alice measures `m` on the evolved input
`(U ⊗ 1) ρ (U ⊗ 1)†`. This absorbs an Alice-side pre-unitary into her measurement in the
Proposition 12.14 reduction. -/
theorem onLeft_precompose_postMeasurement (m : Measurement ι S) (U : Evolution S) (T : QSystem)
    (ρ : State (S.compose T)) (i : ι) (hp : ((m.precompose U).onLeft T).bornProb ρ i ≠ 0) :
    ((m.precompose U).onLeft T).postMeasurement ρ i hp
      = (m.onLeft T).postMeasurement ((U.onLeft T).evolve ρ) i
          (by rwa [onLeft_precompose_bornProb] at hp) := by
  apply State.ext
  rw [postMeasurement_op, postMeasurement_op, ContinuousLinearMap.postState,
    ContinuousLinearMap.postState, precompose_onLeft_op, postOp_precompose]

/-- **A left-factor measurement operator commutes with a right-factor unitary operator.** On
`S ⊗ T`, Alice's measurement operator `Mᵢ ⊗ 1` (`(m.onLeft T).op i`) commutes with Bob's `1 ⊗ V`
(`(V.onRight S).op`): both composites equal `Mᵢ ⊗ V`. This is the disjoint-factor commutation that
lets a Bob-local unitary defer past an Alice measurement in the Proposition 12.14 reduction. -/
theorem onLeft_op_comm_onRight_op {T : QSystem} (m : Measurement ι S) (V : Evolution T) (i : ι) :
    ((m.onLeft T).op i).comp (V.onRight S).op = (V.onRight S).op.comp ((m.onLeft T).op i) := by
  have hmapL : ∀ (a : S.space →L[ℂ] S.space) (b : T.space →L[ℂ] T.space),
      (TensorProduct.mapL a (1 : T.space →L[ℂ] T.space)).comp (TensorProduct.mapL 1 b)
        = (TensorProduct.mapL (1 : S.space →L[ℂ] S.space) b).comp (TensorProduct.mapL a 1) := by
    intro a b
    rw [← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp]
    simp only [← ContinuousLinearMap.mul_def, mul_one, one_mul]
  simp only [Measurement.onLeft_op, Evolution.onRight, Evolution.tmul_op, Evolution.id_op]
  exact hmapL (m.op i) V.op

/-- **A trivial-outcome measurement does not disturb the state.** If the operator `Mᵢ` of a possible
outcome `i` is the identity (`Mᵢ = 1`), then the post-measurement state for that outcome is `ρ`
itself: `Mᵢ ρ Mᵢ† / p(i) = 1 · ρ · 1 / 1 = ρ`. Makes the identity round (and the `certain`-outcome
measurement) a "do nothing" step. -/
theorem postMeasurement_eq_self_of_op_eq_one (m : Measurement ι S) (ρ : State S) (i : ι)
    (h : m.op i = 1) (hp : m.bornProb ρ i ≠ 0) : m.postMeasurement ρ i hp = ρ := by
  apply State.ext
  have hpost : ContinuousLinearMap.postOp m.op ρ.op i = ρ.op := by
    simp only [ContinuousLinearMap.postOp, h, ← ContinuousLinearMap.star_eq_adjoint, star_one,
      ← ContinuousLinearMap.mul_def, one_mul, mul_one]
  have htr : RCLike.re (LinearMap.trace ℂ S.space (ρ.op : S.space →ₗ[ℂ] S.space)) = 1 := by
    rw [ρ.isDensity.trace_eq_one, RCLike.one_re]
  rw [postMeasurement_op, ContinuousLinearMap.postState, hpost, htr]
  simp

end Measurement

end AxQM
