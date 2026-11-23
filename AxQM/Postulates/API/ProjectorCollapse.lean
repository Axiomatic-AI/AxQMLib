/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasurementOperation
import AxQM.Postulates.API.PureState

/-!
# Collapse of a rank-one projective measurement outcome

The state-update rule (Postulate 4) for an outcome whose measurement operator is a **rank-one
projector** onto a unit vector `|φ⟩`: obtaining that outcome collapses the register to `|φ⟩⟨φ|`,
**independent of the input state** — even a mixed one.

`Measurement.postMeasurement_toState_of_op_eq_rankOne` is the mixed-input companion of
`Measurement.postMeasurement_toState_of_op_eq_smul` (which needs a *pure* input). A rank-one
projective outcome fully collapses the register, so the post-measurement state carries no memory of
`ρ`. This is the fact behind "a computational-basis measurement of a register leaves the recorded
basis state" — the collapse of a joint computational-basis wire measurement onto its outcome ket.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- **A rank-one projective outcome collapses any input to the projector state.** If the measurement
operator of outcome `i` is the rank-one projector `Mᵢ = |φ⟩⟨φ|` onto a unit vector `|φ⟩`
(`meas.op i = rankOne φ.vec φ.vec`), then obtaining outcome `i` collapses **any** input state `ρ`
(mixed or pure) to the pure state `|φ⟩⟨φ|`:

  `postMeas(ρ, i) = φ.toState`.

The mixed-input companion of `Measurement.postMeasurement_toState_of_op_eq_smul`, which needs a pure
input. The rank-one sandwich `Mᵢ ρ Mᵢ† = ⟪φ, ρ φ⟫ • |φ⟩⟨φ|`
(`opElement`, via `adjoint_rankOne` / `comp_rankOne` / `rankOne_comp_rankOne`) makes the
post-measurement operator a scalar multiple of `|φ⟩⟨φ|`; the collapsed state is a genuine state, so
its trace is `1` (`State.trace_op_eq_one`), forcing the scalar to `1` (`trace_rankOne` with `φ` a
unit vector). The input `ρ` enters only through the scalar, which the trace normalisation discards —
the collapse forgets `ρ` entirely. -/
theorem Measurement.postMeasurement_toState_of_op_eq_rankOne
    (meas : Measurement ι S) (φ : PureState S) (ρ : State S) (i : ι)
    (hop : meas.op i = InnerProductSpace.rankOne ℂ φ.vec φ.vec)
    (hp : meas.bornProb ρ i ≠ 0) :
    meas.postMeasurement ρ i hp = φ.toState := by
  set v := φ.vec with hv
  -- The rank-one sandwich `Eᵢ(ρ) = Mᵢ ρ Mᵢ† = ⟪v, ρ v⟫ • |v⟩⟨v|`.
  have hsand : meas.opElement ρ i
      = (inner ℂ v (ρ.op v)) • InnerProductSpace.rankOne ℂ v v := by
    rw [Measurement.opElement_eq_postOp]
    simp only [ContinuousLinearMap.postOp]
    rw [hop, InnerProductSpace.adjoint_rankOne, InnerProductSpace.comp_rankOne,
      InnerProductSpace.rankOne_comp_rankOne]
  have hvv : inner ℂ v v = (1 : ℂ) := φ.inner_self
  have htrace : (LinearMap.trace ℂ S.space) ↑(InnerProductSpace.rankOne ℂ v v) = 1 := by
    rw [InnerProductSpace.trace_rankOne, hvv]
  -- The post-measurement operator is `((p(i))⁻¹ · ⟪v, ρ v⟫) • |v⟩⟨v|`.
  have hred : (meas.postMeasurement ρ i hp).op
      = ((meas.bornProb ρ i : ℂ)⁻¹ * inner ℂ v (ρ.op v)) • InnerProductSpace.rankOne ℂ v v := by
    rw [Measurement.postMeasurement_op_eq_bornProb_smul_opElement, hsand, smul_smul]
  -- Trace-one of the collapsed state pins the scalar to `1`.
  have hd1 : (meas.bornProb ρ i : ℂ)⁻¹ * inner ℂ v (ρ.op v) = 1 := by
    have h1 := State.trace_op_eq_one (meas.postMeasurement ρ i hp)
    rw [hred, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul, htrace, mul_one] at h1
    exact h1
  apply State.ext
  rw [hred, hd1, one_smul, PureState.toState_op, hv]

end AxQM
