/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HolevoMeasurementChannel
import AxQM.Postulates.API.Mixture

/-!
# AxQM.Postulates.API — the outcome marginal of the Holevo measurement operation

The **apparatus outcome marginal** of the Holevo measurement operation `𝓔` (Nielsen & Chuang,
Exercise 12.2 / Eq. (12.8), `AxQM.holevoMeasurementChannel`): after `𝓔` measures the
system `Q` with POVM `{E_y}` and *records* the outcome in the apparatus register `M = qudit r`,
**discarding `Q`** leaves the classical diagonal state whose weights are the Born probabilities.

For a measurement `m : Measurement (Fin r) Q` and a system state `σ`, writing
`𝓔(σ ⊗ |0⟩⟨0|) = ∑_y √E_y σ √E_y ⊗ |y⟩⟨y|` (Eq. (12.8)), the `M`-marginal is

  `Tr_Q 𝓔(σ ⊗ |0⟩⟨0|) = ∑_y Tr(E_y σ) |y⟩⟨y| = ∑_y p(y|σ) |y⟩⟨y|`,

the Born distribution `p(y|σ) = m.bornProb σ y` written as a diagonal state on the outcome register.
This is exactly the "measure and record the outcome, forget the post-measurement state" content of
the outcome channel `Measurement.measState` (`Core/MeasurementChannel.lean`), realised here as the
partial trace over `Q` of the concrete apparatus operation `𝓔`.

## Role

This is the **"discard the measured system `Q`" step** of the (Nielsen–Chuang, Theorem 12.1) Holevo
bound proof along the χ-monotonicity / apparatus route (N&C Problem 12.1). That proof runs
`H(X:Y) = χ_M ≤ χ`, where `χ_M` is the Holevo χ of the *measured* ensemble
`{pₓ, Tr_Q 𝓔(ρₓ ⊗ |0⟩⟨0|)}` and `χ` that of `{pₓ, ρₓ}`: the inequality `χ_M ≤ χ` is obtained by
tracing `Q` out of `𝓔(ρₓ ⊗ |0⟩⟨0|)` (Holevo χ monotonicity under discarding, N&C Problem 12.1(1))
after `χ(𝓔∘·) ≤ χ` (monotonicity under the operation `𝓔`, N&C Problem 12.1(2)). This lemma
identifies that traced-out `M`-marginal with the diagonal Born state, connecting the concrete
apparatus `𝓔` (Exercise 12.2) to the outcome distribution used in the Holevo χ.

## Proof

The statement involves `holevoMeasurementChannel` (in
`AxQM/Postulates/API/HolevoMeasurementChannel.lean`), `State.reducedRight`, `State.mix`,
`Measurement.bornProb`, `quditBasis` and `PureState.toState`.
In the proof, `𝓔(σ ⊗ |0⟩⟨0|)`'s operator is the diagonal operator sum
(12.8); the partial trace over `Q` distributes over the sum and (`partialTraceLeft_tensorMap`)
reads off the block traces `Tr(√E_y σ √E_y) = Tr(E_y σ) = p(y|σ)`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {Q : QSystem} {r : ℕ}

/-- **The trace of a POVM block equals the Born probability.** For a measurement `m` and state `σ`,
the trace of the outcome-`y` block `√E_y σ √E_y` of the apparatus operation (with `√E_y = |M_y|` the
absolute value of the measurement operator) is the Born probability of `y`:

`Tr(√E_y σ √E_y) = Tr(E_y σ) = m.bornProb σ y`.

By trace cyclicity `Tr(|M_y| σ |M_y|) = Tr(|M_y| |M_y| σ) = Tr(M_y† M_y σ)` (`absoluteValue_sq`) and
`m.bornProb σ y = Re Tr(M_y σ M_y†) = Re Tr(M_y† M_y σ)` (`bornProb_eq_re_trace_postOp` + trace
cyclicity); both are the same real number `Tr(E_y σ)`, which is genuinely real because
`√E_y σ √E_y` is a positive operator (`trace_postOp_eq_ofReal_re`). -/
theorem trace_absoluteValue_conj_eq_bornProb (m : Measurement (Fin r) Q) (σ : State Q) (y : Fin r) :
    LinearMap.trace ℂ Q.space
        (((m.op y).absoluteValue.comp (σ.op.comp (m.op y).absoluteValue)) : Q.space →ₗ[ℂ] Q.space)
      = (m.bornProb σ y : ℂ) := by
  have habs : (m.op y).absoluteValue.comp (σ.op.comp (m.op y).absoluteValue)
      = ContinuousLinearMap.postOp (fun i => (m.op i).absoluteValue) σ.op y := by
    rw [ContinuousLinearMap.postOp, ContinuousLinearMap.adjoint_absoluteValue,
      ← ContinuousLinearMap.comp_assoc]
  rw [habs, ContinuousLinearMap.trace_postOp_eq_ofReal_re _ σ.isPositive_op y,
    Measurement.bornProb_eq_re_trace_postOp]
  congr 2
  rw [ContinuousLinearMap.trace_postOp, ContinuousLinearMap.trace_postOp,
    ContinuousLinearMap.adjoint_absoluteValue, ← ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.absoluteValue_sq, ContinuousLinearMap.comp_assoc]

variable [NeZero r]

/-- **The apparatus outcome marginal of the Holevo measurement operation is the diagonal Born
state.** Tracing out the measured system `Q` from `𝓔(σ ⊗ |0⟩⟨0|)` (Nielsen & Chuang, Exercise 12.2 /
Eq. (12.8)) yields the classical diagonal state whose weight on `|y⟩⟨y|` is the Born probability of
outcome `y`:

`Tr_Q 𝓔(σ ⊗ |0⟩⟨0|) = ∑_y m.bornProb σ y • |y⟩⟨y|`.

This is the "discard the measured system, keep the recorded outcome" step of the Holevo bound
(Theorem 12.1) via the apparatus route: the traced-out marginal is exactly the measure-and-record
outcome distribution (`Measurement.measState`). The proof reads `𝓔(σ ⊗ |0⟩⟨0|)`'s operator as the
diagonal operator sum `∑_y √E_y σ √E_y ⊗ |y⟩⟨y|` (`holevoMeasurementChannel_apply_tmul`), pushes the
partial trace over `Q` through the sum, and evaluates each block by `partialTraceLeft_tensorMap`
with `Tr(√E_y σ √E_y) = m.bornProb σ y` (`trace_absoluteValue_conj_eq_bornProb`). -/
theorem holevoMeasurementChannel_reducedRight (m : Measurement (Fin r) Q) (σ : State Q) :
    (holevoMeasurementChannel m (σ ⊗ (quditBasis (0 : Fin r)).toState)).reducedRight
      = State.mix (m.bornProb σ) (m.bornProb_nonneg σ) (m.sum_bornProb_eq_one σ)
          (fun y => (quditBasis y).toState) := by
  apply State.ext
  rw [State.reducedRight_op, holevoMeasurementChannel_apply_tmul, State.mix_op,
    ContinuousLinearMap.toLinearMap_sum, ← LinearMap.partialTraceLeftLM_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [LinearMap.partialTraceLeftLM_apply, TensorProduct.toLinearMap_mapL,
    LinearMap.partialTraceLeft_tensorMap, map_smul,
    ContinuousLinearMap.toLinearMap_toContinuousLinearMap, trace_absoluteValue_conj_eq_bornProb]

end AxQM
