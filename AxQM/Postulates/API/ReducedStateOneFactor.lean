/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasurementSimulation
import AxQM.Postulates.PartialTrace
import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract

/-!
# Reduced operators of a post-measurement bipartite pure state

Reduced operators used in **Nielsen & Chuang, Proposition 12.14** (the LOCC reduction,
`AxQM/NC/Ch12/Proposition12_14.lean`). N&C's measurement-simulation argument (Eq. (12.159))
compares the reduced density operators of two post-measurement states: after **Bob** measures `Mⱼ`
on the right factor of a bipartite pure state, *Bob's* marginal is `Mⱼ ρ_B Mⱼ† / p`; after **Alice**
measures `Nⱼ` on the left factor, *Alice's* marginal is `Nⱼ ρ_A Nⱼ† / p`. This file records
those two conjugation identities, in the form the general (off swap-symmetric normal form) lift
uses.

The engine is the partial-trace kept-factor equivariance
(`LinearMap.partialTrace{Left,Right}_tensorMap_id_comp` and its `_comp_tensorMap_id` mirror):
tracing out one factor carries an operator on the *surviving* factor straight through the partial
trace as a two-sided conjugation. The post-measurement state operator is the normalized conjugation
`Mⱼ ρ Mⱼ† / p` (`ContinuousLinearMap.postState`/`postOp`, `Measurement.postMeasurement`); for `Mⱼ`
acting on a single factor (`Measurement.onRight`/`onLeft`, `TensorProduct.mapL _ 1`), the
kept-factor operator passes through the partial trace, leaving `Mⱼ ρ_{B/A} Mⱼ† / p` on that
factor. The
normalization constant is `(bornProb)⁻¹` via `Measurement.bornProb_eq_re_trace_postOp`.

Proof style mirrors `State.reducedRight_evolve_id_tmul` (a local unitary on one party conjugates
that party's marginal): the post-measurement operator is written as a **raw** `TensorProduct.map`
two-sided conjugation (`hbridge`), then the equivariance lemmas are applied — one by `rw`, the other
by `exact` under a `congr` (the `QSystem.compose` instance blocks a direct rewrite of the second).
As in `NC/Ch4/Exercise4_32.lean`, `TensorProduct.adjoint_mapL` is unusable on `onRight`/`onLeft`'s
`1 ⊗ Mⱼ`, so the adjoint is routed through `LinearMap.adjoint` via `TensorProduct.adjoint_map`.

## Main statements

* `Measurement.reducedRight_postMeasurement_onRight_op` — Bob's marginal after Bob's measurement:
  `((m.onRight S).postMeasurement ψ j).reducedRight.op = (bornProb)⁻¹ · (Mⱼ ρ_B Mⱼ†)`.
* `Measurement.reducedLeft_postMeasurement_onLeft_op` — Alice's marginal after Alice's measurement,
  for an arbitrary (possibly mixed) input `ρ : State (S ⊗ T)`:
  `((m.onLeft T).postMeasurement ρ j).reducedLeft.op = (bornProb)⁻¹ · (Nⱼ ρ_A Nⱼ†)`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap (adjoint)

noncomputable section

namespace AxQM

variable {S T : QSystem} {ι : Type*} [Fintype ι]

/-- **Bob's marginal after Bob's measurement.** After Bob measures `m` on the right factor `T` of a
bipartite pure state `ψ` and obtains a possible outcome `j`, his reduced density operator equals
`(bornProb)⁻¹ · (Mⱼ ρ_B Mⱼ†)`, where `Mⱼ = m.op j` and `ρ_B = tr_S|ψ⟩⟨ψ|`. This is exactly N&C's
"the post-measurement state has, on Bob's factor, `Mⱼ ρ_B Mⱼ†` (up to normalization)". The
post-measurement operator is the normalized conjugation `(1⊗Mⱼ) |ψ⟩⟨ψ| (1⊗Mⱼ)† / p`
(`Measurement.postMeasurement`, `ContinuousLinearMap.postState`/`postOp`); the kept-factor operator
`Mⱼ` passes through the left partial trace by equivariance, leaving `Mⱼ ρ_B Mⱼ† / p`. -/
theorem Measurement.reducedRight_postMeasurement_onRight_op (m : Measurement ι T)
    (ψ : PureState (S ⊗ T)) (j : ι) (h : (m.onRight S).bornProb ψ.toState j ≠ 0) :
    ((m.onRight S).postMeasurement ψ.toState j h).reducedRight.op
      = (((m.onRight S).bornProb ψ.toState j : ℝ) : ℂ)⁻¹ •
          ((m.op j).comp (ψ.toState.reducedRight.op.comp (adjoint (m.op j)))) := by
  -- The post-measurement operator as a `(bornProb)⁻¹`-scaled two-sided `1 ⊗ Mⱼ` conjugation, at the
  -- raw `TensorProduct.map` / `LinearMap` level; the adjoint routed through `LinearMap.adjoint`.
  have hbridge : ((m.onRight S).postMeasurement ψ.toState j h).op.toLinearMap
      = (((m.onRight S).bornProb ψ.toState j : ℝ) : ℂ)⁻¹ •
          (TensorProduct.map LinearMap.id (↑(m.op j) : T.space →ₗ[ℂ] T.space) ∘ₗ
            ψ.toState.op.toLinearMap ∘ₗ
            TensorProduct.map LinearMap.id
              (LinearMap.adjoint (↑(m.op j) : T.space →ₗ[ℂ] T.space))) := by
    rw [Measurement.postMeasurement_op]
    simp only [ContinuousLinearMap.postState]
    rw [← Measurement.bornProb_eq_re_trace_postOp]
    simp only [ContinuousLinearMap.postOp, ContinuousLinearMap.toLinearMap_smul,
      Measurement.onRight_op,
      ]
    congr 3
    -- Restate over the generic tensor-product instances, where `toLinearMap_comp` applies.
    let ρ : S.space ⊗[ℂ] T.space →L[ℂ] S.space ⊗[ℂ] T.space := ψ.toState.op
    change (((TensorProduct.mapL (1 : S.space →L[ℂ] S.space) (m.op j)).comp
        (ρ.comp (adjoint (TensorProduct.mapL (1 : S.space →L[ℂ] S.space) (m.op j))))) :
          S.space ⊗[ℂ] T.space →ₗ[ℂ] S.space ⊗[ℂ] T.space) = _
    rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
      TensorProduct.adjoint_mapL, TensorProduct.toLinearMap_mapL, TensorProduct.toLinearMap_mapL,
      ContinuousLinearMap.adjoint_one, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id,
      ← ContinuousLinearMap.adjoint_toLinearMap]
    rfl
  rw [State.reducedRight_op, hbridge, LinearMap.partialTraceLeft_smul,
    LinearMap.partialTraceLeft_tensorMap_id_comp]
  apply ContinuousLinearMap.coe_injective
  rw [LinearMap.coe_toContinuousLinearMap, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
    ← ContinuousLinearMap.adjoint_toLinearMap, State.reducedRight_op,
    LinearMap.coe_toContinuousLinearMap]
  congr 2
  exact LinearMap.partialTraceLeft_comp_tensorMap_id (stdOrthonormalBasis ℂ S.space)
    (LinearMap.adjoint (↑(m.op j) : T.space →ₗ[ℂ] T.space)) ψ.toState.op.toLinearMap

/-- **Alice's marginal after Alice's measurement.** After Alice measures `m` on the left factor `S`
of a bipartite state `ρ` (possibly mixed) and obtains a possible outcome `j`, her reduced density
operator is `(bornProb)⁻¹ · (Nⱼ ρ_A Nⱼ†)`, where `Nⱼ = m.op j` and `ρ_A = tr_T ρ`. Mirror of
`Measurement.reducedRight_postMeasurement_onRight_op`, and exactly N&C's Alice-side simulating
marginal `Nⱼ ρ_A Nⱼ†`. Stated for an arbitrary input `ρ : State (S ⊗ T)`: the proof works at the
operator level throughout and never uses purity (the pure-input case is the instance
`ρ = ψ.toState`, used e.g. in the measured-QFT head-wire collapse of Problem 5.2). -/
theorem Measurement.reducedLeft_postMeasurement_onLeft_op (m : Measurement ι S)
    (ρ : State (S ⊗ T)) (j : ι) (h : (m.onLeft T).bornProb ρ j ≠ 0) :
    ((m.onLeft T).postMeasurement ρ j h).reducedLeft.op
      = (((m.onLeft T).bornProb ρ j : ℝ) : ℂ)⁻¹ •
          ((m.op j).comp (ρ.reducedLeft.op.comp (adjoint (m.op j)))) := by
  have hbridge : ((m.onLeft T).postMeasurement ρ j h).op.toLinearMap
      = (((m.onLeft T).bornProb ρ j : ℝ) : ℂ)⁻¹ •
          (TensorProduct.map (↑(m.op j) : S.space →ₗ[ℂ] S.space) LinearMap.id ∘ₗ
            ρ.op.toLinearMap ∘ₗ
            TensorProduct.map
              (LinearMap.adjoint (↑(m.op j) : S.space →ₗ[ℂ] S.space)) LinearMap.id) := by
    rw [Measurement.postMeasurement_op]
    simp only [ContinuousLinearMap.postState]
    rw [← Measurement.bornProb_eq_re_trace_postOp]
    simp only [ContinuousLinearMap.postOp, ContinuousLinearMap.toLinearMap_smul,
      Measurement.onLeft_op,
      ]
    congr 3
    -- Restate over the generic tensor-product instances, where `toLinearMap_comp` applies.
    let σ : S.space ⊗[ℂ] T.space →L[ℂ] S.space ⊗[ℂ] T.space := ρ.op
    change (((TensorProduct.mapL (m.op j) (1 : T.space →L[ℂ] T.space)).comp
        (σ.comp (adjoint (TensorProduct.mapL (m.op j) (1 : T.space →L[ℂ] T.space))))) :
          S.space ⊗[ℂ] T.space →ₗ[ℂ] S.space ⊗[ℂ] T.space) = _
    rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
      TensorProduct.adjoint_mapL, TensorProduct.toLinearMap_mapL, TensorProduct.toLinearMap_mapL,
      ContinuousLinearMap.adjoint_one, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id,
      ← ContinuousLinearMap.adjoint_toLinearMap]
    rfl
  rw [State.reducedLeft_op, hbridge, LinearMap.partialTraceRight_smul,
    LinearMap.partialTraceRight_tensorMap_id_comp]
  apply ContinuousLinearMap.coe_injective
  rw [LinearMap.coe_toContinuousLinearMap, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
    ← ContinuousLinearMap.adjoint_toLinearMap, State.reducedLeft_op,
    LinearMap.coe_toContinuousLinearMap]
  congr 2
  exact LinearMap.partialTraceRight_comp_tensorMap_id (stdOrthonormalBasis ℂ T.space)
    (LinearMap.adjoint (↑(m.op j) : S.space →ₗ[ℂ] S.space)) ρ.op.toLinearMap

end AxQM
