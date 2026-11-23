/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HolevoMeasurementChannel
import AxQM.Postulates.API.MeasurementModel

/-!
# AxQM.Postulates.API — the Holevo measurement operation as a dilated channel

The **Stinespring / environment representation** of the Holevo measurement operation `𝓔`
(`holevoMeasurementChannel`, Nielsen & Chuang Exercise 12.2, Eq. (12.8)). The apparatus operation
`𝓔` is given as a Kraus channel `ρ ↦ ∑_y (√E_y ⊗ U_y) ρ (√E_y ⊗ U_y)†` on `Q ⊗ M`
(`M = qudit r` the apparatus register); this file exhibits it in the **dilated form**

  `𝓔(ρ) = Tr_C (U (ρ ⊗ |0⟩⟨0|_C) U†)`

of Nielsen & Chuang §8.2.3: append a fresh pure ancilla `C = qudit r` in the standard state `|0⟩`,
evolve by the joint unitary `U`, then discard `C`. This is precisely the form the χ-monotonicity
Part (2) of the alternate Holevo-bound proof (`State.holevoChi_dilatedChannel_le`) quantifies over —
so this bridge is what lets Part (2) act on the apparatus operation in the final assembly of the
Holevo bound (N&C Problem 12.1(3)).

* `holevoMeasurementChannel_eq_reducedLeft_evolve` — the bridge itself:
  `𝓔(ρ) = (U.evolve (ρ ⊗ |0⟩⟨0|)).reducedLeft`, where `U = measurementModelEvolution` is the
  Stinespring dilation (N&C Exercise 8.9's joint unitary) assembled from the operation elements
  `holevoMeasurementKraus m` — a genuine unitary because they satisfy the completeness relation
  `holevoMeasurementKraus_completeness`. The right-hand side is definitionally `dilatedChannel`, so
  the equation presents `𝓔` in Part (2)'s dilated form.

The proof reuses the operator-sum recovery
`LinearMap.partialTraceRight_conj_tmulRightVec_krausDilation`: the joint unitary intertwines the
standard-ancilla embedding with the Stinespring dilation `V₀ = krausDilation`
(`measurementModelEvolution_op_tmul`, the `hUV` step below), so discarding the environment from the
conjugation of `ρ ⊗ |0⟩⟨0|` returns exactly the operator sum `∑_y (√E_y ⊗ U_y) ρ (√E_y ⊗ U_y)†` —
the `.op` of `𝓔(ρ)` (`holevoMeasurementChannel_op`).

The statement concerns `measurementModelEvolution` (whose argument is an `OrthonormalBasis` of
`(qudit r).space`) and the operation elements `holevoMeasurementKraus`; compare
`holevoMeasurementChannel` and the measurement model it dilates.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {Q : QSystem} {r : ℕ} [NeZero r]

/-- **The Holevo measurement operation `𝓔` in dilated form** (Nielsen & Chuang §8.2.3, the
environment/Stinespring representation of Exercise 12.2's operation). For every state `ρ` on the
system–apparatus composite `Q ⊗ M` (`M = qudit r`),

  `𝓔(ρ) = Tr_C (U (ρ ⊗ |0⟩⟨0|_C) U†) = (U.evolve (ρ ⊗ |0⟩⟨0|)).reducedLeft`,

where `C = qudit r` is a fresh pure environment in the standard state `|0⟩` and
`U = measurementModelEvolution (quditOrthonormalBasis r) _ (holevoMeasurementKraus m) _` is the
joint unitary (N&C Exercise 8.9) built from the operation elements `√E_y ⊗ U_y`, which satisfy the
completeness relation `holevoMeasurementKraus_completeness` and so define a genuine unitary. The
right-hand side is definitionally `State.dilatedChannel ρ U ⟨|0⟩⟩`, so this exhibits `𝓔` in the
form Part (2) `State.holevoChi_dilatedChannel_le` quantifies over.

Proof: on the standard-ancilla slice the joint unitary is the Stinespring dilation,
`U.op ∘ tmulRightVec |0⟩ = krausDilation (quditOrthonormalBasis r) (√E_· ⊗ U_·)` (`hUV`, from
`measurementModelEvolution_op_tmul`); the operator-sum recovery
`LinearMap.partialTraceRight_conj_tmulRightVec_krausDilation` then rewrites the discarded
conjugation `Tr_C (U (ρ ⊗ |0⟩⟨0|) U†)` as `∑_y (√E_y ⊗ U_y) ρ (√E_y ⊗ U_y)†`, which is the `.op` of
`𝓔(ρ)` (`holevoMeasurementChannel_op`, `krausSumₗ`). The partial trace is switched from the standard
basis of the reduced marginal to `quditOrthonormalBasis r` (`partialTraceRight_eq_of_basis`, partial
trace being basis-independent) to match the dilation's basis. -/
theorem holevoMeasurementChannel_eq_reducedLeft_evolve (m : Measurement (Fin r) Q)
    (ρ : State (Q ⊗ qudit r)) :
    holevoMeasurementChannel m ρ
      = ((measurementModelEvolution (quditOrthonormalBasis r)
            (quditBasis (0 : Fin r)).normalized (holevoMeasurementKraus m)
            (holevoMeasurementKraus_completeness m)).evolve
          (ρ.tmul (quditBasis (0 : Fin r)).toState)).reducedLeft := by
  set b := quditOrthonormalBasis r with hb
  set E := holevoMeasurementKraus m with hE_def
  set U := measurementModelEvolution b (quditBasis (0 : Fin r)).normalized E
    (holevoMeasurementKraus_completeness m) with hU_def
  -- Pin one representative `U₀` of the unitary's underlying linear map.
  set U₀ : (Q ⊗ qudit r).space ⊗[ℂ] (qudit r).space →ₗ[ℂ]
      (Q ⊗ qudit r).space ⊗[ℂ] (qudit r).space := U.op.toLinearMap with hU₀
  -- The joint unitary intertwines the standard-ancilla embedding with the Stinespring dilation.
  have hUV : U₀ ∘ₗ LinearMap.tmulRightVec (quditBasis (0 : Fin r)).vec
      = LinearMap.krausDilation b (fun y => (E y).toLinearMap) := by
    rw [hU₀]
    refine LinearMap.ext fun ψ => ?_
    change U.op (ψ ⊗ₜ[ℂ] (quditBasis (0 : Fin r)).vec)
        = LinearMap.krausDilation b (fun y => (E y).toLinearMap) ψ
    rw [hU_def, measurementModelEvolution_op_tmul, LinearMap.krausDilation_apply]
    simp only [ContinuousLinearMap.coe_coe]
    rfl
  -- The basis switch (`stdOrthonormalBasis` → `b`) on `.reducedLeft.op`, done abstractly (before
  -- specializing to the concrete `U.evolve (...)`), so `partialTraceRight_eq_of_basis`'s `rw`
  -- only ever sees the plain generic-tensor argument `ρ'.op.toLinearMap`, never the composite
  -- `U.op ∘SL ⋯ ∘SL adjoint U.op` expression, which crosses the `QSystem.compose` instance diamond.
  have hswitch : ∀ ρ' : State ((Q ⊗ qudit r) ⊗ qudit r),
      ρ'.reducedLeft.op = (LinearMap.partialTraceRight b
        (ρ'.op.toLinearMap : (Q ⊗ qudit r).space ⊗[ℂ] (qudit r).space →ₗ[ℂ]
          (Q ⊗ qudit r).space ⊗[ℂ] (qudit r).space)).toContinuousLinearMap := by
    intro ρ'
    rw [State.reducedLeft_op]
    exact congrArg LinearMap.toContinuousLinearMap
      (LinearMap.partialTraceRight_eq_of_basis (stdOrthonormalBasis ℂ (qudit r).space) b
        ρ'.op.toLinearMap)
  refine State.ext ?_
  rw [holevoMeasurementChannel_op, hswitch, Evolution.evolve_op, State.tmul_op,
    PureState.toState_op]
  refine ContinuousLinearMap.coe_injective ?_
  rw [LinearMap.coe_toContinuousLinearMap]
  have hfork := LinearMap.partialTraceRight_conj_tmulRightVec_krausDilation b
    (fun y => (E y).toLinearMap) U₀ hUV ρ.op.toLinearMap
  -- Rewrite the conjugation of `ρ ⊗ |0⟩⟨0|` into the lemma's shape, apply it, and match the
  -- resulting operator sum with the Kraus sum defining `𝓔`. The final `congr 1` bridges the
  -- `QSystem.compose` instance diamond between the bundled `U.op ∘SL ⋯ ∘SL adjoint U.op` and the
  -- generic `U₀ ∘ₗ TensorProduct.map ⋯ ∘ₗ adjoint U₀` (`rw`'s motive-building can't cross it, but
  -- `congr`'s own defeq check can).
  rw [ContinuousLinearMap.krausSumₗ_apply]
  simp only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_comp,
    ← ContinuousLinearMap.adjoint_toLinearMap]
  rw [← hfork]
  congr 1
  refine LinearMap.ext fun ψ => ?_
  rw [hU₀]
  change U.op (TensorProduct.map ρ.op.toLinearMap
        (((rankOne ℂ) (quditBasis 0).vec) (quditBasis 0).vec).toLinearMap (adjoint U.op ψ))
      = U.op (TensorProduct.mapL ρ.op (((rankOne ℂ) (quditBasis 0).vec) (quditBasis 0).vec)
          (adjoint U.op ψ))
  exact congrArg U.op
    (TensorProduct.mapL_apply ρ.op (((rankOne ℂ) (quditBasis 0).vec) (quditBasis 0).vec)
      (adjoint U.op ψ)).symm

end AxQM
