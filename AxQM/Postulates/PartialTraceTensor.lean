/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.PartialTrace
import AxQM.Postulates.Composite

/-!
# AxQM — reduced states of a product state

The marginals of a product state `ρ ⊗ σ` are its factors: `Tr_B(ρ ⊗ σ) = ρ` and
`Tr_A(ρ ⊗ σ) = σ`. The grounded API bridging `State.tmul` (P6) and the partial-trace
generators, via `partialTrace (A ⊗ B) = (tr A) • B` together with `tr = 1` for states.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **The right marginal of a product state is its right factor**: `Tr_A(ρ ⊗ σ) = σ`. -/
theorem State.reducedRight_tmul (ρ : State S) (σ : State T) :
    (ρ ⊗ σ).reducedRight = σ := by
  ext1
  rw [State.reducedRight_op, State.tmul_op, TensorProduct.toLinearMap_mapL,
    LinearMap.partialTraceLeft_tensorMap, ρ.trace_op_eq_one, one_smul]
  apply ContinuousLinearMap.coe_injective
  rw [LinearMap.coe_toContinuousLinearMap]

/-- **The left marginal of a product state is its left factor**: `Tr_B(ρ ⊗ σ) = ρ`. -/
theorem State.reducedLeft_tmul (ρ : State S) (σ : State T) :
    (ρ ⊗ σ).reducedLeft = ρ := by
  ext1
  rw [State.reducedLeft_op, State.tmul_op, TensorProduct.toLinearMap_mapL,
    LinearMap.partialTraceRight_tensorMap, σ.trace_op_eq_one, one_smul]
  apply ContinuousLinearMap.coe_injective
  rw [LinearMap.coe_toContinuousLinearMap]

end AxQM
