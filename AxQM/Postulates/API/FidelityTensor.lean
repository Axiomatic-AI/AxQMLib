/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Fidelity
import AxQM.Postulates.Composite
import ToMathlib.Analysis.InnerProductSpace.TraceNormTensor

/-!
# AxQM — the fidelity is multiplicative under tensor products

Nielsen & Chuang record (§9.2.2, and used throughout Chapters 9 & 12) that the fidelity is
**multiplicative under tensor products**: for states `ρ, ρ'` of a system `S` and `σ, σ'` of a
system `T`,
```
F(ρ ⊗ σ, ρ' ⊗ σ') = F(ρ, ρ') · F(σ, σ').
```
This is the mixed-state companion of `PureState.fidelity_piTensor` (which factorises the fidelity of
*pure* product states through inner products); it holds for arbitrary density operators.

The proof goes through the trace-norm form `State.fidelity_eq_traceNorm`
(`F(ρ, σ) = ‖√ρ √σ‖₁`): the CFC square root distributes over the tensor product on the
(nonnegative) density operators (`ContinuousLinearMap.cfc_real_sqrt_mapL`), the product of tensor
maps is the tensor map of the products (`TensorProduct.mapL_mul`), and the trace norm is
multiplicative under tensor products (`ContinuousLinearMap.traceNorm_mapL`, in `ToMathlib`).

## Main statements

* `State.fidelity_tmul` — `F(ρ ⊗ σ, ρ' ⊗ σ') = F(ρ, ρ') · F(σ, σ')`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **The fidelity is multiplicative under the tensor product of states**
(Nielsen & Chuang §9.2.2): `F(ρ ⊗ σ, ρ' ⊗ σ') = F(ρ, ρ') · F(σ, σ')`.

Through the trace-norm bridge `F(ρ, σ) = ‖√ρ √σ‖₁` (`State.fidelity_eq_traceNorm`), the operator
`√(ρ ⊗ σ) √(ρ' ⊗ σ')` factorises: `√(ρ ⊗ σ) = √ρ ⊗ √σ` (the density operators are nonnegative, so
`ContinuousLinearMap.cfc_real_sqrt_mapL` applies), the product of tensor maps is the tensor map of
the products (`TensorProduct.mapL_mul`), and the trace norm is multiplicative under the tensor
product (`ContinuousLinearMap.traceNorm_mapL`). -/
theorem State.fidelity_tmul (ρ ρ' : State S) (σ σ' : State T) :
    (ρ.tmul σ).fidelity (ρ'.tmul σ') = ρ.fidelity ρ' * σ.fidelity σ' := by
  rw [State.fidelity_eq_traceNorm, State.fidelity_eq_traceNorm, State.fidelity_eq_traceNorm]
  -- `(ρ ⊗ σ).op` is `mapL ρ.op σ.op` definitionally; `change` re-types it as an operator on the
  -- underlying space `S.space ⊗ T.space` (not `(S ⊗ T).space`) so the tensor lemmas below fire.
  change (cfc Real.sqrt (TensorProduct.mapL ρ.op σ.op)
        * cfc Real.sqrt (TensorProduct.mapL ρ'.op σ'.op)).traceNorm = _
  rw [cfc_real_sqrt_mapL ρ.isDensity.nonneg σ.isDensity.nonneg,
    cfc_real_sqrt_mapL ρ'.isDensity.nonneg σ'.isDensity.nonneg,
    ← TensorProduct.mapL_mul, ContinuousLinearMap.traceNorm_mapL]

end AxQM
