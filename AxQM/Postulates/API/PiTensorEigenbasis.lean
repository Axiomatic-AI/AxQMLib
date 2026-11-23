/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TypicalSubspace
import ToMathlib.Analysis.InnerProductSpace.PiTensorProduct
import ToMathlib.Analysis.InnerProductSpace.PiTensorProductMap

/-!
# AxQM.Postulates.API — the product eigenbasis of a family of states `⨂ᵢ ρᵢ`

For a finite family of quantum states `ρ : (i : ι) → State (S i)`, the indexed product state
`⨂ₚ i, ρ i` (`State.piTensor`, `AxQM/Postulates/PiTensorState.lean`) is diagonal in the **product
eigenbasis** built from the individual spectral eigenbases: if each `ρ i = ∑ₖ λᵢₖ |eᵢₖ⟩⟨eᵢₖ|`,
then the elementary tensors `|e_κ⟩ = ⨂ᵢ |e_{i,κᵢ}⟩` (indexed by a choice `κ : (i : ι) → Fin dᵢ`
of an eigenvector in each factor) are eigenvectors of `⨂ₚ i, ρ i` with eigenvalue the product
`∏ᵢ λ_{i,κᵢ}`:

`(⨂ₚ i, ρ i) |e_κ⟩ = (∏ᵢ λ_{i,κᵢ}) |e_κ⟩`.

This is the **distinct-factor generalisation** of the tensor-power spectral decomposition
`State.tensorPowEigenbasis` / `State.tensorPow_op_apply_tensorPowEigenbasis`
(`AxQM/Postulates/API/TensorPowState.lean`), which handles only the constant family `ρ^⊗n`
(all factors equal). It is the eigenstructure Nielsen & Chuang's HSW achievability argument
(Theorem 12.8, Eqs. 12.74–12.75) needs for the **conditional typical subspace** of a product
codeword `σ_M = σ_{M₁} ⊗ ⋯ ⊗ σ_{Mₙ}`, whose factors `σ_{Mᵢ} = E(ρ_{Mᵢ})` are in general
*different* output states drawn from the input ensemble — so its typical subspace cannot be read
off `tensorPowEigenbasis` (which needs one repeated state).

## Main definitions and results

* `AxQM.State.piTensorEigenbasis` — the product eigenbasis `⨂ᵢ |e_{i,κᵢ}⟩` of
  `⨂ₚ i, ρ i`, an orthonormal basis of `(QSystem.piTensor S).space` indexed by the dependent
  sequences `κ : (i : ι) → Fin (dim (S i).space)`.
* `AxQM.State.piTensorEigenbasis_apply` — its value: the elementary tensor of the
  per-factor eigenvectors.
* `AxQM.State.piTensor_op_apply_piTensorEigenbasis` — the spectral action
  `(⨂ₚ i, ρ i) |e_κ⟩ = (∏ᵢ λ_{i,κᵢ}) |e_κ⟩`, with `λ_{i,·} = (ρ i).eigenvalueDist`.
-/

open scoped InnerProductSpace TensorProduct BigOperators

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → QSystem}

/-- The **product eigenbasis** of the indexed product state `⨂ₚ i, ρ i`: the elementary tensor
`⨂ᵢ |e_{i,κᵢ}⟩` of each factor's canonical spectral eigenbasis `(ρ i).eigenbasis`
(`OrthonormalBasis.piTensorProduct`), an orthonormal basis of `(QSystem.piTensor S).space` indexed
by the dependent sequences `κ : (i : ι) → Fin (dim (S i).space)`.  The distinct-factor
generalisation of `State.tensorPowEigenbasis` (which is this basis for the constant family
`fun _ ↦ ρ`). -/
def State.piTensorEigenbasis (ρ : (i : ι) → State (S i)) :
    OrthonormalBasis ((i : ι) → Fin (Module.finrank ℂ (S i).space)) ℂ
      (QSystem.piTensor S).space :=
  OrthonormalBasis.piTensorProduct fun i => (ρ i).eigenbasis

/-- The product eigenbasis vector at a dependent sequence `κ` is the elementary tensor
`⨂ᵢ |e_{i,κᵢ}⟩` of the per-factor eigenvectors. -/
theorem State.piTensorEigenbasis_apply (ρ : (i : ι) → State (S i))
    (κ : (i : ι) → Fin (Module.finrank ℂ (S i).space)) :
    State.piTensorEigenbasis ρ κ = ⨂ₜ[ℂ] i, (ρ i).eigenbasis (κ i) :=
  OrthonormalBasis.piTensorProduct_apply (fun i => (ρ i).eigenbasis) κ

/-- **Spectral action of `⨂ₚ i, ρ i`** (Nielsen & Chuang, the eigenvalues underlying the HSW
conditional typical subspace, Eqs. 12.74–12.75).  The product eigenvector
`|e_κ⟩ = ⨂ᵢ |e_{i,κᵢ}⟩` is an eigenvector of the indexed product state with eigenvalue the product
`∏ᵢ λ_{i,κᵢ}` of the corresponding per-factor eigenvalues:

`(⨂ₚ i, ρ i) |e_κ⟩ = (∏ᵢ λ_{i,κᵢ}) |e_κ⟩`,   `λ_{i,·} = (ρ i).eigenvalueDist`.

The operator acts factor-by-factor via `PiTensorProduct.mapCLM_tprod` (`State.piTensor_op` unfolds
`⨂ₚ i, ρ i` to `PiTensorProduct.mapCLM (fun i ↦ (ρ i).op)`); each factor
`(ρ i).op |e_{i,κᵢ}⟩ = λ_{i,κᵢ} |e_{i,κᵢ}⟩` (`State.op_apply_eigenbasis`); and the scalars pull out
of the elementary tensor all at once by multilinearity (`MultilinearMap.map_smul_univ`).  The
distinct-factor generalisation of `State.tensorPow_op_apply_tensorPowEigenbasis`. -/
theorem State.piTensor_op_apply_piTensorEigenbasis (ρ : (i : ι) → State (S i))
    (κ : (i : ι) → Fin (Module.finrank ℂ (S i).space)) :
    (State.piTensor ρ).op (State.piTensorEigenbasis ρ κ) =
      ((∏ i, (ρ i).eigenvalueDist (κ i) : ℝ) : ℂ) • State.piTensorEigenbasis ρ κ := by
  rw [State.piTensorEigenbasis_apply, State.piTensor_op]
  calc (PiTensorProduct.mapCLM fun i => (ρ i).op) (⨂ₜ[ℂ] i, (ρ i).eigenbasis (κ i))
      = ⨂ₜ[ℂ] i, (ρ i).op ((ρ i).eigenbasis (κ i)) :=
        PiTensorProduct.mapCLM_tprod (fun i => (ρ i).op) _
    _ = ⨂ₜ[ℂ] i, (((ρ i).eigenvalueDist (κ i) : ℂ) • (ρ i).eigenbasis (κ i)) := by
        simp only [State.op_apply_eigenbasis, State.eigenvalueDist]
    _ = (∏ i, ((ρ i).eigenvalueDist (κ i) : ℂ)) • ⨂ₜ[ℂ] i, (ρ i).eigenbasis (κ i) :=
        (PiTensorProduct.tprod ℂ).map_smul_univ _ _
    _ = ((∏ i, (ρ i).eigenvalueDist (κ i) : ℝ) : ℂ) • ⨂ₜ[ℂ] i, (ρ i).eigenbasis (κ i) := by
        rw [Complex.ofReal_prod]

end AxQM
