/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.PiTensorState
import AxQM.Postulates.API.PseudoInverse
import ToMathlib.Analysis.InnerProductSpace.PiTensorProduct

/-!
# AxQM.Postulates.API — the `n`-fold tensor-power state `ρ^⊗n` and its spectrum

The **`n`-fold tensor power** of a quantum state `ρ : State S` is the product state
`ρ^⊗n = ρ ⊗ ⋯ ⊗ ρ` (`n` factors) living on the tensor-power system `S ^⊗ₛ n`. Because
`S ^⊗ₛ n` is definitionally the indexed composite `⨂ₛ _ : Fin n, S`
(`QSystem.tensorPow_eq`) and the indexed product state `⨂ₚ i, ρ i` is already available
(`State.piTensor`, `Postulates/PiTensorState.lean`), the tensor power is simply
`State.piTensor` over the *constant* family `fun _ : Fin n ↦ ρ`. It inherits its
density-operator status for free.

This file records its **spectral decomposition**, the key technical input to Nielsen &
Chuang's typical subspace theorem (Theorem 12.5). If `ρ = ∑ₓ λₓ |eₓ⟩⟨eₓ|` is the spectral
decomposition of `ρ` (eigenbasis `e` indexed by `Fin d`, `d = dim S.space`), then `ρ^⊗n` is
diagonal in the **product eigenbasis** `{|e_{κ₁}⟩ ⊗ ⋯ ⊗ |e_{κₙ}⟩ : κ : Fin n → Fin d}`, with
eigenvalue `∏ᵢ λ_{κᵢ}`:

`ρ^⊗n (|e_{κ}⟩) = (∏ᵢ λ_{κᵢ}) |e_{κ}⟩`.

The product eigenbasis is the `n`-ary tensor of `ρ`'s eigenbasis
(`OrthonormalBasis.piTensorProduct`, `ToMathlib/`), and the product eigenvalue drops out of
`PiTensorProduct.mapCLM` acting factor-by-factor (`mapCLM_tprod`) together with the
multilinearity of the elementary tensor (`MultilinearMap.map_smul_univ`). Crucially the product
eigenbasis is indexed by the **length-`n` sequences** `Fin n → Fin d`, which are exactly the
sequences the classical theorem of typical sequences (N&C Theorem 12.2,
`ToMathlib/InformationTheory/TypicalSequence.lean`) is stated over — this is what lets Theorem 12.5
reduce to Theorem 12.2 applied to the eigenvalue distribution `λ`.

## Main definitions and results

* `AxQM.State.tensorPow` (`ρ^⊗n`) — the `n`-fold tensor-power state, on `S ^⊗ₛ n`.
* `AxQM.State.tensorPow_op` — its density operator is the `n`-ary tensor
  `PiTensorProduct.mapCLM (fun _ ↦ ρ.op)`.
* `AxQM.State.tensorPowEigenbasis` — the product eigenbasis
  `⨂ᵢ |e_{κᵢ}⟩` of `ρ^⊗n`, an orthonormal basis of `(S ^⊗ₛ n).space` indexed by
  `Fin n → Fin d`.
* `AxQM.State.tensorPow_op_apply_tensorPowEigenbasis` — the spectral action:
  `ρ^⊗n |e_κ⟩ = (∏ᵢ λ_{κᵢ}) |e_κ⟩`.

The typical subspace theorem itself is `AxQM/NC/Ch12/Theorem12_5.lean`.
-/

open scoped InnerProductSpace TensorProduct BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The **`n`-fold tensor-power state** `ρ^⊗n` of a quantum state `ρ : State S`, living on the
tensor-power system `S ^⊗ₛ n`. It is the indexed product state `⨂ₚ _ : Fin n, ρ`
(`State.piTensor` over the constant family), the `n`-ary analogue of the binary product state
`ρ ⊗ σ` (`State.tmul`); a genuine `State` because the `n`-ary tensor of density operators is a
density operator. -/
def State.tensorPow (ρ : State S) (n : ℕ) : State (S ^⊗ₛ n) := ⨂ₚ _ : Fin n, ρ

/-- The density operator of `ρ^⊗n` is the `n`-ary tensor map `PiTensorProduct.mapCLM` of the
single-copy density operator `ρ.op`. Definitional (unfolds `State.piTensor`). -/
@[simp]
theorem State.tensorPow_op (ρ : State S) (n : ℕ) :
    (ρ.tensorPow n).op = PiTensorProduct.mapCLM (fun _ : Fin n => ρ.op) := rfl

/-- The **product eigenbasis** of `ρ^⊗n`: the `n`-ary tensor `⨂ᵢ |e_{κᵢ}⟩` of `ρ`'s spectral
eigenbasis `e = ρ.isDensity.isSymmetric.eigenvectorBasis` (`OrthonormalBasis.piTensorProduct`),
an orthonormal basis of `(S ^⊗ₛ n).space` indexed by the length-`n` sequences
`κ : Fin n → Fin (dim S.space)`. These sequences are exactly the index type of the classical
`ε`-typical set `Real.typicalSeq`, which is what reduces Nielsen & Chuang's typical subspace
theorem to the classical theorem of typical sequences. -/
def State.tensorPowEigenbasis (ρ : State S) (n : ℕ) :
    OrthonormalBasis (Fin n → Fin (Module.finrank ℂ S.space)) ℂ (S ^⊗ₛ n).space :=
  OrthonormalBasis.piTensorProduct fun _ : Fin n => ρ.isDensity.isSymmetric.eigenvectorBasis rfl

-- Unifying `(S ^⊗ₛ n).space` with `⨂[ℂ] i, S.space` exceeds the default recursion depth.
set_option maxRecDepth 2000 in
/-- The product eigenbasis vector at a sequence `κ` is the elementary tensor
`⨂ᵢ |e_{κᵢ}⟩` of `ρ`'s eigenvectors. -/
theorem State.tensorPowEigenbasis_apply (ρ : State S) (n : ℕ)
    (κ : Fin n → Fin (Module.finrank ℂ S.space)) :
    ρ.tensorPowEigenbasis n κ =
      ⨂ₜ[ℂ] i, ρ.isDensity.isSymmetric.eigenvectorBasis rfl (κ i) :=
  OrthonormalBasis.piTensorProduct_apply
    (fun _ : Fin n => ρ.isDensity.isSymmetric.eigenvectorBasis rfl) κ

/-- **Spectral action of `ρ^⊗n`** (Nielsen & Chuang, the eigenvalues underlying Eq. 12.42/12.46).
The product eigenvector `|e_κ⟩ = ⨂ᵢ |e_{κᵢ}⟩` is an eigenvector of `ρ^⊗n` with eigenvalue the
product `∏ᵢ λ_{κᵢ}` of the corresponding single-copy eigenvalues:

`ρ^⊗n |e_κ⟩ = (∏ᵢ λ_{κᵢ}) |e_κ⟩`.

The operator acts factor-by-factor via `PiTensorProduct.mapCLM_tprod`; each factor `ρ.op |e_{κᵢ}⟩ =
λ_{κᵢ} |e_{κᵢ}⟩` (`State.op_apply_eigenvectorBasis`); and the scalars pull out of the elementary
tensor all at once by multilinearity (`MultilinearMap.map_smul_univ`). -/
theorem State.tensorPow_op_apply_tensorPowEigenbasis (ρ : State S) (n : ℕ)
    (κ : Fin n → Fin (Module.finrank ℂ S.space)) :
    (ρ.tensorPow n).op (ρ.tensorPowEigenbasis n κ) =
      ((∏ i, ρ.isDensity.isSymmetric.eigenvalues rfl (κ i) : ℝ) : ℂ) •
        ρ.tensorPowEigenbasis n κ := by
  rw [State.tensorPowEigenbasis_apply, State.tensorPow_op]
  calc PiTensorProduct.mapCLM (fun _ : Fin n => ρ.op)
        (⨂ₜ[ℂ] i, ρ.isDensity.isSymmetric.eigenvectorBasis rfl (κ i))
      = ⨂ₜ[ℂ] i, ρ.op (ρ.isDensity.isSymmetric.eigenvectorBasis rfl (κ i)) :=
        PiTensorProduct.mapCLM_tprod (fun _ : Fin n => ρ.op) _
    _ = ⨂ₜ[ℂ] i, ((ρ.isDensity.isSymmetric.eigenvalues rfl (κ i) : ℂ) •
          ρ.isDensity.isSymmetric.eigenvectorBasis rfl (κ i)) := by
        simp only [State.op_apply_eigenvectorBasis]
    _ = (∏ i, (ρ.isDensity.isSymmetric.eigenvalues rfl (κ i) : ℂ)) •
          ⨂ₜ[ℂ] i, ρ.isDensity.isSymmetric.eigenvectorBasis rfl (κ i) :=
        (PiTensorProduct.tprod ℂ).map_smul_univ _ _
    _ = ((∏ i, ρ.isDensity.isSymmetric.eigenvalues rfl (κ i) : ℝ) : ℂ) •
          ⨂ₜ[ℂ] i, ρ.isDensity.isSymmetric.eigenvectorBasis rfl (κ i) := by
        rw [Complex.ofReal_prod]

end AxQM
