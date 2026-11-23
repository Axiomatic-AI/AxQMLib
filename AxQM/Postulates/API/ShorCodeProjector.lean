/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorPhaseSyndrome
import ToMathlib.Analysis.InnerProductSpace.RankOneProjector

/-!
# AxQM.Postulates.API — the Shor-code logical codewords and code projector

The **code projector** of the nine-qubit Shor code (Nielsen & Chuang §10.2), the object `P` that
N&C's quantum error-correction conditions (Theorem 10.1) are stated with: `P Eᵢ† Eⱼ P = αᵢⱼ P`. It
is used in the verification of the QEC conditions for the Shor code (Exercise 10.10). Compare the
bit-flip code projector in `AxQM/Postulates/API/BitFlipSyndromeMeasurement.lean`; the conditions
themselves are in `ToMathlib/Analysis/InnerProductSpace/QuantumErrorCorrection.lean`.

The Shor code is a concatenation: the two logical codewords are the equal-sign three-block cat
products (`shorCatProduct`, from `AxQM/Postulates/API/ShorPhaseSyndrome.lean`)

* `|0_L⟩ = shorCodeword 0 = (|000⟩+|111⟩)⊗(|000⟩+|111⟩)⊗(|000⟩+|111⟩) / (2√2)`,
* `|1_L⟩ = shorCodeword 1 = (|000⟩−|111⟩)⊗(|000⟩−|111⟩)⊗(|000⟩−|111⟩) / (2√2)`,

and the code projector `P = |0_L⟩⟨0_L| + |1_L⟩⟨1_L|` is the orthogonal projector onto the
two-dimensional code space `span{|0_L⟩, |1_L⟩}` (`InnerProductSpace.orthonormalProjector`).

## Contents

The block cat states' orthonormality (`catBlockVec_inner`, `catBlockState_inner`) lives beside
their definitions in `AxQM/Postulates/API/ShorCodeBlock.lean`; this file constructs the nine-qubit
codewords and projector from them.

* `shorCodeword` / `shorCodeword_inner` / `shorCodeword_orthonormal` — the two logical codewords and
  their orthonormality (the block orthonormality cubed, via `TensorProduct.inner_tmul`).
* `shorCodeProj` — the code projector `P = |0_L⟩⟨0_L| + |1_L⟩⟨1_L|`, with
  `shorCodeProj_isSelfAdjoint` (`P† = P`), `shorCodeProj_isIdempotentElem` (`P² = P`) — so `P` is a
  genuine orthogonal projector — `shorCodeProj_apply_shorCodeword_zero` (`P|0_L⟩ = |0_L⟩`) and
  `shorCodeProj_ne_zero` (`P ≠ 0`).

-/

open scoped InnerProductSpace TensorProduct
open InnerProductSpace

noncomputable section

namespace AxQM

/-! ### The logical codewords and the code projector -/

/-- **The Shor logical codewords** `|0_L⟩ = shorCodeword 0` and `|1_L⟩ = shorCodeword 1`, the
equal-sign three-block cat products `shorCatProduct s s s`: three copies of the same block sign.
`shorCodeword 0 = |0_L⟩` uses the `+`-sign block `(|000⟩+|111⟩)/√2`, `shorCodeword 1 = |1_L⟩` the
`−`-sign block `(|000⟩−|111⟩)/√2`. -/
def shorCodeword (s : Fin 2) : PureState shorReg := shorCatProduct s s s

/-- **The logical codewords are orthonormal:** `⟪shorCodeword s, shorCodeword s'⟫ = δ_{s,s'}`. Each
codeword factors as `c_s ⊗ c_s ⊗ c_s` over the three cat blocks, so the inner product factors
(`TensorProduct.inner_tmul`) into the cube of the block overlap `⟪c_s, c_{s'}⟫ = δ_{s,s'}`
(`catBlockState_inner`), which is again `δ_{s,s'}`. -/
theorem shorCodeword_inner (s s' : Fin 2) :
    (inner ℂ (shorCodeword s).vec (shorCodeword s').vec : ℂ) = if s = s' then 1 else 0 := by
  rw [shorCodeword, shorCodeword, shorCatProduct, shorCatProduct, PureState.tmul_vec,
    PureState.tmul_vec, PureState.tmul_vec, PureState.tmul_vec]
  change (@inner ℂ (TensorProduct ℂ bitFlipReg.space
      (TensorProduct ℂ bitFlipReg.space bitFlipReg.space)) _
    ((catBlockState s).vec ⊗ₜ[ℂ] ((catBlockState s).vec ⊗ₜ[ℂ] (catBlockState s).vec))
    ((catBlockState s').vec ⊗ₜ[ℂ] ((catBlockState s').vec ⊗ₜ[ℂ] (catBlockState s').vec)) : ℂ) = _
  simp only [TensorProduct.inner_tmul, catBlockState_inner]
  split <;> simp

/-- The logical codewords, as the family `s ↦ |s_L⟩`, form an **orthonormal** family — the input to
the orthogonal projector onto the code space. -/
theorem shorCodeword_orthonormal : Orthonormal ℂ (fun s => (shorCodeword s).vec) :=
  orthonormal_iff_ite.mpr shorCodeword_inner

/-- **The Shor code projector** `P = |0_L⟩⟨0_L| + |1_L⟩⟨1_L|`, the orthogonal projector onto the
two-dimensional code space `span{|0_L⟩, |1_L⟩}`. This is the projector `P` of N&C's quantum
error-correction conditions `P Eᵢ† Eⱼ P = αᵢⱼ P` (Theorem 10.1, Exercise 10.10). -/
def shorCodeProj : shorReg.space →L[ℂ] shorReg.space :=
  orthonormalProjector ℂ (fun s => (shorCodeword s).vec) Finset.univ

/-- **`P` is self-adjoint** (`P† = P`): a projector is Hermitian. -/
theorem shorCodeProj_isSelfAdjoint : IsSelfAdjoint shorCodeProj :=
  isSelfAdjoint_orthonormalProjector _ _

/-- **`P² = P`:** the code projector is idempotent, since the codewords are orthonormal
(`shorCodeword_orthonormal`). Together with self-adjointness this makes `P` a genuine orthogonal
projector. -/
theorem shorCodeProj_isIdempotentElem : IsIdempotentElem shorCodeProj :=
  isIdempotentElem_orthonormalProjector shorCodeword_orthonormal _

/-- **`P |0_L⟩ = |0_L⟩`:** the code projector fixes the logical-zero codeword (it lies in the code
space). The `s = 0` rank-one term contributes `⟪|0_L⟩,|0_L⟩⟫ = 1` and the `s = 1` term
`⟪|1_L⟩,|0_L⟩⟫ = 0` (`shorCodeword_inner`). -/
theorem shorCodeProj_apply_shorCodeword_zero :
    shorCodeProj (shorCodeword 0).vec = (shorCodeword 0).vec := by
  rw [shorCodeProj, orthonormalProjector_apply,
    Finset.sum_eq_single_of_mem (0 : Fin 2) (Finset.mem_univ _)
      (fun s _ hs => by rw [shorCodeword_inner s 0, ite_eq_right hs, zero_smul]),
    shorCodeword_inner 0 0, ite_eq_left rfl, one_smul]

/-- **`P ≠ 0`:** the code projector is nonzero, since it fixes the (nonzero, unit) codeword
`|0_L⟩` (`shorCodeProj_apply_shorCodeword_zero`). -/
theorem shorCodeProj_ne_zero : shorCodeProj ≠ 0 := by
  intro h
  have hz : (shorCodeword 0).vec = 0 := by
    rw [← shorCodeProj_apply_shorCodeword_zero, h, zero_apply]
  simpa [hz] using (PureState.inner_self (shorCodeword 0))

end AxQM
