/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorPauliError

/-!
# AxQM.Postulates.API — the Shor-code error family and off-diagonal error-vector overlaps

Nielsen & Chuang's **Exercise 10.10**: the verification of the
quantum error-correction conditions (Theorem 10.1) for the nine-qubit Shor code against the error
set `{I} ∪ {X_j, Y_j, Z_j : j = 1..9}` (the identity and every single-qubit Pauli). This file
collects the **error family** and one of the two matrix-element facts the verification rests on.

By the codeword-basis route (`ContinuousLinearMap.satisfiesKLConditions_of_inner_error_images`, the
shared engine of N&C Exercises 10.7–10.10), the conditions `P Eᵢ† Eⱼ P = αᵢⱼ P` reduce to the
overlaps of the **error vectors** `v_{i,s} = Eᵢ |s_L⟩` (`i` an error, `s ∈ Fin 2` a logical
codeword):

  `⟪v_{i,a}, v_{j,b}⟫ = αᵢⱼ · δ_{a,b}`.

The coefficient matrix `α` is the Gram matrix `αᵢⱼ = ⟪v_{i,0}, v_{j,0}⟫` (Hermitian automatically),
and the reduction needs exactly two facts: **(A)** diagonal-equality `⟪v_{i,1}, v_{j,1}⟫ =
⟪v_{i,0}, v_{j,0}⟫`, and **(B)** off-diagonal-vanishing `⟪v_{i,0}, v_{j,1}⟫ = 0`. This file proves
**(B)**; the diagonal-equality **(A)** is proved in
`AxQM/Postulates/API/ShorErrorInnerProductDiag.lean` and the assembly into
`SatisfiesQECConditions` is in `AxQM/Postulates/API/ShorCodeQEC.lean`. It builds on the Shor code
projector (`AxQM/Postulates/API/ShorCodeProjector.lean`), the Pauli errors
(`AxQM/Postulates/API/ShorPauliError.lean`) and the error-correction conditions
(`AxQM/Postulates/API/QuantumErrorCorrection.lean`).

The whole computation runs on the **block factorisation** `shorReg = bitFlipReg ⊗ (bitFlipReg ⊗
bitFlipReg)`: a codeword is the equal-sign three-block cat product `|s_L⟩ = c_s ⊗ (c_s ⊗ c_s)`
(`shorCodeword`), and a single-qubit Pauli error touches **exactly one** of the three cat blocks
(the identity error touches none). So two errors together touch **at most two** of the three blocks,
leaving at least one block untouched by both; on that block the overlap factor is `⟪c_0, c_1⟫ = 0`
(`catBlockState_inner`), and the whole tensor overlap vanishes. This is why off-diagonal overlaps —
between the images of the two *distinct* codewords — are zero: the code stays distinguishable under
any pair of single-qubit Pauli errors.

## Contents

* `ShorErrorIndex` — the index set `Option (Fin 3 × Fin 3 × Fin 3)` of the 28 errors: `none = I`,
  `some (t, block, pos)` the Pauli of type `t` (`0 = X`, `1 = Y`, `2 = Z`) on qubit `(block, pos)`.
* `shorErrorFamily` / `shorErrorVec` — the error operators `Eᵢ` (`none ↦ 1`,
  `some ↦ shorPauliError`) and the error vectors `v_{i,s} = Eᵢ |s_L⟩`.
* `shorReg_inner_tmul` — the block-factorisation of the register inner product: an inner product of
  two three-block tensors is the product of the three per-block inner products
  (`TensorProduct.inner_tmul`, twice).
* `shorErrorVec_inner_offdiag_eq_zero` — **fact (B)**: `⟪v_{i,0}, v_{j,1}⟫ = 0` for every pair of
  errors, and `shorErrorVec_inner_offdiag` its `a ≠ b` form.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-! ### The error family `{I, X_j, Y_j, Z_j : j = 1..9}` -/

/-- **The index set of the 28 Shor-code errors** of Exercise 10.10: `none` is the identity `I`, and
`some (t, block, pos)` is the single-qubit Pauli of type `t` (`0 = X`, `1 = Y`, `2 = Z`) placed at
qubit `(block, pos) ∈ Fin 3 × Fin 3`, i.e. `X_j, Y_j, Z_j` with `j = 3·block + pos + 1`. The 27
Pauli errors plus the single identity make up the error set `{I} ∪ {X_j, Y_j, Z_j : j = 1..9}`. -/
abbrev ShorErrorIndex : Type := Option (Fin 3 × Fin 3 × Fin 3)

/-- **The Shor-code error operators** `Eᵢ` indexed by `ShorErrorIndex`: the identity `I = 1` for
`none`, and the single-qubit Pauli error `shorPauliError t block pos` for `some (t, block, pos)`.
These are the operation elements the quantum error-correction conditions (Theorem 10.1,
Exercise 10.10) are checked against. -/
def shorErrorFamily : ShorErrorIndex → shorReg.space →L[ℂ] shorReg.space
  | none => 1
  | some (t, block, pos) => shorPauliError t block pos

/-- **The error vectors** `v_{i,s} = Eᵢ |s_L⟩`: the image of the logical codeword `shorCodeword s`
under the error operator `shorErrorFamily i`. The quantum error-correction conditions reduce, via
`satisfiesKLConditions_of_inner_error_images`, to the overlaps `⟪v_{i,a}, v_{j,b}⟫` of these
vectors. -/
def shorErrorVec (i : ShorErrorIndex) (s : Fin 2) : shorReg.space :=
  shorErrorFamily i (shorCodeword s).vec

/-! ### Block factorisation of the register inner product -/

/-- **The register inner product factors over the three cat blocks:** for three-block tensors
`x₀ ⊗ (x₁ ⊗ x₂)` and `y₀ ⊗ (y₁ ⊗ y₂)` on `shorReg = bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)`,
`⟪x₀ ⊗ (x₁ ⊗ x₂), y₀ ⊗ (y₁ ⊗ y₂)⟫ = ⟪x₀, y₀⟫ · ⟪x₁, y₁⟫ · ⟪x₂, y₂⟫`, by the multiplicativity of the
tensor inner product (`TensorProduct.inner_tmul`, applied to the outer and then the inner tensor).
This is the workhorse that turns every register overlap into per-block cat-state overlaps. -/
theorem shorReg_inner_tmul (x₀ x₁ x₂ y₀ y₁ y₂ : bitFlipReg.space) :
    (inner ℂ (x₀ ⊗ₜ[ℂ] (x₁ ⊗ₜ[ℂ] x₂) : shorReg.space) (y₀ ⊗ₜ[ℂ] (y₁ ⊗ₜ[ℂ] y₂)) : ℂ)
      = inner ℂ x₀ y₀ * (inner ℂ x₁ y₁ * inner ℂ x₂ y₂) := by
  change (@inner ℂ (TensorProduct ℂ bitFlipReg.space
      (TensorProduct ℂ bitFlipReg.space bitFlipReg.space)) _
    (x₀ ⊗ₜ[ℂ] (x₁ ⊗ₜ[ℂ] x₂)) (y₀ ⊗ₜ[ℂ] (y₁ ⊗ₜ[ℂ] y₂)) : ℂ) = _
  rw [TensorProduct.inner_tmul, TensorProduct.inner_tmul]

/-! ### Off-diagonal error-vector overlaps vanish -/

/-- **Off-diagonal error-vector overlaps vanish** (fact (B) of Exercise 10.10):
`⟪v_{i,0}, v_{j,1}⟫ = ⟪Eᵢ |0_L⟩, Eⱼ |1_L⟩⟫ = 0` for **every** pair of errors `i, j`.

Each single-qubit Pauli error touches exactly one of the three cat blocks (the identity touches
none), so two errors touch at most two blocks and at least one block is untouched by both. On the
block factorisation `shorReg = bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)` (`shorReg_inner_tmul`) that
untouched block contributes the factor `⟪c_0, c_1⟫ = 0` (`catBlockState_inner`), so the whole
overlap vanishes: the images of the two distinct logical codewords stay orthogonal under any pair of
single-qubit Pauli errors. -/
theorem shorErrorVec_inner_offdiag_eq_zero (i j : ShorErrorIndex) :
    (inner ℂ (shorErrorVec i 0) (shorErrorVec j 1) : ℂ) = 0 := by
  rcases i with _ | ⟨ti, bi, pi⟩ <;> rcases j with _ | ⟨tj, bj, pj⟩ <;>
    simp only [shorErrorVec, shorErrorFamily]
  · -- I, I : the two codewords are orthogonal
    rw [one_apply_eq_self, one_apply_eq_self, shorCodeword_inner]
    simp
  · -- I, Pauli : the error touches one block, two blocks are untouched
    fin_cases bj <;>
      (simp only [shorPauliError, shorSinglePauli, shorCodeword,
        shorCatProduct, PureState.tmul_vec,
        ]
       erw [shorReg_inner_tmul]
       simp [catBlockState_inner])
  · -- Pauli, I : symmetric
    fin_cases bi <;>
      (simp only [shorPauliError, shorSinglePauli, shorCodeword,
        shorCatProduct, PureState.tmul_vec,
        ]
       erw [shorReg_inner_tmul]
       simp [catBlockState_inner])
  · -- Pauli, Pauli : at least one block untouched by both
    fin_cases bi <;> fin_cases bj <;>
      (simp only [shorPauliError, shorSinglePauli, shorCodeword, shorCatProduct, PureState.tmul_vec,
        ]
       erw [shorReg_inner_tmul]
       simp [catBlockState_inner])

/-- **Off-diagonal error-vector overlaps vanish, in the `a ≠ b` form:** `⟪v_{i,a}, v_{j,b}⟫ = 0`
whenever `a ≠ b`. On `Fin 2` this is the pair `(a, b) ∈ {(0,1), (1,0)}`; the `(0,1)` case is
`shorErrorVec_inner_offdiag_eq_zero` and the `(1,0)` case is its conjugate
(`⟪v_{i,1}, v_{j,0}⟫ = conj ⟪v_{j,0}, v_{i,1}⟫ = 0`). This is the shape consumed by the
Knill–Laflamme reduction `satisfiesKLConditions_of_inner_error_images`. -/
theorem shorErrorVec_inner_offdiag (i j : ShorErrorIndex) {a b : Fin 2} (hab : a ≠ b) :
    (inner ℂ (shorErrorVec i a) (shorErrorVec j b) : ℂ) = 0 := by
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · exact shorErrorVec_inner_offdiag_eq_zero i j
  · change (inner ℂ (shorErrorVec i 1) (shorErrorVec j 0) : ℂ) = 0
    rw [← inner_conj_symm, shorErrorVec_inner_offdiag_eq_zero j i, map_zero]
  · exact absurd rfl hab

end AxQM
