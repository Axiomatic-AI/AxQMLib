/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorErrorInnerProduct

/-!
# AxQM.Postulates.API — the diagonal error-vector overlaps of the Shor code

Nielsen & Chuang's **Exercise 10.10**, the verification of the
quantum error-correction conditions (Theorem 10.1) for the nine-qubit Shor code against the error
set `{I} ∪ {X_j, Y_j, Z_j : j = 1..9}`. This file proves **fact (A)**, the *diagonal-equality* of
the error-vector overlaps, the companion of the off-diagonal-vanishing **fact (B)** in
`AxQM/Postulates/API/ShorErrorInnerProduct.lean`:

  `⟪v_{i,1}, v_{j,1}⟫ = ⟪v_{i,0}, v_{j,0}⟫`  for every pair of errors `i, j`

(`v_{i,s} = Eᵢ |s_L⟩` the error vectors, `shorErrorVec`). Together (A) and (B) give the Gram-matrix
form `⟪v_{i,a}, v_{j,b}⟫ = αᵢⱼ · δ_{a,b}` that the Knill–Laflamme reduction
`ContinuousLinearMap.satisfiesKLConditions_of_inner_error_images` consumes.

## The argument

The overlap `⟪v_{i,s}, v_{j,s}⟫` factors over the three cat blocks
`shorReg = bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)` (`shorReg_inner_tmul`), because a codeword is the
equal-sign three-block product `|s_L⟩ = c_s ⊗ (c_s ⊗ c_s)` and each single-qubit Pauli error touches
exactly one block. So the register overlap is a product of per-block factors, and it suffices that
**each per-block factor is independent of the sign `s`**. A block is touched by at most one of
`i, j` except when both errors sit in the *same* block, so the per-block factors fall into three
shapes:

* **untouched** (both errors elsewhere): `⟪c_s, c_s⟫ = 1` (`catBlockState_inner`) — constant;
* **one Pauli** `P` (touched by exactly one error): `⟪P c_s, c_s⟫ = 0` and `⟪c_s, P c_s⟫ = 0`
  (`blockSinglePauli_pauliErrorObs_catBlockState_inner_self_eq_zero` and its adjoint) — a `Z` sends
  `c_s` to the *other* cat state, an `X`/`Y` sends it out of the cat span, so the overlap with `c_s`
  vanishes for every `s`;
* **two Paulis `P, P'` on the same block**: the only case requiring real work
  (`blockSinglePauli_pauliErrorObs_catBlockState_inner_diag_eq`). Writing
  `c_s = |000⟩ + (−1)^s |111⟩` and expanding, the two cross terms carry a single `(−1)^s`, while the
  diagonal terms carry `(−1)^{2s} = 1`; the cross terms vanish because a single-qubit Pauli maps
  `|000⟩` (weight `≤ 1`) and `|111⟩` (weight `≥ 2`) to *orthogonal* kets
  (`shorBlockPauli_e000_inner_e111`), so only the
  `s`-independent diagonal terms survive (`catBlockState_bilin_diag_eq`).

## Contents

* `catBlockVec_bilin_diag_collapse` / `catBlockState_bilin_diag_eq` — the sign-collapse core: for
  block operators `L, L'` whose images of `|000⟩` and `|111⟩` are cross-orthogonal,
  `⟪L c_s, L' c_s⟫` is independent of `s`.
* `shorBlockPauli_e000_inner_e111` and the four `qubitThreeBasis_*_inner_*` weight facts — a
  single-qubit Pauli sends `|000⟩` and `|111⟩` to orthogonal kets (weight `≤ 1` vs `≥ 2`).
* `blockSinglePauli_pauliErrorObs_catBlockState_inner_self_eq_zero` (and its `..._diag_eq` two-Pauli
  companion) — the per-block factor lemmas.
* `shorErrorVec_inner_diag_eq` — **fact (A)**: `⟪v_{i,1}, v_{j,1}⟫ = ⟪v_{i,0}, v_{j,0}⟫`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-! ### Orthogonality of the extreme kets `|000⟩`, `|111⟩` under a single-qubit Pauli

A single-qubit Pauli maps `|000⟩` (Hamming weight `0`) to a weight-`≤ 1` ket and `|111⟩` (weight
`3`) to a weight-`≥ 2` ket, so the two images are orthogonal. The four facts below record the four
ket shapes that occur, via orthonormality of the computational basis
(`qubitThreeBasis_orthonormal`). -/

/-- `⟪|000⟩, |111⟩⟫ = 0`: the all-zeros and all-ones kets are orthogonal
(`qubitThreeBasis_inner_eq_zero_of_ne`). -/
theorem qubitThreeBasis_zero_inner_one :
    (inner ℂ (qubitThreeBasis (0, 0, 0)).vec (qubitThreeBasis (1, 1, 1)).vec : ℂ) = 0 :=
  qubitThreeBasis_inner_eq_zero_of_ne (by decide)

/-- `⟪X/Y|000⟩, |111⟩⟫ = 0`: a bit-flipped `|000⟩` (weight `1`) is orthogonal to `|111⟩` (weight
`3`), for every flip position. -/
theorem qubitThreeBasis_flipZero_inner_one (pa : Fin 3) :
    (inner ℂ (qubitThreeBasis (qubitThreeFlip pa (0, 0, 0))).vec
      (qubitThreeBasis (1, 1, 1)).vec : ℂ) = 0 :=
  qubitThreeBasis_inner_eq_zero_of_ne (by fin_cases pa <;> decide)

/-- `⟪|000⟩, X/Y|111⟩⟫ = 0`: `|000⟩` (weight `0`) is orthogonal to a bit-flipped `|111⟩` (weight
`2`), for every flip position. -/
theorem qubitThreeBasis_zero_inner_flipOne (pb : Fin 3) :
    (inner ℂ (qubitThreeBasis (0, 0, 0)).vec
      (qubitThreeBasis (qubitThreeFlip pb (1, 1, 1))).vec : ℂ) = 0 :=
  qubitThreeBasis_inner_eq_zero_of_ne (by fin_cases pb <;> decide)

/-- `⟪X/Y|000⟩, X/Y|111⟩⟫ = 0`: a bit-flipped `|000⟩` (weight `1`) is orthogonal to a bit-flipped
`|111⟩` (weight `2`), for every pair of flip positions. -/
theorem qubitThreeBasis_flipZero_inner_flipOne (pa pb : Fin 3) :
    (inner ℂ (qubitThreeBasis (qubitThreeFlip pa (0, 0, 0))).vec
      (qubitThreeBasis (qubitThreeFlip pb (1, 1, 1))).vec : ℂ) = 0 :=
  qubitThreeBasis_inner_eq_zero_of_ne (by fin_cases pa <;> fin_cases pb <;> decide)

/-- **A single-qubit Pauli sends `|000⟩` and `|111⟩` to orthogonal kets:**
`⟪Pₐ|000⟩, P_b|111⟩⟫ = 0` for any two single-qubit Paulis `Pₐ = pauliErrorObs ta` (at `pa`),
`P_b = pauliErrorObs tb` (at `pb`). Each Pauli maps `|000⟩` to a phase times a weight-`≤ 1` ket and
`|111⟩` to a phase times a weight-`≥ 2` ket, and weight-`≤ 1` and weight-`≥ 2` kets are orthogonal
(`qubitThreeBasis_*_inner_*`). This is the cross-vanishing that makes the same-block two-Pauli
diagonal factor `s`-independent. -/
theorem shorBlockPauli_e000_inner_e111 (ta pa tb pb : Fin 3) :
    (inner ℂ ((blockSinglePauli (pauliErrorObs ta) pa).op (qubitThreeBasis (0, 0, 0)).vec)
      ((blockSinglePauli (pauliErrorObs tb) pb).op (qubitThreeBasis (1, 1, 1)).vec) : ℂ) = 0 := by
  fin_cases ta <;> fin_cases tb <;>
    simp [pauliErrorObs, blockSinglePauliX_op_qubitThreeBasis,
      blockSinglePauliY_op_qubitThreeBasis, blockSinglePauliZ_op_qubitThreeBasis,
      inner_smul_left, inner_smul_right, qubitThreeBasis_zero_inner_one,
      qubitThreeBasis_flipZero_inner_one, qubitThreeBasis_zero_inner_flipOne,
      qubitThreeBasis_flipZero_inner_flipOne]

/-! ### The sign-collapse core -/

/-- **Sign-collapse on the unnormalised cat vector.** For block operators `L, L'` whose images of
`|000⟩` and `|111⟩` are cross-orthogonal (`⟪L|000⟩, L'|111⟩⟫ = 0 = ⟪L|111⟩, L'|000⟩⟫`), the bilinear
form `⟪L c_s, L' c_s⟫` on the cat vector `c_s = |000⟩ + (−1)^s|111⟩` is independent of the sign `s`.
Expanding by linearity, the two cross terms carry a lone `(−1)^s` and are killed by the hypotheses;
the two diagonal terms carry `conj((−1)^s)·(−1)^s = 1`, leaving the `s`-free sum
`⟪L|000⟩, L'|000⟩⟫ + ⟪L|111⟩, L'|111⟩⟫`. -/
theorem catBlockVec_bilin_diag_collapse (L L' : bitFlipReg.space →L[ℂ] bitFlipReg.space) (s : Fin 2)
    (h1 : (inner ℂ (L (qubitThreeBasis (0, 0, 0)).vec)
      (L' (qubitThreeBasis (1, 1, 1)).vec) : ℂ) = 0)
    (h2 : (inner ℂ (L (qubitThreeBasis (1, 1, 1)).vec)
      (L' (qubitThreeBasis (0, 0, 0)).vec) : ℂ) = 0) :
    (inner ℂ (L (catBlockVec s)) (L' (catBlockVec s)) : ℂ)
      = (inner ℂ (L (catBlockVec 0)) (L' (catBlockVec 0)) : ℂ) := by
  simp only [catBlockVec, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, h1, h2, mul_zero, add_zero, zero_add]
  fin_cases s <;> simp

/-- **Sign-collapse on the normalised cat state.** The normalised versions inherit the sign-collapse
of `catBlockVec_bilin_diag_collapse` because the two cat states share the same normalisation
constant `√2` (`catBlockVec_norm`), independent of `s`: `⟪L c_s, L' c_s⟫ = ⟪L c_0, L' c_0⟫` on
`catBlockState`. -/
theorem catBlockState_bilin_diag_eq (L L' : bitFlipReg.space →L[ℂ] bitFlipReg.space) (s : Fin 2)
    (h1 : (inner ℂ (L (qubitThreeBasis (0, 0, 0)).vec)
      (L' (qubitThreeBasis (1, 1, 1)).vec) : ℂ) = 0)
    (h2 : (inner ℂ (L (qubitThreeBasis (1, 1, 1)).vec)
      (L' (qubitThreeBasis (0, 0, 0)).vec) : ℂ) = 0) :
    (inner ℂ (L (catBlockState s).vec) (L' (catBlockState s).vec) : ℂ)
      = (inner ℂ (L (catBlockState 0).vec) (L' (catBlockState 0).vec) : ℂ) := by
  simp only [catBlockState, PureState.normalize_vec, catBlockVec_norm, map_smul, inner_smul_left,
    inner_smul_right]
  rw [catBlockVec_bilin_diag_collapse L L' s h1 h2]

/-! ### The per-block factors -/

/-- **A single Pauli, one side of the overlap, kills the block factor:** `⟪c_s, P c_s⟫ = 0` for a
single-qubit Pauli `P = pauliErrorObs t` at position `p`. A `Z` sends `c_s` to the other cat state
`c_{s+1} ⊥ c_s`; an `X` or `Y` sends it out of the cat span. So a block touched by exactly one of
the two errors contributes an overlap of `0`, independently of `s`. -/
theorem catBlockState_inner_blockSinglePauli_self_eq_zero (t p : Fin 3) (s : Fin 2) :
    (inner ℂ (catBlockState s).vec
      ((blockSinglePauli (pauliErrorObs t) p).op (catBlockState s).vec) : ℂ) = 0 := by
  fin_cases t <;>
    simp [pauliErrorObs, blockSinglePauliZ_op_catBlockState, catBlockState_inner,
      catBlockState_inner_blockSinglePauliX, catBlockState_inner_blockSinglePauliY]

/-- **A single Pauli, the other side, also kills the block factor:** `⟪P c_s, c_s⟫ = 0`, the adjoint
form of `catBlockState_inner_blockSinglePauli_self_eq_zero` (`⟪P c_s, c_s⟫ = conj ⟪c_s, P c_s⟫`). -/
theorem blockSinglePauli_catBlockState_inner_self_eq_zero (t p : Fin 3) (s : Fin 2) :
    (inner ℂ ((blockSinglePauli (pauliErrorObs t) p).op (catBlockState s).vec)
      (catBlockState s).vec : ℂ) = 0 := by
  rw [← inner_conj_symm, catBlockState_inner_blockSinglePauli_self_eq_zero, map_zero]

/-- **The same-block two-Pauli factor is `s`-independent:**
`⟪Pₐ c_1, P_b c_1⟫ = ⟪Pₐ c_0, P_b c_0⟫` for two single-qubit Paulis `Pₐ = pauliErrorObs ta` (at
`pa`), `P_b = pauliErrorObs tb` (at `pb`) placed in the *same* cat block. This is the only per-block
factor needing the sign-collapse (`catBlockState_bilin_diag_eq`); its cross-vanishing hypotheses are
`shorBlockPauli_e000_inner_e111` (and its conjugate). -/
theorem blockSinglePauli_pauliErrorObs_catBlockState_inner_diag_eq
    (ta pa tb pb : Fin 3) (s : Fin 2) :
    (inner ℂ ((blockSinglePauli (pauliErrorObs ta) pa).op (catBlockState s).vec)
      ((blockSinglePauli (pauliErrorObs tb) pb).op (catBlockState s).vec) : ℂ)
    = (inner ℂ ((blockSinglePauli (pauliErrorObs ta) pa).op (catBlockState 0).vec)
      ((blockSinglePauli (pauliErrorObs tb) pb).op (catBlockState 0).vec) : ℂ) := by
  apply catBlockState_bilin_diag_eq
  · exact shorBlockPauli_e000_inner_e111 ta pa tb pb
  · rw [← inner_conj_symm, shorBlockPauli_e000_inner_e111 tb pb ta pa, map_zero]

/-! ### Diagonal error-vector overlaps agree -/

/-- **Diagonal error-vector overlaps agree** (fact (A) of Exercise 10.10):
`⟪v_{i,1}, v_{j,1}⟫ = ⟪Eᵢ |1_L⟩, Eⱼ |1_L⟩⟫ = ⟪Eᵢ |0_L⟩, Eⱼ |0_L⟩⟫ = ⟪v_{i,0}, v_{j,0}⟫` for
**every** pair of errors `i, j`.

The overlap factors over the three cat blocks (`shorReg_inner_tmul`), and each per-block factor is
`s`-independent: a block touched by neither error contributes `⟪c_s, c_s⟫ = 1`
(`PureState.inner_self`), a block touched by exactly one error contributes `0` (the two
`..._self_eq_zero` lemmas), and a block touched by both (only when `i, j` sit in the same block)
contributes the `s`-independent two-Pauli factor
`blockSinglePauli_pauliErrorObs_catBlockState_inner_diag_eq`. Hence the whole product is the same
for the two codewords: the Gram matrix `αᵢⱼ = ⟪v_{i,0}, v_{j,0}⟫` sees both codewords identically,
the code's degeneracy under single-qubit Paulis. -/
theorem shorErrorVec_inner_diag_eq (i j : ShorErrorIndex) :
    (inner ℂ (shorErrorVec i 1) (shorErrorVec j 1) : ℂ)
      = (inner ℂ (shorErrorVec i 0) (shorErrorVec j 0) : ℂ) := by
  rcases i with _ | ⟨ti, bi, pi⟩ <;> rcases j with _ | ⟨tj, bj, pj⟩ <;>
    simp only [shorErrorVec, shorErrorFamily]
  · -- I, I : both codewords have unit norm
    simp only [one_apply_eq_self]
    rw [PureState.inner_self, PureState.inner_self]
  · -- I, Pauli : the touched block contributes a vanishing single-Pauli factor
    fin_cases bj <;>
      (simp only [shorPauliError, shorSinglePauli, shorCodeword,
        shorCatProduct, PureState.tmul_vec,
        ]
       conv_lhs => erw [shorReg_inner_tmul]
       conv_rhs => erw [shorReg_inner_tmul]
       simp only [ContinuousLinearMap.coe_coe, Observable.id_op, one_apply_eq_self,
         LinearMap.id_apply, PureState.inner_self,
             catBlockState_inner_blockSinglePauli_self_eq_zero,
         mul_one, mul_zero])
  · -- Pauli, I : symmetric
    fin_cases bi <;>
      (simp only [shorPauliError, shorSinglePauli, shorCodeword,
        shorCatProduct, PureState.tmul_vec,
        ]
       conv_lhs => erw [shorReg_inner_tmul]
       conv_rhs => erw [shorReg_inner_tmul]
       simp only [ContinuousLinearMap.coe_coe, Observable.id_op, one_apply_eq_self,
         LinearMap.id_apply, PureState.inner_self,
             blockSinglePauli_catBlockState_inner_self_eq_zero,
         mul_one, mul_zero])
  · -- Pauli, Pauli : same block ⇒ two-Pauli factor; different blocks ⇒ a vanishing factor
    fin_cases bi <;> fin_cases bj <;>
      (simp only [shorPauliError, shorSinglePauli, shorCodeword, shorCatProduct, PureState.tmul_vec,
        ]
       conv_lhs => erw [shorReg_inner_tmul]
       conv_rhs => erw [shorReg_inner_tmul]
       simp only [ContinuousLinearMap.coe_coe, Observable.id_op, one_apply_eq_self,
         LinearMap.id_apply, PureState.inner_self,
             blockSinglePauli_pauliErrorObs_catBlockState_inner_diag_eq,
         blockSinglePauli_catBlockState_inner_self_eq_zero,
         catBlockState_inner_blockSinglePauli_self_eq_zero, mul_one, one_mul, mul_zero])

end AxQM
