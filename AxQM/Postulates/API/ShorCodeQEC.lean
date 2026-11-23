/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorErrorInnerProductDiag
import AxQM.Postulates.API.QuantumErrorCorrection

/-!
# AxQM.Postulates.API — the Shor code satisfies the QEC conditions (Exercise 10.10)

Nielsen & Chuang's **Exercise 10.10** (p. 441): the nine-qubit Shor code
`{|0_L⟩, |1_L⟩}` satisfies the quantum error-correction conditions (Theorem 10.1, Eq. (10.16)) for
the error set `{I} ∪ {X_j, Y_j, Z_j : j = 1..9}` — the identity together with every single-qubit
Pauli.

The two matrix-element facts are proved in the neighbouring files:

* **(B) off-diagonal-vanishing** `⟪v_{i,0}, v_{j,1}⟫ = 0` (`shorErrorVec_inner_offdiag_eq_zero`,
  `AxQM/Postulates/API/ShorErrorInnerProduct.lean`), and
* **(A) diagonal-equality** `⟪v_{i,1}, v_{j,1}⟫ = ⟪v_{i,0}, v_{j,0}⟫` (`shorErrorVec_inner_diag_eq`,
  `AxQM/Postulates/API/ShorErrorInnerProductDiag.lean`),

where `v_{i,s} = Eᵢ |s_L⟩` are the error vectors. This file combines them into the single
codeword-basis identity `⟪v_{i,a}, v_{j,b}⟫ = αᵢⱼ · δ_{a,b}` (`shorErrorVec_inner_eq`) and feeds it
to the Knill–Laflamme reduction `satisfiesKLConditions_of_inner_error_images` (the shared engine of
Exercises 10.7–10.10) to conclude `P Eᵢ† Eⱼ P = αᵢⱼ P`.

## The coefficient matrix is the Gram matrix — the code is *degenerate*

The coefficient matrix is `αᵢⱼ = ⟪v_{i,0}, v_{j,0}⟫` (`shorErrorAlpha`), the Gram matrix of the
error images of the `|0_L⟩` codeword, automatically **Hermitian** (`inner_conj_symm`). Unlike the
three-qubit bit-flip / phase-flip codes — where `α = 1` and the errors carry the codeword to an
*orthonormal* set — the Shor code is a **degenerate** code: distinct single-qubit Paulis in the
*same* cat block send a codeword to overlapping (non-orthogonal) states, so `α` has genuinely
nonzero off-diagonal entries. Faithfulness to N&C therefore requires proving the conditions with
this **general Hermitian `α`**, not the specialised `α = 1`; that is exactly the shape of
`SatisfiesQECConditions` (N&C Theorem 10.1: "for *some* Hermitian matrix `α`"), and no such
diagonality is asserted here.

## Contents

* `shorErrorAlpha` — the Gram / coefficient matrix `αᵢⱼ = ⟪v_{i,0}, v_{j,0}⟫`, and
  `shorErrorAlpha_isHermitian` its Hermiticity.
* `shorErrorVec_inner_eq` — the combined codeword matrix element
  `⟪v_{i,a}, v_{j,b}⟫ = αᵢⱼ · δ_{a,b}` (facts (A) and (B) packaged in the shape the Knill–Laflamme
  reduction consumes).
* `shorCode_satisfiesQECConditions` — **Exercise 10.10**: `SatisfiesQECConditions shorCodeProj
  shorErrorFamily`, the Shor code satisfies the quantum error-correction conditions.

## Related files

The phase-flip-code exercise (Exercise 10.8) is treated analogously in
`AxQM/Postulates/API/PhaseFlipCode.lean`. The Knill–Laflamme reduction
`satisfiesKLConditions_of_inner_error_images` is in
`ToMathlib/Analysis/InnerProductSpace/QuantumErrorCorrection.lean`.
-/

open scoped InnerProductSpace TensorProduct Matrix
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-! ### The Gram coefficient matrix `α` -/

/-- **The Shor-code coefficient matrix** `αᵢⱼ = ⟪v_{i,0}, v_{j,0}⟫ = ⟪Eᵢ |0_L⟩, Eⱼ |0_L⟩⟫`, the Gram
matrix of the error images of the `|0_L⟩` codeword. This is the matrix `α` of N&C's quantum
error-correction conditions `P Eᵢ† Eⱼ P = αᵢⱼ P` (Theorem 10.1); the diagonal-equality
`shorErrorVec_inner_diag_eq` guarantees the `|1_L⟩` codeword produces the *same* Gram matrix, the
hallmark of a degenerate code. -/
def shorErrorAlpha : Matrix ShorErrorIndex ShorErrorIndex ℂ :=
  Matrix.of fun i j => (inner ℂ (shorErrorVec i 0) (shorErrorVec j 0) : ℂ)

/-- **`α` is Hermitian.** A Gram matrix is always Hermitian: `conj αⱼᵢ = conj ⟪v_{j,0}, v_{i,0}⟫ =
⟪v_{i,0}, v_{j,0}⟫ = αᵢⱼ` (`inner_conj_symm`). This is the Hermiticity required of the coefficient
matrix in the quantum error-correction conditions. -/
theorem shorErrorAlpha_isHermitian : shorErrorAlpha.IsHermitian := by
  ext i j
  simp only [shorErrorAlpha, Matrix.conjTranspose_apply, Matrix.of_apply]
  exact inner_conj_symm _ _

/-! ### The combined codeword matrix element -/

/-- **The codeword-basis matrix element of the errors** (facts (A) and (B) of Exercise 10.10
combined): `⟪v_{i,a}, v_{j,b}⟫ = ⟪Eᵢ |a_L⟩, Eⱼ |b_L⟩⟫ = αᵢⱼ · δ_{a,b}`.

The four cases: for `a = b` the overlap is `αᵢⱼ` — definitionally so for `a = b = 0`, and by the
diagonal-equality `shorErrorVec_inner_diag_eq` for `a = b = 1`; for `a ≠ b` it vanishes, by the
off-diagonal-vanishing `shorErrorVec_inner_offdiag_eq_zero` (and its conjugate). This is exactly the
hypothesis `satisfiesKLConditions_of_inner_error_images` consumes. -/
theorem shorErrorVec_inner_eq (i j : ShorErrorIndex) (a b : Fin 2) :
    (inner ℂ (shorErrorVec i a) (shorErrorVec j b) : ℂ)
      = shorErrorAlpha i j * (if a = b then (1 : ℂ) else 0) := by
  fin_cases a <;> fin_cases b <;>
    simp only [shorErrorAlpha, Matrix.of_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceEq, ↓reduceIte, mul_one, mul_zero]
  · exact shorErrorVec_inner_offdiag_eq_zero i j
  · exact shorErrorVec_inner_offdiag i j (by decide)
  · exact shorErrorVec_inner_diag_eq i j

/-! ### Exercise 10.10 -/

/-- **Nielsen & Chuang, Exercise 10.10.** The nine-qubit Shor code (logical codewords
`shorCodeword 0 = |0_L⟩`, `shorCodeword 1 = |1_L⟩`) satisfies the quantum error-correction
conditions (Theorem 10.1) for the error set `{I} ∪ {X_j, Y_j, Z_j : j = 1..9}`
(`shorErrorFamily`): the code projector `shorCodeProj` and error operators `shorErrorFamily` satisfy
`SatisfiesQECConditions` with the **Hermitian Gram matrix** `α = shorErrorAlpha` (`P Eᵢ† Eⱼ P = αᵢⱼ
P`). Hence `{I} ∪ {X_j, Y_j, Z_j}` is a correctable set for the Shor code — every single-qubit error
is correctable.

The matrix `α` is *not* diagonal: the Shor code is a **degenerate** code (distinct Paulis in the
same cat block act identically on the codewords up to phase), so this is genuinely N&C's "some
Hermitian `α`" condition, not the sharper orthonormal-image condition (`α = 1`) of the bit-flip /
phase-flip codes. -/
theorem shorCode_satisfiesQECConditions :
    SatisfiesQECConditions shorCodeProj shorErrorFamily :=
  ⟨shorErrorAlpha, shorErrorAlpha_isHermitian,
    satisfiesKLConditions_of_inner_error_images (fun s => (shorCodeword s).vec) shorErrorFamily
      shorErrorAlpha (fun i j a b => shorErrorVec_inner_eq i j a b)⟩

end AxQM
