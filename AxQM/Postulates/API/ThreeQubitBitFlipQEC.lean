/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BitFlipSyndromeMeasurement
import AxQM.Postulates.API.QuantumErrorCorrection

/-!
# AxQM.Postulates.API — the QEC conditions for the three-qubit bit-flip code (N&C Ex 10.7)

Infrastructure for **Nielsen & Chuang, Exercise 10.7**: the three-qubit bit-flip code
of §10.1.1, with code projector `P = |000⟩⟨000| + |111⟩⟨111|` (`bitFlipSyndromeProj 0`), satisfies
the quantum error-correction conditions (N&C Thm 10.1, `SatisfiesQECConditions`) for the
*non-trace-preserving* noise process whose operation elements are

  `{ √(1−p)³ · I, √(p(1−p)²) · X₁, √(p(1−p)²) · X₂, √(p(1−p)²) · X₃ }`

(bit flips on zero or one qubit; the two- and three-qubit bit flips are deliberately omitted, so
`∑ᵢ Eᵢ† Eᵢ ≠ 1`). Here `Xₖ` is the Pauli-`X` bit flip on qubit `k` of the register
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`.

**The verification.** The QEC conditions `P Eᵢ† Eⱼ P = αᵢⱼ P` hold with the *diagonal* Hermitian
matrix `α = diag((1−p)³, p(1−p)², p(1−p)², p(1−p)²)`. The whole computation reduces to one operator
identity for the *unscaled* errors `T = (I, X₁, X₂, X₃)`:

* off the diagonal, a single bit flip carries the code space `span{|000⟩,|111⟩}` into single-error
  strings, and a product of two *distinct* bit flips into two-error strings, both orthogonal to the
  code — so `P Xₖ P = 0` and `P Xₖ Xₗ P = 0` (`k ≠ l`);
* on the diagonal, `Xₖ² = I` and `P² = P` give `P Tᵢ² P = P`.

The scalar coefficients then contribute the `α` entries via `√a · √a = a` for `a ≥ 0` (needing
`0 ≤ p ≤ 1`).

## Contents

* `bitFlipX k` — the three single-qubit bit-flip errors `X₁, X₂, X₃` as tensor observables on
  `bitFlipReg`, with `bitFlipX_op_qubitThreeBasis` (each flips the corresponding bit) and
  `bitFlipX_op_involution` (`Xₖ² = 1`).
* `codeProj_comp_comp_codeProj_eq_zero` — the workhorse: `P M P = 0` whenever `M` maps both
  codewords out of the code space; with `codeProj_comp_bitFlipX_comp_codeProj` (`P Xₖ P = 0`) and
  `codeProj_comp_bitFlipX_comp_bitFlipX_comp_codeProj` (`P Xₖ Xₗ P = 0`, `k ≠ l`).
* `bitFlipErrorOp` — the unscaled error family `T = (I, X₁, X₂, X₃)`, with
  `codeProj_bitFlipErrorOp_sandwich_diag` / `_offdiag` (`P Tᵢ Tⱼ P = δᵢⱼ P`).
* `threeBitFlipNoise p` / `threeBitFlipAlpha p` — the four noise operation elements and the diagonal
  Hermitian matrix `α`.
* `threeBitFlipNoise_satisfiesKLConditions` — the explicit Knill–Laflamme identities
  `P Eᵢ† Eⱼ P = αᵢⱼ P` (N&C Eq. 10.16), the "verification".
* `threeBitFlipNoise_satisfiesQECConditions` — the headline (N&C Ex 10.7): the QEC conditions hold.

The statement of Exercise 10.7 is in `AxQM/NC/Ch10/Exercise10_7.lean`.
-/

open scoped InnerProductSpace TensorProduct Matrix
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-! ### The single-qubit bit-flip errors `X₁, X₂, X₃` on the register -/

/-- **The three single-qubit bit-flip errors** `X₁ = X⊗I⊗I`, `X₂ = I⊗X⊗I`, `X₃ = I⊗I⊗X` on the
three-qubit register `bitFlipReg`, as tensor observables (N&C's `X₁, X₂, X₃`). Indexed by
`k : Fin 3` (`0 ↦ X₁`, etc.). -/
def bitFlipX : Fin 3 → Observable bitFlipReg :=
  ![pauliXObservable ⊗ (Observable.id qubit ⊗ Observable.id qubit),
    Observable.id qubit ⊗ (pauliXObservable ⊗ Observable.id qubit),
    Observable.id qubit ⊗ (Observable.id qubit ⊗ pauliXObservable)]

/-- `X₁ = X⊗I⊗I` flips the first bit of a computational-basis ket:
`X₁ |b₁b₂b₃⟩ = |(b₁+1)b₂b₃⟩`. -/
theorem bitFlipX_zero_op_qubitThreeBasis (b : Fin 2 × Fin 2 × Fin 2) :
    (pauliXObservable ⊗ (Observable.id qubit ⊗ Observable.id qubit)).op (qubitThreeBasis b).vec
      = (qubitThreeBasis (b.1 + 1, b.2.1, b.2.2)).vec := by
  simp only [qubitThreeBasis, PureState.tmul_vec]
  erw [Observable.tmul_op_tmul, Observable.tmul_op_tmul]
  simp only [Observable.id_op, one_apply_eq_self, pauliXObservable_op_apply_qubitBasis]
  rfl

/-- `X₂ = I⊗X⊗I` flips the second bit: `X₂ |b₁b₂b₃⟩ = |b₁(b₂+1)b₃⟩`. -/
theorem bitFlipX_one_op_qubitThreeBasis (b : Fin 2 × Fin 2 × Fin 2) :
    (Observable.id qubit ⊗ (pauliXObservable ⊗ Observable.id qubit)).op (qubitThreeBasis b).vec
      = (qubitThreeBasis (b.1, b.2.1 + 1, b.2.2)).vec := by
  simp only [qubitThreeBasis, PureState.tmul_vec]
  erw [Observable.tmul_op_tmul, Observable.tmul_op_tmul]
  simp only [Observable.id_op, one_apply_eq_self, pauliXObservable_op_apply_qubitBasis]
  rfl

/-- `X₃ = I⊗I⊗X` flips the third bit: `X₃ |b₁b₂b₃⟩ = |b₁b₂(b₃+1)⟩`. -/
theorem bitFlipX_two_op_qubitThreeBasis (b : Fin 2 × Fin 2 × Fin 2) :
    (Observable.id qubit ⊗ (Observable.id qubit ⊗ pauliXObservable)).op (qubitThreeBasis b).vec
      = (qubitThreeBasis (b.1, b.2.1, b.2.2 + 1)).vec := by
  simp only [qubitThreeBasis, PureState.tmul_vec]
  erw [Observable.tmul_op_tmul, Observable.tmul_op_tmul]
  simp only [Observable.id_op, one_apply_eq_self, pauliXObservable_op_apply_qubitBasis]
  rfl

/-- **`Xₖ` flips bit `k` of a computational-basis ket:** `Xₖ |b⟩ = |qubitThreeFlip k b⟩`. -/
theorem bitFlipX_op_qubitThreeBasis (k : Fin 3) (b : Fin 2 × Fin 2 × Fin 2) :
    (bitFlipX k).op (qubitThreeBasis b).vec = (qubitThreeBasis (qubitThreeFlip k b)).vec := by
  fin_cases k
  · exact bitFlipX_zero_op_qubitThreeBasis b
  · exact bitFlipX_one_op_qubitThreeBasis b
  · exact bitFlipX_two_op_qubitThreeBasis b

/-- **`Xₖ` is an involution:** `Xₖ² = 1` (a double flip returns every basis ket to itself). -/
theorem bitFlipX_op_involution (k : Fin 3) : (bitFlipX k).op ∘L (bitFlipX k).op = 1 := by
  apply qubitThree_op_ext
  intro b
  rw [ContinuousLinearMap.comp_apply, bitFlipX_op_qubitThreeBasis, bitFlipX_op_qubitThreeBasis,
    qubitThreeFlip_involutive, one_apply_eq_self]

/-! ### The code projector `P = |000⟩⟨000| + |111⟩⟨111|` sandwich lemmas -/

/-- **`P |b⟩` on a computational-basis ket:** the code projector `P = |000⟩⟨000| + |111⟩⟨111|`
(`bitFlipSyndromeProj 0`) keeps `|000⟩` and `|111⟩` and annihilates every other basis ket. -/
theorem bitFlipSyndromeProj_zero_apply_qubitThreeBasis (b : Fin 2 × Fin 2 × Fin 2) :
    (bitFlipSyndromeProj 0) (qubitThreeBasis b).vec
      = (if ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2)) = b then (1 : ℂ) else 0)
          • (qubitThreeBasis ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2))).vec
        + (if ((1 : Fin 2), (1 : Fin 2), (1 : Fin 2)) = b then (1 : ℂ) else 0)
          • (qubitThreeBasis ((1 : Fin 2), (1 : Fin 2), (1 : Fin 2))).vec := by
  simp only [bitFlipSyndromeProj, bitFlipSyndromeStr, Matrix.cons_val_zero,
    _root_.add_apply, qubitThreeBasis_rankOne_apply]

/-- **Workhorse for the off-diagonal QEC conditions.** If an operator `M` carries both codewords
`|000⟩`, `|111⟩` out of the code space (`P (M |000⟩) = 0` and `P (M |111⟩) = 0`), then `P M P = 0`.
Because `P = |000⟩⟨000| + |111⟩⟨111|`, the sandwich `P M P` acts on any ket only through
`M`'s action on the two codewords. -/
theorem codeProj_comp_comp_codeProj_eq_zero (M : bitFlipReg.space →L[ℂ] bitFlipReg.space)
    (h000 : (bitFlipSyndromeProj 0)
      (M (qubitThreeBasis ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2))).vec) = 0)
    (h111 : (bitFlipSyndromeProj 0)
      (M (qubitThreeBasis ((1 : Fin 2), (1 : Fin 2), (1 : Fin 2))).vec) = 0) :
    (bitFlipSyndromeProj 0) ∘L M ∘L (bitFlipSyndromeProj 0) = 0 := by
  apply qubitThree_op_ext
  intro b
  rw [_root_.zero_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, bitFlipSyndromeProj_zero_apply_qubitThreeBasis, map_add,
    map_smul, map_smul, map_add, map_smul, map_smul, h000, h111, smul_zero, smul_zero, add_zero]

/-- **`P² = P`:** the code projector is idempotent. -/
theorem bitFlipSyndromeProj_zero_comp_self :
    (bitFlipSyndromeProj 0) ∘L (bitFlipSyndromeProj 0) = bitFlipSyndromeProj 0 := by
  apply qubitThree_op_ext
  intro b
  rw [ContinuousLinearMap.comp_apply, bitFlipSyndromeProj_zero_apply_qubitThreeBasis, map_add,
    map_smul, map_smul, bitFlipSyndromeProj_zero_apply_qubitThreeBasis,
    bitFlipSyndromeProj_zero_apply_qubitThreeBasis]
  fin_cases b <;> simp

/-- **A single bit flip leaves the code space:** `P Xₖ P = 0`. Each `Xₖ |000⟩` / `Xₖ |111⟩` is a
single-error string, orthogonal to both codewords. -/
theorem codeProj_comp_bitFlipX_comp_codeProj (k : Fin 3) :
    (bitFlipSyndromeProj 0) ∘L (bitFlipX k).op ∘L (bitFlipSyndromeProj 0) = 0 := by
  apply codeProj_comp_comp_codeProj_eq_zero <;>
    · rw [bitFlipX_op_qubitThreeBasis, bitFlipSyndromeProj_zero_apply_qubitThreeBasis]
      fin_cases k <;> · rw [ite_eq_right (by decide), ite_eq_right (by decide)]; simp

/-- **A product of two distinct bit flips leaves the code space:** `P Xₖ Xₗ P = 0` for `k ≠ l`.
Each `Xₖ Xₗ |000⟩` / `Xₖ Xₗ |111⟩` is a two-error string, orthogonal to both codewords. -/
theorem codeProj_comp_bitFlipX_comp_bitFlipX_comp_codeProj {k l : Fin 3} (h : k ≠ l) :
    (bitFlipSyndromeProj 0) ∘L (bitFlipX k).op ∘L (bitFlipX l).op ∘L (bitFlipSyndromeProj 0)
      = 0 := by
  rw [← ContinuousLinearMap.comp_assoc (bitFlipX k).op (bitFlipX l).op (bitFlipSyndromeProj 0)]
  apply codeProj_comp_comp_codeProj_eq_zero <;>
    · rw [ContinuousLinearMap.comp_apply, bitFlipX_op_qubitThreeBasis, bitFlipX_op_qubitThreeBasis,
        bitFlipSyndromeProj_zero_apply_qubitThreeBasis]
      fin_cases k <;> fin_cases l <;>
        first
          | exact absurd rfl h
          | · rw [ite_eq_right (by decide), ite_eq_right (by decide)]; simp

/-- **`P Xₖ² P = P`:** for a repeated single error, `Xₖ² = I` and `P² = P` give the code projector
back. -/
theorem codeProj_comp_bitFlipX_sq_comp_codeProj (k : Fin 3) :
    (bitFlipSyndromeProj 0) ∘L (bitFlipX k).op ∘L (bitFlipX k).op ∘L (bitFlipSyndromeProj 0)
      = bitFlipSyndromeProj 0 := by
  rw [← ContinuousLinearMap.comp_assoc (bitFlipX k).op (bitFlipX k).op (bitFlipSyndromeProj 0),
    bitFlipX_op_involution, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    bitFlipSyndromeProj_zero_comp_self]

/-! ### The unscaled error family and the sandwich identity `P Tᵢ Tⱼ P = δᵢⱼ P` -/

/-- **The four unscaled error operators** `T = (I, X₁, X₂, X₃)` — the noise operation elements with
their scalar coefficients stripped off. -/
def bitFlipErrorOp : Fin 4 → bitFlipReg.space →L[ℂ] bitFlipReg.space :=
  ![1, (bitFlipX 0).op, (bitFlipX 1).op, (bitFlipX 2).op]

/-- Helper: `P (1 Xₖ) P = 0`, the off-diagonal identity in the form appearing after the unscaled
identity `T₀ = I` (used by `codeProj_bitFlipErrorOp_sandwich_offdiag`). -/
theorem codeProj_comp_one_comp_bitFlipX_comp_codeProj (k : Fin 3) :
    (bitFlipSyndromeProj 0) ∘L (1 : bitFlipReg.space →L[ℂ] bitFlipReg.space) ∘L (bitFlipX k).op
      ∘L (bitFlipSyndromeProj 0) = 0 := by
  rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  exact codeProj_comp_bitFlipX_comp_codeProj k

/-- Helper: `P (Xₖ 1) P = 0`, the off-diagonal identity in the form appearing after the unscaled
identity `T₀ = I` (used by `codeProj_bitFlipErrorOp_sandwich_offdiag`). -/
theorem codeProj_comp_bitFlipX_comp_one_comp_codeProj (k : Fin 3) :
    (bitFlipSyndromeProj 0) ∘L (bitFlipX k).op ∘L (1 : bitFlipReg.space →L[ℂ] bitFlipReg.space)
      ∘L (bitFlipSyndromeProj 0) = 0 := by
  rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  exact codeProj_comp_bitFlipX_comp_codeProj k

/-- **The diagonal sandwich identity:** `P Tᵢ Tᵢ P = P` for the unscaled error family — a repeated
error `Tᵢ² = I` gives the code projector back (with `P² = P`). -/
theorem codeProj_bitFlipErrorOp_sandwich_diag (i : Fin 4) :
    (bitFlipSyndromeProj 0) ∘L (bitFlipErrorOp i) ∘L (bitFlipErrorOp i) ∘L (bitFlipSyndromeProj 0)
      = bitFlipSyndromeProj 0 := by
  fin_cases i
  · change (bitFlipSyndromeProj 0) ∘L (1 : bitFlipReg.space →L[ℂ] bitFlipReg.space)
        ∘L (1 : bitFlipReg.space →L[ℂ] bitFlipReg.space) ∘L (bitFlipSyndromeProj 0)
      = bitFlipSyndromeProj 0
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.id_comp,
      bitFlipSyndromeProj_zero_comp_self]
  · exact codeProj_comp_bitFlipX_sq_comp_codeProj 0
  · exact codeProj_comp_bitFlipX_sq_comp_codeProj 1
  · exact codeProj_comp_bitFlipX_sq_comp_codeProj 2

/-- **The off-diagonal sandwich identity:** `P Tᵢ Tⱼ P = 0` for `i ≠ j` — distinct errors are
distinguished by the code (they carry it out of the code space). -/
theorem codeProj_bitFlipErrorOp_sandwich_offdiag {i j : Fin 4} (h : i ≠ j) :
    (bitFlipSyndromeProj 0) ∘L (bitFlipErrorOp i) ∘L (bitFlipErrorOp j) ∘L (bitFlipSyndromeProj 0)
      = 0 := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl h
  · exact codeProj_comp_one_comp_bitFlipX_comp_codeProj 0
  · exact codeProj_comp_one_comp_bitFlipX_comp_codeProj 1
  · exact codeProj_comp_one_comp_bitFlipX_comp_codeProj 2
  · exact codeProj_comp_bitFlipX_comp_one_comp_codeProj 0
  · exact absurd rfl h
  · exact codeProj_comp_bitFlipX_comp_bitFlipX_comp_codeProj (k := 0) (l := 1) (by decide)
  · exact codeProj_comp_bitFlipX_comp_bitFlipX_comp_codeProj (k := 0) (l := 2) (by decide)
  · exact codeProj_comp_bitFlipX_comp_one_comp_codeProj 1
  · exact codeProj_comp_bitFlipX_comp_bitFlipX_comp_codeProj (k := 1) (l := 0) (by decide)
  · exact absurd rfl h
  · exact codeProj_comp_bitFlipX_comp_bitFlipX_comp_codeProj (k := 1) (l := 2) (by decide)
  · exact codeProj_comp_bitFlipX_comp_one_comp_codeProj 2
  · exact codeProj_comp_bitFlipX_comp_bitFlipX_comp_codeProj (k := 2) (l := 0) (by decide)
  · exact codeProj_comp_bitFlipX_comp_bitFlipX_comp_codeProj (k := 2) (l := 1) (by decide)
  · exact absurd rfl h

/-- Each unscaled error operator is **self-adjoint** (`Tᵢ† = Tᵢ`): `I` and each `Xₖ` are
self-adjoint. -/
theorem bitFlipErrorOp_adjoint (i : Fin 4) :
    ContinuousLinearMap.adjoint (bitFlipErrorOp i) = bitFlipErrorOp i := by
  fin_cases i
  · exact (ContinuousLinearMap.star_eq_adjoint _).symm.trans (star_one _)
  · exact (ContinuousLinearMap.star_eq_adjoint _).symm.trans (bitFlipX 0).selfAdjoint
  · exact (ContinuousLinearMap.star_eq_adjoint _).symm.trans (bitFlipX 1).selfAdjoint
  · exact (ContinuousLinearMap.star_eq_adjoint _).symm.trans (bitFlipX 2).selfAdjoint

/-! ### The noise operation elements, the matrix `α`, and the QEC conditions -/

variable (p : ℝ)

/-- The real coefficients of the noise operation elements: `√(1−p)³` for no bit flip, `√(p(1−p)²)`
for each single bit flip. -/
def threeBitFlipNoiseCoeff : Fin 4 → ℝ :=
  ![Real.sqrt ((1 - p) ^ 3), Real.sqrt (p * (1 - p) ^ 2), Real.sqrt (p * (1 - p) ^ 2),
    Real.sqrt (p * (1 - p) ^ 2)]

/-- **The four noise operation elements** of N&C Ex 10.7: `E₀ = √(1−p)³ · I` (no bit flip) and
`Eₖ = √(p(1−p)²) · Xₖ` (a bit flip on qubit `k`), for `k = 1, 2, 3`. The two- and three-qubit bit
flips are omitted, so this is *not* trace-preserving. -/
def threeBitFlipNoise : Fin 4 → bitFlipReg.space →L[ℂ] bitFlipReg.space :=
  fun i => (threeBitFlipNoiseCoeff p i : ℂ) • bitFlipErrorOp i

/-- **The Hermitian matrix `α` of the QEC conditions**, diagonal with entries `(1−p)³` (no flip) and
`p(1−p)²` (each single flip): `α = diag((1−p)³, p(1−p)², p(1−p)², p(1−p)²)`. -/
def threeBitFlipAlpha : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![(((1 - p) ^ 3 : ℝ) : ℂ), ((p * (1 - p) ^ 2 : ℝ) : ℂ),
    ((p * (1 - p) ^ 2 : ℝ) : ℂ), ((p * (1 - p) ^ 2 : ℝ) : ℂ)]

/-- The noise matrix `α` is **Hermitian**: it is diagonal with real entries. -/
theorem threeBitFlipAlpha_isHermitian : (threeBitFlipAlpha p).IsHermitian := by
  rw [threeBitFlipAlpha]
  refine Matrix.isHermitian_diagonal_iff.mpr fun i => ?_
  fin_cases i <;> simp [IsSelfAdjoint, Complex.conj_ofReal]

/-- Each noise operation element is **self-adjoint** (`Eᵢ† = Eᵢ`): a real multiple of the
self-adjoint operators `I` and `Xₖ`. -/
theorem threeBitFlipNoise_adjoint (i : Fin 4) :
    ContinuousLinearMap.adjoint (threeBitFlipNoise p i) = threeBitFlipNoise p i := by
  rw [threeBitFlipNoise, ← ContinuousLinearMap.star_eq_adjoint, star_smul,
    ContinuousLinearMap.star_eq_adjoint, bitFlipErrorOp_adjoint]
  congr 1

/-- **Nielsen & Chuang, Exercise 10.7 — the Knill–Laflamme identities.** For `0 ≤ p ≤ 1` the noise
operation elements satisfy `P Eᵢ† Eⱼ P = αᵢⱼ P` (N&C Eq. 10.16) with the diagonal Hermitian
`α = diag((1−p)³, p(1−p)², p(1−p)², p(1−p)²)`. This is the direct verification of the QEC conditions
the exercise asks for. -/
theorem threeBitFlipNoise_satisfiesKLConditions (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ContinuousLinearMap.SatisfiesKLConditions (bitFlipSyndromeProj 0) (threeBitFlipNoise p)
      (threeBitFlipAlpha p) := by
  have hcube : Real.sqrt ((1 - p) ^ 3) * Real.sqrt ((1 - p) ^ 3) = (1 - p) ^ 3 :=
    Real.mul_self_sqrt (pow_nonneg (by linarith) 3)
  have hpp : Real.sqrt (p * (1 - p) ^ 2) * Real.sqrt (p * (1 - p) ^ 2) = p * (1 - p) ^ 2 :=
    Real.mul_self_sqrt (mul_nonneg hp0 (sq_nonneg _))
  intro i j
  rw [threeBitFlipNoise_adjoint]
  simp only [threeBitFlipNoise, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    smul_smul]
  rcases eq_or_ne i j with h | h
  · subst h
    rw [codeProj_bitFlipErrorOp_sandwich_diag, threeBitFlipAlpha, Matrix.diagonal_apply_eq]
    congr 1
    fin_cases i
    · change ((Real.sqrt ((1 - p) ^ 3) : ℂ)) * ((Real.sqrt ((1 - p) ^ 3) : ℂ))
        = (((1 - p) ^ 3 : ℝ) : ℂ)
      rw [← Complex.ofReal_mul, hcube]
    · change ((Real.sqrt (p * (1 - p) ^ 2) : ℂ)) * ((Real.sqrt (p * (1 - p) ^ 2) : ℂ))
        = ((p * (1 - p) ^ 2 : ℝ) : ℂ)
      rw [← Complex.ofReal_mul, hpp]
    · change ((Real.sqrt (p * (1 - p) ^ 2) : ℂ)) * ((Real.sqrt (p * (1 - p) ^ 2) : ℂ))
        = ((p * (1 - p) ^ 2 : ℝ) : ℂ)
      rw [← Complex.ofReal_mul, hpp]
    · change ((Real.sqrt (p * (1 - p) ^ 2) : ℂ)) * ((Real.sqrt (p * (1 - p) ^ 2) : ℂ))
        = ((p * (1 - p) ^ 2 : ℝ) : ℂ)
      rw [← Complex.ofReal_mul, hpp]
  · rw [codeProj_bitFlipErrorOp_sandwich_offdiag h, smul_zero, threeBitFlipAlpha,
      Matrix.diagonal_apply_ne _ h, zero_smul]

/-- **Nielsen & Chuang, Exercise 10.7.** The three-qubit bit-flip code (code projector
`P = |000⟩⟨000| + |111⟩⟨111|`) satisfies the **quantum error-correction conditions**
(`SatisfiesQECConditions`, N&C Thm 10.1) for the non-trace-preserving noise process with operation
elements `{√(1−p)³ · I, √(p(1−p)²) · X₁, √(p(1−p)²) · X₂, √(p(1−p)²) · X₃}` (`0 ≤ p ≤ 1`): there
is a Hermitian `α` with `P Eᵢ† Eⱼ P = αᵢⱼ P`, witnessed by
`α = diag((1−p)³, p(1−p)², p(1−p)², p(1−p)²)`. -/
theorem threeBitFlipNoise_satisfiesQECConditions (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    SatisfiesQECConditions (bitFlipSyndromeProj 0) (threeBitFlipNoise p) :=
  ⟨threeBitFlipAlpha p, threeBitFlipAlpha_isHermitian p,
    threeBitFlipNoise_satisfiesKLConditions p hp0 hp1⟩

end AxQM
