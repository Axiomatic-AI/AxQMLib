/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PhaseFlipCode
import AxQM.Postulates.API.Swap

/-!
# AxQM.Postulates.API — the phase-flip code protects against `{I, P₁, Q₁, P₂, Q₂, P₃, Q₃}`

Nielsen & Chuang's **Exercise 10.9** (p. 441) asks: *again consider the three-qubit phase-flip code*
(`|0_L⟩ = |+++⟩`, `|1_L⟩ = |−−−⟩`); *let `Pᵢ` and `Qᵢ` be the projectors onto the `|0⟩` and `|1⟩`
states, respectively, of the `i`-th qubit; prove that the code protects against the error set*
`{I, P₁, Q₁, P₂, Q₂, P₃, Q₃}`.

"Protects against" is N&C's language for the **quantum error-correction conditions** (Theorem 10.1):
a set `{Eᵢ}` is correctable iff `P Eᵢ† Eⱼ P = αᵢⱼ P` for a Hermitian `α` (`SatisfiesQECConditions`).

## The argument

Each projector is a linear combination of the identity and a single Pauli `Z` on its qubit:
on one qubit `|0⟩⟨0| = ½(I + Z)` and `|1⟩⟨1| = ½(I − Z)`, so on the three-qubit register

  `Pᵢ = ½(I + Zᵢ)`,  `Qᵢ = ½(I − Zᵢ)`,

i.e. every member of `{I, P₁, Q₁, P₂, Q₂, P₃, Q₃}` is a linear combination of the set
`{I, Z₁, Z₂, Z₃}` already shown correctable in **Exercise 10.8**
(`phaseFlipCode_satisfiesQECConditions`, with the identity coefficient matrix). N&C's own
discretization principle (Theorem 10.2, p. 440 — "any noise whose operation elements are linear
combinations of a correctable set is itself corrected") then gives the result immediately: it is the
reusable `SatisfiesQECConditions.recombine`, applied with the `4 × 7` recombination matrix
`phaseFlipRecombineMatrix` whose columns realise the seven combinations above.

Note this does **not** re-run the codeword-basis calculation of Exercise 10.8: the `Pᵢ`/`Qᵢ` are not
even permutations of the `±` basis (they mix `|+⟩` and `|−⟩`), so the direct Knill–Laflamme check
would be far messier — the point of the discretization lemma is that correctability of the projector
set is obtained *for free* from correctability of `{I, Z₁, Z₂, Z₃}`.

## Contents

* `qubitZeroProj` / `qubitOneProj` — the single-qubit computational-basis projectors `|0⟩⟨0|`,
  `|1⟩⟨1|`; `qubitZeroProj_eq_half_one_add_pauliZ` / `qubitOneProj_eq_half_one_sub_pauliZ` are the
  spectral identities `|0⟩⟨0| = ½(I + Z)`, `|1⟩⟨1| = ½(I − Z)`.
* `phaseFlipFullError` — the error set `{I, P₁, Q₁, P₂, Q₂, P₃, Q₃}` as operators on the register
  `qubit ⊗ (qubit ⊗ qubit)`, each `Pᵢ`/`Qᵢ` the single-wire projector `qubitZeroProj`/`qubitOneProj`
  embedded via `TensorProduct.mapL`.
* `phaseFlipRecombineMatrix` — the `Matrix (Fin 4) (Fin 7) ℂ` expressing each error as a linear
  combination of `phaseFlipErrorOp = {I, Z₁, Z₂, Z₃}`.
* `phaseFlipFullError_recombine` — the pointwise identity
  `phaseFlipFullError k = ∑ i, phaseFlipRecombineMatrix i k • phaseFlipErrorOp i` (`Pᵢ = ½(I + Zᵢ)`,
  `Qᵢ = ½(I − Zᵢ)`).
* `phaseFlipCode_satisfiesQECConditions_fullErrorSet` — **Exercise 10.9**:
  `SatisfiesQECConditions phaseFlipCodeProj phaseFlipFullError`.

The statement of Exercise 10.9 is in `AxQM/NC/Ch10/Exercise10_9.lean`.
-/

open scoped InnerProductSpace TensorProduct Matrix
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-! ### Single-qubit computational-basis projectors as `½(I ± Z)` -/

/-- **The single-qubit projector `|0⟩⟨0|`** onto the computational basis state `|0⟩`. -/
def qubitZeroProj : qubit.space →L[ℂ] qubit.space :=
  rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec

/-- **The single-qubit projector `|1⟩⟨1|`** onto the computational basis state `|1⟩`. -/
def qubitOneProj : qubit.space →L[ℂ] qubit.space :=
  rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec

/-- **Completeness for the single-qubit computational basis:** `|0⟩⟨0| + |1⟩⟨1| = 1`, the
resolution of identity `sum_rankOne_qubitBasis_eq_one` written over the two projectors. -/
theorem qubitZeroProj_add_qubitOneProj_eq_one :
    qubitZeroProj + qubitOneProj = (1 : qubit.space →L[ℂ] qubit.space) := by
  rw [qubitZeroProj, qubitOneProj, ← sum_rankOne_qubitBasis_eq_one, Fin.sum_univ_two]

/-- **`|0⟩⟨0| = ½(I + Z)`.** Proof: the completeness relation `|0⟩⟨0| + |1⟩⟨1| = 1`
(`qubitZeroProj_add_qubitOneProj_eq_one`) and the spectral decomposition `Z = |0⟩⟨0| − |1⟩⟨1|`
(`pauliZGate_op_eq_rankOne_sub`) give `1 + Z = 2|0⟩⟨0|`. -/
theorem qubitZeroProj_eq_half_one_add_pauliZ :
    qubitZeroProj = (2⁻¹ : ℂ) • (1 + pauliZGate.op) := by
  rw [qubitZeroProj, pauliZGate_op_eq_rankOne_sub, ← qubitZeroProj, ← qubitOneProj,
    ← qubitZeroProj_add_qubitOneProj_eq_one]
  module

/-- **`|1⟩⟨1| = ½(I − Z)`,** dual to `qubitZeroProj_eq_half_one_add_pauliZ`: from
`|0⟩⟨0| + |1⟩⟨1| = 1` (`qubitZeroProj_add_qubitOneProj_eq_one`) and `Z = |0⟩⟨0| − |1⟩⟨1|` one gets
`1 − Z = 2|1⟩⟨1|`. -/
theorem qubitOneProj_eq_half_one_sub_pauliZ :
    qubitOneProj = (2⁻¹ : ℂ) • (1 - pauliZGate.op) := by
  rw [qubitOneProj, pauliZGate_op_eq_rankOne_sub, ← qubitZeroProj, ← qubitOneProj,
    ← qubitZeroProj_add_qubitOneProj_eq_one]
  module

/-! ### The projector error set `{I, P₁, Q₁, P₂, Q₂, P₃, Q₃}` -/

/-- **The error set `{I, P₁, Q₁, P₂, Q₂, P₃, Q₃}` of Exercise 10.9**, as operators on the
three-qubit phase-flip register `qubit ⊗ (qubit ⊗ qubit)`. Indexed by `Fin 7`:
`0 ↦ I`; `1 ↦ P₁`, `2 ↦ Q₁`; `3 ↦ P₂`, `4 ↦ Q₂`; `5 ↦ P₃`, `6 ↦ Q₃`, where `Pₖ`/`Qₖ` are the
projectors onto `|0⟩`/`|1⟩` of qubit `k` — the single-wire projectors `qubitZeroProj`/`qubitOneProj`
tensored with identities on the other two wires (`TensorProduct.mapL … 1` embeddings mirroring the
wire structure of `phaseFlipErrorGate`). -/
def phaseFlipFullError : Fin 7 → (qubit ⊗ (qubit ⊗ qubit)).space →L[ℂ]
    (qubit ⊗ (qubit ⊗ qubit)).space
  | 0 => 1
  | 1 => TensorProduct.mapL qubitZeroProj 1
  | 2 => TensorProduct.mapL qubitOneProj 1
  | 3 => TensorProduct.mapL 1 (TensorProduct.mapL qubitZeroProj 1)
  | 4 => TensorProduct.mapL 1 (TensorProduct.mapL qubitOneProj 1)
  | 5 => TensorProduct.mapL 1 (TensorProduct.mapL 1 qubitZeroProj)
  | 6 => TensorProduct.mapL 1 (TensorProduct.mapL 1 qubitOneProj)

/-- **The recombination matrix** expressing each error of `phaseFlipFullError` as a linear
combination of `phaseFlipErrorOp = {I, Z₁, Z₂, Z₃}` (rows indexed by `Fin 4 = {I, Z₁, Z₂, Z₃}`,
columns by `Fin 7`). Column `0` is `I`; column `2k−1` is `½(e₀ + eₖ)` (realising `Pₖ`) and column
`2k` is `½(e₀ − eₖ)` (realising `Qₖ`). -/
def phaseFlipRecombineMatrix : Matrix (Fin 4) (Fin 7) ℂ :=
  !![1, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹;
     0, 2⁻¹, -2⁻¹, 0, 0, 0, 0;
     0, 0, 0, 2⁻¹, -2⁻¹, 0, 0;
     0, 0, 0, 0, 0, 2⁻¹, -2⁻¹]

set_option synthInstance.maxHeartbeats 400000 in
-- The bilinear `TensorProduct.mapL` distribution below forces `DistribSMul` synthesis over the
-- register-level continuous-linear-map algebra, which exceeds the default instance-search budget.
/-- **Each projector error is a linear combination of `{I, Z₁, Z₂, Z₃}`:**
`phaseFlipFullError k = ∑ i, phaseFlipRecombineMatrix i k • phaseFlipErrorOp i`. This is the content
`Pₖ = ½(I + Zₖ)`, `Qₖ = ½(I − Zₖ)`, obtained by pushing the single-qubit identities
`qubitZeroProj_eq_half_one_add_pauliZ` / `qubitOneProj_eq_half_one_sub_pauliZ` through the bilinear
`TensorProduct.mapL` embeddings (`mapL 1 1 = 1`, and `mapL` distributes over `+`, `-`, `•`), the
`Zₖ = phaseFlipErrorOp k` being `Z` embedded on wire `k`. -/
theorem phaseFlipFullError_recombine (k : Fin 7) :
    phaseFlipFullError k = ∑ i, phaseFlipRecombineMatrix i k • phaseFlipErrorOp i := by
  -- `phaseFlipErrorOp = {I, Z₁, Z₂, Z₃}` as `TensorProduct.mapL` embeddings of `Z` (all `rfl`).
  have eo1 : phaseFlipErrorOp 1 = TensorProduct.mapL pauliZGate.op 1 := rfl
  have eo2 : phaseFlipErrorOp 2 = TensorProduct.mapL 1 (TensorProduct.mapL pauliZGate.op 1) := rfl
  have eo3 : phaseFlipErrorOp 3 = TensorProduct.mapL 1 (TensorProduct.mapL 1 pauliZGate.op) := rfl
  -- The six wire identities `Pₖ = ½(I + Zₖ)`, `Qₖ = ½(I − Zₖ)`.
  have pw1 : phaseFlipFullError 1
      = (2⁻¹:ℂ) • phaseFlipErrorOp 0 + (2⁻¹:ℂ) • phaseFlipErrorOp 1 := by
    rw [(rfl : phaseFlipErrorOp 0 = 1), eo1]
    change TensorProduct.mapL qubitZeroProj 1 = _
    rw [qubitZeroProj_eq_half_one_add_pauliZ]
    simp only [TensorProduct.mapL_smul_left, TensorProduct.mapL_add_left, TensorProduct.mapL_one,
      smul_add]
    rfl
  have qw1 : phaseFlipFullError 2
      = (2⁻¹:ℂ) • phaseFlipErrorOp 0 - (2⁻¹:ℂ) • phaseFlipErrorOp 1 := by
    rw [(rfl : phaseFlipErrorOp 0 = 1), eo1]
    change TensorProduct.mapL qubitOneProj 1 = _
    rw [qubitOneProj_eq_half_one_sub_pauliZ]
    simp only [TensorProduct.mapL_smul_left, TensorProduct.mapL_sub_left, TensorProduct.mapL_one,
      smul_sub]
    rfl
  have pw2 : phaseFlipFullError 3
      = (2⁻¹:ℂ) • phaseFlipErrorOp 0 + (2⁻¹:ℂ) • phaseFlipErrorOp 2 := by
    rw [(rfl : phaseFlipErrorOp 0 = 1), eo2]
    change TensorProduct.mapL 1 (TensorProduct.mapL qubitZeroProj 1) = _
    rw [qubitZeroProj_eq_half_one_add_pauliZ]
    simp only [TensorProduct.mapL_smul_left, TensorProduct.mapL_smul_right,
      TensorProduct.mapL_add_left, TensorProduct.mapL_add_right, TensorProduct.mapL_one, smul_add]
    rfl
  have qw2 : phaseFlipFullError 4
      = (2⁻¹:ℂ) • phaseFlipErrorOp 0 - (2⁻¹:ℂ) • phaseFlipErrorOp 2 := by
    rw [(rfl : phaseFlipErrorOp 0 = 1), eo2]
    change TensorProduct.mapL 1 (TensorProduct.mapL qubitOneProj 1) = _
    rw [qubitOneProj_eq_half_one_sub_pauliZ]
    simp only [TensorProduct.mapL_smul_left, TensorProduct.mapL_smul_right,
      TensorProduct.mapL_sub_left, TensorProduct.mapL_sub_right, TensorProduct.mapL_one, smul_sub]
    rfl
  have pw3 : phaseFlipFullError 5
      = (2⁻¹:ℂ) • phaseFlipErrorOp 0 + (2⁻¹:ℂ) • phaseFlipErrorOp 3 := by
    rw [(rfl : phaseFlipErrorOp 0 = 1), eo3]
    change TensorProduct.mapL 1 (TensorProduct.mapL 1 qubitZeroProj) = _
    rw [qubitZeroProj_eq_half_one_add_pauliZ]
    simp only [TensorProduct.mapL_smul_right, TensorProduct.mapL_add_right, TensorProduct.mapL_one,
      smul_add]
    rfl
  have qw3 : phaseFlipFullError 6
      = (2⁻¹:ℂ) • phaseFlipErrorOp 0 - (2⁻¹:ℂ) • phaseFlipErrorOp 3 := by
    rw [(rfl : phaseFlipErrorOp 0 = 1), eo3]
    change TensorProduct.mapL 1 (TensorProduct.mapL 1 qubitOneProj) = _
    rw [qubitOneProj_eq_half_one_sub_pauliZ]
    simp only [TensorProduct.mapL_smul_right, TensorProduct.mapL_sub_right, TensorProduct.mapL_one,
      smul_sub]
    rfl
  match k with
  | 0 => rw [Fin.sum_univ_four]
         simp [phaseFlipRecombineMatrix, phaseFlipFullError, phaseFlipErrorOp, phaseFlipErrorGate,
           Evolution.id_op]
  | 1 => rw [pw1, Fin.sum_univ_four]; simp [phaseFlipRecombineMatrix]
  | 2 => rw [qw1, Fin.sum_univ_four]; simp [phaseFlipRecombineMatrix, sub_eq_add_neg]
  | 3 => rw [pw2, Fin.sum_univ_four]; simp [phaseFlipRecombineMatrix]
  | 4 => rw [qw2, Fin.sum_univ_four]; simp [phaseFlipRecombineMatrix, sub_eq_add_neg]
  | 5 => rw [pw3, Fin.sum_univ_four]; simp [phaseFlipRecombineMatrix]
  | 6 => rw [qw3, Fin.sum_univ_four]; simp [phaseFlipRecombineMatrix, sub_eq_add_neg]

/-- **Nielsen & Chuang, Exercise 10.9.** The three-qubit phase-flip code
(`|0_L⟩ = |+++⟩`, `|1_L⟩ = |−−−⟩`) protects against the error set `{I, P₁, Q₁, P₂, Q₂, P₃, Q₃}`,
where `Pᵢ`/`Qᵢ` are the projectors onto `|0⟩`/`|1⟩` of qubit `i`: the code projector
`phaseFlipCodeProj` and the projector error operators `phaseFlipFullError` satisfy the quantum
error-correction conditions (Theorem 10.1).

The proof is the discretization argument: each `Pᵢ = ½(I + Zᵢ)`, `Qᵢ = ½(I − Zᵢ)` is a linear
combination of `{I, Z₁, Z₂, Z₃}` (`phaseFlipFullError_recombine`), which Exercise 10.8
(`phaseFlipCode_satisfiesQECConditions`) already shows correctable;
`SatisfiesQECConditions.recombine` (N&C Theorem 10.2) transports correctability along the matrix. -/
theorem phaseFlipCode_satisfiesQECConditions_fullErrorSet :
    SatisfiesQECConditions phaseFlipCodeProj phaseFlipFullError :=
  phaseFlipCode_satisfiesQECConditions.recombine phaseFlipRecombineMatrix
    phaseFlipFullError_recombine

end AxQM
