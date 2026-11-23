/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliEigen
import AxQM.Postulates.API.Observable
import AxQM.Postulates.API.PauliMeasurement
import AxQM.Postulates.API.CascadedMeasurement
import AxQM.Postulates.API.QubitThree
import AxQM.Concrete.TensorScalar

/-!
# AxQM.Postulates.API — the three-qubit bit-flip syndrome measurement

Infrastructure for Nielsen & Chuang §10.1.1 / Exercise 10.3: the syndrome
measurement of the three-qubit bit-flip code, described **two ways** — as a cascade of two
`±1` observable measurements, and as a single four-outcome projective measurement — together
with the operator identity that makes the two descriptions coincide.

On the three-qubit register `bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`:

* `zzIObservable` (`Z₁Z₂ = Z ⊗ Z ⊗ I`) and `izzObservable` (`Z₂Z₃ = I ⊗ Z ⊗ Z`) are the two
  syndrome observables (N&C eq. 10.12); each is a self-adjoint involution (`zzI_involution`,
  `izz_involution`), so `Observable.signMeasurement` turns it into a two-outcome projective
  measurement (`bitFlipZ12Measurement`, `bitFlipZ23Measurement`).
* `bitFlipSyndromeProj` are the four bit-flip syndrome projectors of N&C eqns (10.5)–(10.8):
  `P₀ = |000⟩⟨000|+|111⟩⟨111|`, `P₁ = |100⟩⟨100|+|011⟩⟨011|`, `P₂ = |010⟩⟨010|+|101⟩⟨101|`,
  `P₃ = |001⟩⟨001|+|110⟩⟨110|`, and `bitFlipSyndromeMeasurement` bundles them into a single
  four-outcome `Measurement (Fin 4)`.
* `cascade_op_eq_syndromeProj` is the heart of Exercise 10.3: the cascade
  `bitFlipZ12Measurement` then `bitFlipZ23Measurement` has, for each joint outcome
  `(s₁, s₂) : Fin 2 × Fin 2`, exactly the syndrome projector `Pᵢ` with `i = bitFlipRelabel (s₁,s₂)`
  as its measurement operator. The relabeling `bitFlipRelabel` is N&C's outcome dictionary
  `(+,+) ↦ 0` (no error), `(−,+) ↦ 1` (qubit 1), `(−,−) ↦ 2` (qubit 2), `(+,−) ↦ 3` (qubit 3).

The two physical-equivalence statements ("same statistics and post-measurement states") are the
theorems of `AxQM/NC/Ch10/Exercise10_3.lean`, which follow from the operator
identity here via the general `Measurement.bornProb_congr` / `Measurement.postMeasurement_congr`
bridges (outcome operators equal ⇒ Born probabilities and collapses equal), which are in
`AxQM/Postulates/API/CascadedMeasurement.lean`.

The three-qubit register's computational basis and its extensionality / orthonormality tools are
the shared `qubitThreeBasis` and helpers from `Postulates/API/QubitThree.lean`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-! ### The three-qubit register

The register's computational basis (`qubitThreeBasis`), its extensionality lemma
(`qubitThree_op_ext`), orthonormality (`qubitThreeBasis_orthonormal`), and the rank-one action
(`qubitThreeBasis_rankOne_apply`) are the shared tools from `Postulates/API/QubitThree.lean`. -/

/-- The **three-qubit register** `qubit ⊗ (qubit ⊗ qubit)`, the physical system of the three-qubit
bit-flip code. -/
abbrev bitFlipReg : QSystem := qubit ⊗ (qubit ⊗ qubit)

/-! ### The syndrome observables `Z₁Z₂`, `Z₂Z₃` and their `±1` measurements -/

/-- **`Z₁Z₂ = Z ⊗ Z ⊗ I`**, the first syndrome observable (N&C eq. 10.12): compares qubits 1 and 2.
-/
def zzIObservable : Observable bitFlipReg :=
  pauliZObservable ⊗ (pauliZObservable ⊗ Observable.id qubit)

/-- **`Z₂Z₃ = I ⊗ Z ⊗ Z`**, the second syndrome observable: compares qubits 2 and 3. -/
def izzObservable : Observable bitFlipReg :=
  Observable.id qubit ⊗ (pauliZObservable ⊗ pauliZObservable)

/-- **`Z₁Z₂` acts diagonally:** `Z₁Z₂ |b₁b₂b₃⟩ = (−1)^{b₁+b₂} |b₁b₂b₃⟩` (only the first two qubits'
`Z`s contribute; the third factor is the identity). -/
theorem zzI_op_ket (b : Fin 2 × Fin 2 × Fin 2) :
    zzIObservable.op (qubitThreeBasis b).vec
      = ((-1 : ℂ) ^ (b.1 : ℕ) * (-1 : ℂ) ^ (b.2.1 : ℕ)) • (qubitThreeBasis b).vec := by
  simp only [qubitThreeBasis, PureState.tmul_vec, zzIObservable]
  erw [Observable.tmul_op_tmul, Observable.tmul_op_tmul]
  simp only [Observable.id_op, one_apply_eq_self, pauliZObservable_op_apply_qubitBasis]
  exact Concrete.smul_tmul_smul_tmul_left _ _ _ _ _

/-- **`Z₂Z₃` acts diagonally:** `Z₂Z₃ |b₁b₂b₃⟩ = (−1)^{b₂+b₃} |b₁b₂b₃⟩`. -/
theorem izz_op_ket (b : Fin 2 × Fin 2 × Fin 2) :
    izzObservable.op (qubitThreeBasis b).vec
      = ((-1 : ℂ) ^ (b.2.1 : ℕ) * (-1 : ℂ) ^ (b.2.2 : ℕ)) • (qubitThreeBasis b).vec := by
  simp only [qubitThreeBasis, PureState.tmul_vec, izzObservable]
  erw [Observable.tmul_op_tmul, Observable.tmul_op_tmul]
  simp only [Observable.id_op, one_apply_eq_self, pauliZObservable_op_apply_qubitBasis]
  exact Concrete.tmul_smul_tmul_smul_right _ _ _ _ _

/-- **`Z₁Z₂` is a self-adjoint involution:** `(Z₁Z₂)² = I`. Verified on the computational basis,
where `Z₁Z₂` acts by the sign `(−1)^{b₁+b₂}`, whose square is `1`. -/
theorem zzI_involution : zzIObservable.op * zzIObservable.op = 1 := by
  apply qubitThree_op_ext
  intro b
  rw [mul_apply_eq_comp, zzI_op_ket, map_smul, zzI_op_ket, smul_smul,
    one_apply_eq_self]
  fin_cases b <;> simp

/-- **`Z₂Z₃` is a self-adjoint involution:** `(Z₂Z₃)² = I`. -/
theorem izz_involution : izzObservable.op * izzObservable.op = 1 := by
  apply qubitThree_op_ext
  intro b
  rw [mul_apply_eq_comp, izz_op_ket, map_smul, izz_op_ket, smul_smul,
    one_apply_eq_self]
  fin_cases b <;> simp

/-- **Measuring `Z₁Z₂`**: the two-outcome projective measurement of the observable `Z₁Z₂`
(outcome `0 ↔ +1`, `1 ↔ −1`). -/
def bitFlipZ12Measurement : Measurement (Fin 2) bitFlipReg :=
  zzIObservable.signMeasurement zzI_involution

/-- **Measuring `Z₂Z₃`**: the two-outcome projective measurement of the observable `Z₂Z₃`. -/
def bitFlipZ23Measurement : Measurement (Fin 2) bitFlipReg :=
  izzObservable.signMeasurement izz_involution

/-! ### The four bit-flip syndrome projectors and their measurement -/

/-- The two computational basis strings supporting each of N&C's four syndrome projectors:
`0 ↦ {000, 111}` (no error), `1 ↦ {100, 011}` (qubit 1), `2 ↦ {010, 101}` (qubit 2),
`3 ↦ {001, 110}` (qubit 3). -/
def bitFlipSyndromeStr : Fin 4 → (Fin 2 × Fin 2 × Fin 2) × (Fin 2 × Fin 2 × Fin 2) :=
  ![((0, 0, 0), (1, 1, 1)), ((1, 0, 0), (0, 1, 1)), ((0, 1, 0), (1, 0, 1)), ((0, 0, 1), (1, 1, 0))]

/-- **The four bit-flip syndrome projectors** of N&C eqns (10.5)–(10.8): `Pᵢ` is the sum of the two
rank-one projectors onto the computational basis states of `bitFlipSyndromeStr i`, e.g.
`P₀ = |000⟩⟨000| + |111⟩⟨111|`. -/
def bitFlipSyndromeProj (i : Fin 4) : bitFlipReg.space →L[ℂ] bitFlipReg.space :=
  rankOne ℂ (qubitThreeBasis (bitFlipSyndromeStr i).1).vec
      (qubitThreeBasis (bitFlipSyndromeStr i).1).vec
    + rankOne ℂ (qubitThreeBasis (bitFlipSyndromeStr i).2).vec
        (qubitThreeBasis (bitFlipSyndromeStr i).2).vec

/-- **The outcome relabeling** of Exercise 10.3: the pair of `±1` measurement outcomes `(s₁, s₂)`
maps to the syndrome label `i ∈ {0,1,2,3}` by N&C's dictionary `(+,+) ↦ 0` (no error),
`(−,+) ↦ 1` (bit flip on qubit 1), `(−,−) ↦ 2` (qubit 2), `(+,−) ↦ 3` (qubit 3). -/
def bitFlipRelabel : Fin 2 × Fin 2 ≃ Fin 4 where
  toFun := fun s => ![![0, 3], ![1, 2]] s.1 s.2
  invFun := fun i => ![(0, 0), (1, 0), (1, 1), (0, 1)] i
  left_inv := by decide
  right_inv := by decide

/-- **The core operator identity of Exercise 10.3.** For every joint outcome `(s₁, s₂)`, the
measurement operator of the cascade "measure `Z₁Z₂` then `Z₂Z₃`" equals the bit-flip syndrome
projector `P_{bitFlipRelabel (s₁,s₂)}`. Proved on the computational basis: the cascade operator is
`P^{Z₂Z₃}_{s₂} P^{Z₁Z₂}_{s₁}`, which acts on `|b⟩` by the product of the two eigenprojector
coefficients `½(1 ± (−1)^{b₁+b₂})·½(1 ± (−1)^{b₂+b₃})`; this is `1` exactly on the two basis
strings of the corresponding syndrome projector and `0` otherwise. -/
theorem cascade_op_eq_syndromeProj (s : Fin 2 × Fin 2) :
    (bitFlipZ12Measurement.cascade bitFlipZ23Measurement).op s
      = bitFlipSyndromeProj (bitFlipRelabel s) := by
  apply qubitThree_op_ext
  intro b
  obtain ⟨s1, s2⟩ := s
  rw [Measurement.cascade_op, ContinuousLinearMap.comp_apply]
  simp only [bitFlipZ12Measurement, bitFlipZ23Measurement]
  fin_cases s1 <;> fin_cases s2 <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Observable.signMeasurement_op_zero,
      Observable.signMeasurement_op_one, Observable.projPlus_apply_smul _ (zzI_op_ket b),
      Observable.projMinus_apply_smul _ (zzI_op_ket b),
      Observable.projPlus_apply_smul _ (izz_op_ket b),
      Observable.projMinus_apply_smul _ (izz_op_ket b), map_smul, smul_smul, bitFlipRelabel,
      Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, bitFlipSyndromeProj,
      bitFlipSyndromeStr, _root_.add_apply, qubitThreeBasis_rankOne_apply] <;>
    fin_cases b <;> norm_num

/-- **Measuring the four bit-flip syndrome projectors** as a single four-outcome projective
measurement (N&C eqns 10.5–10.8). Completeness `∑ᵢ Pᵢ† Pᵢ = 1` is inherited from the cascade
measurement through the operator identity `cascade_op_eq_syndromeProj` and the relabeling
`bitFlipRelabel`. -/
def bitFlipSyndromeMeasurement : Measurement (Fin 4) bitFlipReg where
  op := bitFlipSyndromeProj
  complete := by
    rw [← Equiv.sum_comp bitFlipRelabel (fun i => (adjoint (bitFlipSyndromeProj i)).comp
      (bitFlipSyndromeProj i))]
    simp only [← cascade_op_eq_syndromeProj]
    exact (bitFlipZ12Measurement.cascade bitFlipZ23Measurement).complete

/-- The measurement operator of `bitFlipSyndromeMeasurement` for outcome `i` is the syndrome
projector `bitFlipSyndromeProj i`. -/
@[simp]
theorem bitFlipSyndromeMeasurement_op (i : Fin 4) :
    bitFlipSyndromeMeasurement.op i = bitFlipSyndromeProj i := rfl

end AxQM
