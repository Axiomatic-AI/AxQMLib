/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Sqrt2IntegerMatrix
import AxQM.Concrete.Pauli
import AxQM.Concrete.PauliOuterProduct
import ToMathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Concrete: conjugation of the Pauli matrices by the Toffoli gate (N&C eqs 10.93–10.95)

This file verifies the Toffoli half of
Nielsen & Chuang **Exercise 10.41**, namely equations (10.93)–(10.95) describing the action by
conjugation of the **Toffoli gate** `U` — controls on qubits `1, 2`, target qubit `3` — on the
three-qubit Pauli operators. (The π/8-gate half, eq. (10.92), is in
`Concrete/PiEighthConjugation.lean`.) With `Zₖ`, `Xₖ` the Pauli operators on qubit `k` of the
three-qubit register:

> (10.93)  `U Z₁ U† = Z₁`,   `U X₁ U† = X₁ (I + Z₂ + X₃ − Z₂X₃)/2`;
> (10.94)  `U Z₂ U† = Z₂`,   `U X₂ U† = X₂ (I + Z₁ + X₃ − Z₁X₃)/2`;
> (10.95)  `U X₃ U† = X₃`,   `U Z₃ U† = Z₃ (I + Z₁ + Z₂ − Z₁Z₂)/2`.

Together with the π/8 identities these exhibit the π/8 and Toffoli gates as lying *outside* the
normalizer `N(Gₙ)` of the Pauli group (N&C §10.5.3): unlike Hadamard, phase and CNOT, conjugating a
Pauli operator by `U` need not return a Pauli operator — e.g. `U X₁ U†` is `X₁` times the
controlled-`X` combination `(I + Z₂ + X₃ − Z₂X₃)/2`, not a single Pauli. This is exactly what makes
stabilizer analysis of circuits containing Toffoli gates inconvenient.

Each identity is a fact of `8 × 8` complex linear algebra — an equality of
concrete matrices. The statement of Exercise 10.41 is in `AxQM/NC/Ch10/Exercise10_41.lean`.

## Representation

The Toffoli gate is the reusable `Fin 8` permutation matrix
`AxQM.Concrete.toffoliMatrix` of `Concrete/Sqrt2IntegerMatrix.lean` — the transposition
swapping `|110⟩ ↔ |111⟩` (indices `6 ↔ 7`) in the **big-endian** basis order
`000, …, 111` (`|q₁q₂q₃⟩ ↦ 4q₁ + 2q₂ + q₃`). To match that `Fin 8` indexing, the three-qubit Pauli
operators `Xₖ`, `Zₖ` are the triple Kronecker products `pauliX ⊗ₖ pauliI ⊗ₖ pauliI` etc. of the
single-qubit matrices (`Concrete/Pauli.lean`, `Concrete/PauliOuterProduct.lean`), flattened to
`Fin 8` by `flattenTriQubit` along the same big-endian equiv `triQubitEquiv`.

## What is proved

* `toffoli_conj_apply` — the structural lemma that conjugation by `U` (a real symmetric permutation)
  simply relabels matrix entries by the transposition `swap 6 7`:
  `(U A U†) i j = A (swap 6 7 i) (swap 6 7 j)`. Every identity below reduces to this plus an
  entrywise check.
* `pauliX1_eq, …, pauliZ3_eq` — the six three-qubit Paulis as explicit `8 × 8` matrices (permutation
  matrices for the `Xₖ`, diagonal sign matrices for the `Zₖ`), the closed forms the entrywise
  computations run on.
* `toffoli_conj_pauliZ1, toffoli_conj_pauliZ2, toffoli_conj_pauliX3` — the three fixed generators
  (`U Z₁ U† = Z₁`, `U Z₂ U† = Z₂`, `U X₃ U† = X₃`).
* `toffoli_conj_pauliX1, toffoli_conj_pauliX2, toffoli_conj_pauliZ3` — the three non-Pauli images
  `U X₁ U† = X₁ (I + Z₂ + X₃ − Z₂X₃)/2`, `U X₂ U† = X₂ (I + Z₁ + X₃ − Z₁X₃)/2`,
  `U Z₃ U† = Z₃ (I + Z₁ + Z₂ − Z₁Z₂)/2`, witnessing `U ∉ N(G₃)`.

## Design notes

* We index over `Fin 8` rather than `Fin 2 × Fin 2 × Fin 2` so as to reuse the existing, already
  `√2`-cyclotomic-certified `toffoliMatrix`; the Kronecker definitions keep the operators manifestly
  `X ⊗ I ⊗ I` etc., and the `_eq` lemmas expose the explicit closed forms that make the `8 × 8`
  `fin_cases` computations tractable.
* The `⊗` of N&C (`X₁ ⊗ (…)`) is rendered as the matrix product `pauliX1 * (…)`: `X₁` and the
  bracket have disjoint support, so their product is exactly the tensor N&C writes.
-/

open Matrix Complex
open scoped Kronecker

namespace AxQM.Concrete.ToffoliConj

/-- The big-endian re-indexing `((q₁, q₂), q₃) ↦ 4q₁ + 2q₂ + q₃` of a three-qubit tensor index to
`Fin 8`, i.e. the computational-basis order `|000⟩, …, |111⟩`. It is `finProdFinEquiv` (the
two-qubit flattening `(i, j) ↦ 2i + j`) applied on the first two factors and then again on it, and
matches the big-endian order in which `toffoliMatrix` is written. -/
def triQubitEquiv : (Fin 2 × Fin 2) × Fin 2 ≃ Fin 8 :=
  (finProdFinEquiv.prodCongr (Equiv.refl (Fin 2))).trans finProdFinEquiv

/-- Flatten a `((Fin 2 × Fin 2) × Fin 2)`-indexed matrix (a three-factor tensor/Kronecker product,
associated as `(A ⊗ₖ B) ⊗ₖ C`) to its `8 × 8` representation, ordering the tensor index by the
big-endian equiv `triQubitEquiv`. -/
def flattenTriQubit (M : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ) :
    Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.reindex triQubitEquiv triQubitEquiv M

/-- Conjugation by the Toffoli gate relabels matrix entries by the transposition `swap 6 7`. -/
theorem toffoli_conj_apply (A : Matrix (Fin 8) (Fin 8) ℂ) (i j : Fin 8) :
    (toffoliMatrix * A * toffoliMatrixᴴ) i j = A (Equiv.swap 6 7 i) (Equiv.swap 6 7 j) := by
  have hT : ∀ p q : Fin 8, (toffoliMatrix : Matrix (Fin 8) (Fin 8) ℂ) p q
      = if Equiv.swap 6 7 p = q then 1 else 0 := fun p q => rfl
  have hTH : ∀ p q : Fin 8, (toffoliMatrixᴴ : Matrix (Fin 8) (Fin 8) ℂ) p q
      = if Equiv.swap 6 7 q = p then 1 else 0 := by
    intro p q
    rw [Matrix.conjTranspose_apply, hT]
    simp [apply_ite (starRingEnd ℂ)]
  simp only [Matrix.mul_apply, hT, hTH, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- `X₁ = X ⊗ I ⊗ I`. -/
def pauliX1 : Matrix (Fin 8) (Fin 8) ℂ := flattenTriQubit (pauliX ⊗ₖ pauliI ⊗ₖ pauliI)
/-- `Z₁ = Z ⊗ I ⊗ I`. -/
def pauliZ1 : Matrix (Fin 8) (Fin 8) ℂ := flattenTriQubit (pauliZ ⊗ₖ pauliI ⊗ₖ pauliI)
/-- `X₂ = I ⊗ X ⊗ I`. -/
def pauliX2 : Matrix (Fin 8) (Fin 8) ℂ := flattenTriQubit (pauliI ⊗ₖ pauliX ⊗ₖ pauliI)
/-- `Z₂ = I ⊗ Z ⊗ I`. -/
def pauliZ2 : Matrix (Fin 8) (Fin 8) ℂ := flattenTriQubit (pauliI ⊗ₖ pauliZ ⊗ₖ pauliI)
/-- `X₃ = I ⊗ I ⊗ X`. -/
def pauliX3 : Matrix (Fin 8) (Fin 8) ℂ := flattenTriQubit (pauliI ⊗ₖ pauliI ⊗ₖ pauliX)
/-- `Z₃ = I ⊗ I ⊗ Z`. -/
def pauliZ3 : Matrix (Fin 8) (Fin 8) ℂ := flattenTriQubit (pauliI ⊗ₖ pauliI ⊗ₖ pauliZ)

-- local simp set to compute a flattened triple-Kronecker entry.
attribute [local simp] flattenTriQubit triQubitEquiv finProdFinEquiv Fin.divNat Fin.modNat
  pauliX pauliY pauliZ pauliI

/-- `X₁ = X ⊗ I ⊗ I` as an explicit `8 × 8` matrix: the permutation flipping the top qubit
(`i ↦ i XOR 4`). -/
theorem pauliX1_eq : pauliX1 = !![0,0,0,0,1,0,0,0; 0,0,0,0,0,1,0,0; 0,0,0,0,0,0,1,0;
    0,0,0,0,0,0,0,1; 1,0,0,0,0,0,0,0; 0,1,0,0,0,0,0,0; 0,0,1,0,0,0,0,0; 0,0,0,1,0,0,0,0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX1]

/-- `Z₁ = Z ⊗ I ⊗ I` explicitly: `diag(1,1,1,1,−1,−1,−1,−1)` (sign `(−1)^{q₁}`). -/
theorem pauliZ1_eq : pauliZ1 = Matrix.diagonal ![1,1,1,1,-1,-1,-1,-1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ1, Matrix.diagonal]

/-- `X₂ = I ⊗ X ⊗ I` as an explicit `8 × 8` matrix: the permutation flipping the middle qubit
(`i ↦ i XOR 2`). -/
theorem pauliX2_eq : pauliX2 = !![0,0,1,0,0,0,0,0; 0,0,0,1,0,0,0,0; 1,0,0,0,0,0,0,0;
    0,1,0,0,0,0,0,0; 0,0,0,0,0,0,1,0; 0,0,0,0,0,0,0,1; 0,0,0,0,1,0,0,0; 0,0,0,0,0,1,0,0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX2]

/-- `Z₂ = I ⊗ Z ⊗ I` explicitly: `diag(1,1,−1,−1,1,1,−1,−1)` (sign `(−1)^{q₂}`). -/
theorem pauliZ2_eq : pauliZ2 = Matrix.diagonal ![1,1,-1,-1,1,1,-1,-1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ2, Matrix.diagonal]

/-- `X₃ = I ⊗ I ⊗ X` as an explicit `8 × 8` matrix: the permutation flipping the bottom qubit
(`i ↦ i XOR 1`). -/
theorem pauliX3_eq : pauliX3 = !![0,1,0,0,0,0,0,0; 1,0,0,0,0,0,0,0; 0,0,0,1,0,0,0,0;
    0,0,1,0,0,0,0,0; 0,0,0,0,0,1,0,0; 0,0,0,0,1,0,0,0; 0,0,0,0,0,0,0,1; 0,0,0,0,0,0,1,0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX3]

/-- `Z₃ = I ⊗ I ⊗ Z` explicitly: `diag(1,−1,1,−1,1,−1,1,−1)` (sign `(−1)^{q₃}`). -/
theorem pauliZ3_eq : pauliZ3 = Matrix.diagonal ![1,-1,1,-1,1,-1,1,-1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ3, Matrix.diagonal]

/-- `U Z₁ U† = Z₁` (Nielsen & Chuang, eq. 10.93, first identity). -/
theorem toffoli_conj_pauliZ1 : toffoliMatrix * pauliZ1 * toffoliMatrixᴴ = pauliZ1 := by
  ext i j
  rw [toffoli_conj_apply, pauliZ1_eq]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Equiv.swap_apply_def]

/-- `U Z₂ U† = Z₂` (Nielsen & Chuang, eq. 10.94, first identity). -/
theorem toffoli_conj_pauliZ2 : toffoliMatrix * pauliZ2 * toffoliMatrixᴴ = pauliZ2 := by
  ext i j
  rw [toffoli_conj_apply, pauliZ2_eq]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Equiv.swap_apply_def]

/-- `U X₃ U† = X₃` (Nielsen & Chuang, eq. 10.95, first identity). -/
theorem toffoli_conj_pauliX3 : toffoliMatrix * pauliX3 * toffoliMatrixᴴ = pauliX3 := by
  ext i j
  rw [toffoli_conj_apply, pauliX3_eq]
  fin_cases i <;> fin_cases j <;>
    simp [Equiv.swap_apply_def]

set_option maxHeartbeats 1000000 in
-- entrywise `8 × 8` computation: the `fin_cases`-split conjugation identity unfolds two nested
-- matrix products (`Fin.sum_univ_eight`) across 64 entries, exceeding the default heartbeats.
theorem toffoli_conj_pauliX1 :
    toffoliMatrix * pauliX1 * toffoliMatrixᴴ
      = pauliX1 * ((2 : ℂ)⁻¹ • (1 + pauliZ2 + pauliX3 - pauliZ2 * pauliX3)) := by
  ext i j
  rw [toffoli_conj_apply, pauliX1_eq, pauliZ2_eq, pauliX3_eq]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal, Equiv.swap_apply_def,
      smul_eq_mul] <;> ring

set_option maxHeartbeats 1000000 in
-- entrywise `8 × 8` computation: see `toffoli_conj_pauliX1`.
theorem toffoli_conj_pauliX2 :
    toffoliMatrix * pauliX2 * toffoliMatrixᴴ
      = pauliX2 * ((2 : ℂ)⁻¹ • (1 + pauliZ1 + pauliX3 - pauliZ1 * pauliX3)) := by
  ext i j
  rw [toffoli_conj_apply, pauliX2_eq, pauliZ1_eq, pauliX3_eq]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal, Equiv.swap_apply_def,
      smul_eq_mul] <;> ring

set_option maxHeartbeats 1000000 in
-- entrywise `8 × 8` computation: see `toffoli_conj_pauliX1`.
theorem toffoli_conj_pauliZ3 :
    toffoliMatrix * pauliZ3 * toffoliMatrixᴴ
      = pauliZ3 * ((2 : ℂ)⁻¹ • (1 + pauliZ1 + pauliZ2 - pauliZ1 * pauliZ2)) := by
  ext i j
  rw [toffoli_conj_apply, pauliZ3_eq, pauliZ1_eq, pauliZ2_eq]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal, Equiv.swap_apply_def,
      smul_eq_mul] <;> ring

end AxQM.Concrete.ToffoliConj
