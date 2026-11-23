/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SqrtSwapCNOT
import AxQM.Concrete.PauliKronecker

/-!
# Concrete: the CNOT conjugation `U Y₁ U† = Y₁ X₂` (Nielsen & Chuang, Exercise 10.37)

This file computes, at the level of raw `4 × 4` complex matrices, how the two-qubit controlled-NOT
gate `U` conjugates the Pauli operator `Y₁ = Y ⊗ I` (Pauli `Y` on the control qubit). This is
Nielsen & Chuang, *Quantum Computation and Quantum Information*, **Exercise 10.37** (p. 460), part
of the stabilizer-formalism tableau of §10.5.1: one continues the explicit conjugation checks of
Exercise 10.36 (`U X₁ U† = X₁X₂`, `U X₂ U† = X₂`, `U Z₁ U† = Z₁`, `U Z₂ U† = Z₁Z₂`) to the
remaining generator `Y₁`.

The answer is
`U Y₁ U† = Y₁ X₂ = Y ⊗ X`,
consistent with `Y = iXZ`: `Y₁ = i X₁ Z₁ ↦ i (X₁X₂)(Z₁) = i X₁ Z₁ X₂ = Y₁ X₂`, using the
Exercise 10.36 rules `X₁ ↦ X₁X₂` and `Z₁ ↦ Z₁`.

## The gate and the representation

The gate is the concrete two-qubit CNOT `twoQubitCNOT` (control = first qubit, target = second)
from `Concrete/SqrtSwapCNOT.lean`, `|q, r⟩ ↦ |q, r ⊕ q⟩`, a
`Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ` on the two-qubit computational basis. The single-qubit
Pauli operators are the `Concrete` matrices `pauliX`, `pauliY`, `pauliI` (= `1`), and their
two-qubit placements are Kronecker (tensor) products `σ ⊗ₖ τ`
(Mathlib's `Matrix.kroneckerMap (· * ·)`), so `Y₁ = pauliY ⊗ₖ pauliI`, `X₂ = pauliI ⊗ₖ pauliX`,
and `Y ⊗ X = pauliY ⊗ₖ pauliX` — the same `Fin 2 × Fin 2` tensor representation used for the
Pauli Kronecker products of Exercise 2.27 (`Concrete/PauliKronecker.lean`).

That `U` is Hermitian (`U† = U`), an involution (`U² = I`), and unitary — so `U Y₁ U†` is a genuine
gate conjugation and the "`U†`" is again `U` — is recorded by the reusable gate lemmas
`twoQubitCNOT_conjTranspose` / `twoQubitCNOT_mul_self` / `twoQubitCNOT_mem_unitaryGroup`, which live
beside the `twoQubitCNOT` def in `Concrete/SqrtSwapCNOT.lean` (and are the single source from which
the identical `cnotExtraResp` trio of `Concrete/AugmentedOracleConstruction.lean` is now derived).

## Contents

* `pauliY_kron_pauliI_mul_pauliI_kron_pauliX` — `Y₁ X₂ = Y ⊗ X`, i.e.
  `(Y ⊗ I)(I ⊗ X) = Y ⊗ X`, the mixed-product identity that identifies the closed form `Y ⊗ X`
  with the textbook's product form `Y₁ X₂`.
* `twoQubitCNOT_conj_pauliY_kron_pauliI` — the exercise proper:
  `U Y₁ U† = Y ⊗ X`.
* `twoQubitCNOT_conj_pauliY_kron_pauliI_eq_mul` — the same result in Nielsen & Chuang's product
  form `U Y₁ U† = Y₁ X₂`.

Compare the companion Pauli Kronecker computations (Exercise 2.27) and the CNOT gate itself.
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

/-- **`Y₁ X₂ = Y ⊗ X`.** The product of `Y` on the first qubit and `X` on the second qubit is the
single tensor `Y ⊗ X`: `(Y ⊗ I)(I ⊗ X) = (Y·I) ⊗ (I·X) = Y ⊗ X` by the Kronecker mixed-product
rule. This identifies the closed form `Y ⊗ X` of `U Y₁ U†` with Nielsen & Chuang's product answer
`Y₁ X₂`. -/
theorem pauliY_kron_pauliI_mul_pauliI_kron_pauliX :
    (pauliY ⊗ₖ pauliI) * (pauliI ⊗ₖ pauliX) = pauliY ⊗ₖ pauliX := by
  rw [← Matrix.mul_kronecker_mul]
  simp only [pauliI, mul_one, one_mul]

/-- **Nielsen & Chuang, Exercise 10.37:** the CNOT gate `U` (control = first qubit) conjugates
`Y₁ = Y ⊗ I` to `Y ⊗ X`:
`U Y₁ U† = Y ⊗ X`.
Consistent with `Y = iXZ` and the Exercise 10.36 rules (`X₁ ↦ X₁X₂`, `Z₁ ↦ Z₁`):
`Y₁ = i X₁ Z₁ ↦ i (X₁X₂)(Z₁) = i X₁ Z₁ X₂ = Y₁ X₂ = Y ⊗ X`. Proved by the `4 × 4` entrywise
computation, using that `U† = U` (`twoQubitCNOT_conjTranspose`). -/
theorem twoQubitCNOT_conj_pauliY_kron_pauliI :
    twoQubitCNOT * (pauliY ⊗ₖ pauliI) * twoQubitCNOTᴴ = pauliY ⊗ₖ pauliX := by
  rw [twoQubitCNOT_conjTranspose]
  ext i j
  obtain ⟨i1, i2⟩ := i; obtain ⟨j1, j2⟩ := j
  simp only [Matrix.mul_apply, twoQubitCNOT_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, pauliY, pauliI, pauliX]
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp

/-- **Nielsen & Chuang, Exercise 10.37, product form:** `U Y₁ U† = Y₁ X₂`, i.e.
`U (Y ⊗ I) U† = (Y ⊗ I)(I ⊗ X)` — the answer written as the product of the Pauli generators exactly
as in the textbook tableau. Combines the closed form `U Y₁ U† = Y ⊗ X`
(`twoQubitCNOT_conj_pauliY_kron_pauliI`) with `Y₁ X₂ = Y ⊗ X`
(`pauliY_kron_pauliI_mul_pauliI_kron_pauliX`). -/
theorem twoQubitCNOT_conj_pauliY_kron_pauliI_eq_mul :
    twoQubitCNOT * (pauliY ⊗ₖ pauliI) * twoQubitCNOTᴴ
      = (pauliY ⊗ₖ pauliI) * (pauliI ⊗ₖ pauliX) := by
  rw [twoQubitCNOT_conj_pauliY_kron_pauliI, pauliY_kron_pauliI_mul_pauliI_kron_pauliX]

end AxQM.Concrete
