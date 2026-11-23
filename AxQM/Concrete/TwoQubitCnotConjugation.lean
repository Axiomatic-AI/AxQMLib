/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliKronecker
import AxQM.Concrete.Sqrt2IntegerMatrix

/-!
# Concrete: explicit CNOT conjugation of the two-qubit Pauli generators (N&C Ex. 10.36)

This file carries out the **explicit**
matrix verification of Nielsen & Chuang, Exercise 10.36 (p. 460), namely how the two-qubit
controlled-NOT gate `U = CNOT` (control = qubit 1, target = qubit 2) conjugates the four Pauli
generators of the two-qubit Pauli group. It works with the concrete
`4 × 4` matrices `pauliX`, `pauliZ`, `pauliI` and `cnotMatrix`. Compare the
single-qubit Hadamard/phase conjugations of `Concrete/HadamardPauliConjugation.lean` and the
two-qubit angular-momentum relations of `Concrete/TotalAngularMomentumTwoQubit.lean` (Ex. 7.25).

## The exercise

Writing `X₁ = X ⊗ I`, `X₂ = I ⊗ X`, `Z₁ = Z ⊗ I`, `Z₂ = I ⊗ Z` for the single-Pauli operators
acting on qubit `1` (the control) or qubit `2` (the target) of a two-qubit register, Exercise 10.36
asks to verify the four conjugation relations (Nielsen & Chuang, and summarized in Figure 10.7):

`U X₁ U† = X₁X₂,   U X₂ U† = X₂,   U Z₁ U† = Z₁,   U Z₂ U† = Z₁Z₂`.

Physically: an `X` on the control propagates to the target (`X₁ ↦ X₁X₂`), an `X` on the target is
unchanged, a `Z` on the control is unchanged, and a `Z` on the target propagates to the control
(`Z₂ ↦ Z₁Z₂`). These four facts generate the CNOT action on the whole two-qubit Pauli group, which
is why N&C singles them out.

## Index convention

The two-qubit space is `Fin 4` in big-endian computational-basis order `|00⟩, |01⟩, |10⟩, |11⟩`,
with qubit `1` (the control) the **high** bit. The tensor product `A ⊗ B` is realized as
`flattenFin4 (A ⊗ₖ B)` (`Concrete/PauliKronecker.lean`), the Kronecker product reindexed by
`finProdFinEquiv (i, j) = 2 i + j`. In this order the CNOT gate `cnotMatrix`
(`Concrete/Sqrt2IntegerMatrix.lean`, control = first qubit) is the basis permutation `|10⟩ ↔ |11⟩`,
i.e. it flips qubit `2` exactly when qubit `1` is set, matching the operator convention above. The
adjoint `U†` is the conjugate transpose `cnotMatrixᴴ`; since `cnotMatrix` is a real symmetric
permutation matrix, `cnotMatrixᴴ = cnotMatrix` (`cnotMatrix_conjTranspose`).

## Contents

* `pauliX1`, `pauliX2`, `pauliZ1`, `pauliZ2` — the two-qubit generators `X ⊗ I`, `I ⊗ X`, `Z ⊗ I`,
  `I ⊗ Z` as `4 × 4` matrices, defined via `flattenFin4`.
* `pauliX1_eq`, `pauliX2_eq`, `pauliZ1_eq`, `pauliZ2_eq` — their explicit `4 × 4` matrix forms,
  each a direct citation of the corresponding `flattenFin4_pauli…_kronecker_pauli…` computation
  reused from `Concrete/PauliKronecker.lean` (N&C Ex. 2.27's Kronecker forms), not re-proved here.
* `cnotMatrix_conjTranspose` — `cnotMatrixᴴ = cnotMatrix` (the gate is Hermitian), and
  `cnotMatrix_eq` — its explicit `4 × 4` matrix form.
* `cnotMatrix_conj_pauliX1`, `cnotMatrix_conj_pauliX2`, `cnotMatrix_conj_pauliZ1`,
  `cnotMatrix_conj_pauliZ2` — **Exercise 10.36**: the four conjugation identities
  `U X₁ U† = X₁X₂`, `U X₂ U† = X₂`, `U Z₁ U† = Z₁`, `U Z₂ U† = Z₁Z₂`, where the right-hand
  products `X₁X₂` and `Z₁Z₂` are the literal matrix products `pauliX1 * pauliX2` and
  `pauliZ1 * pauliZ2` (`pauliX2`, `pauliZ1` on the two "trivial" cases).

## Proof strategy

Each Pauli operator's explicit `4 × 4` form is reused verbatim from `Concrete/PauliKronecker.lean`
(the `flattenFin4_pauli…_kronecker_pauli…` family), so `pauliX1_eq`, …, `pauliZ2_eq` are one-line
citations rather than re-proofs; only `cnotMatrix_eq` and `cnotMatrix_conjTranspose` are the finite
`Fin 4²` checks unfolding the permutation. The four conjugation identities then reduce, after
rewriting to those explicit forms and using `cnotMatrix_conjTranspose` for the adjoint, to entrywise
matrix-product computations over `Fin 4` (`Matrix.mul_apply`, `Fin.sum_univ_four`) — the direct
"explicit verification" the exercise asks for.
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

/-- The two-qubit generator `X₁ = X ⊗ I` (Pauli `X` on the control qubit), as the `4 × 4` matrix
`flattenFin4 (X ⊗ₖ I)` in big-endian computational-basis order. -/
noncomputable def pauliX1 : Matrix (Fin 4) (Fin 4) ℂ := flattenFin4 (pauliX ⊗ₖ pauliI)

/-- The two-qubit generator `X₂ = I ⊗ X` (Pauli `X` on the target qubit), as the `4 × 4` matrix
`flattenFin4 (I ⊗ₖ X)` in big-endian computational-basis order. -/
noncomputable def pauliX2 : Matrix (Fin 4) (Fin 4) ℂ := flattenFin4 (pauliI ⊗ₖ pauliX)

/-- The two-qubit generator `Z₁ = Z ⊗ I` (Pauli `Z` on the control qubit), as the `4 × 4` matrix
`flattenFin4 (Z ⊗ₖ I)` in big-endian computational-basis order. -/
noncomputable def pauliZ1 : Matrix (Fin 4) (Fin 4) ℂ := flattenFin4 (pauliZ ⊗ₖ pauliI)

/-- The two-qubit generator `Z₂ = I ⊗ Z` (Pauli `Z` on the target qubit), as the `4 × 4` matrix
`flattenFin4 (I ⊗ₖ Z)` in big-endian computational-basis order. -/
noncomputable def pauliZ2 : Matrix (Fin 4) (Fin 4) ℂ := flattenFin4 (pauliI ⊗ₖ pauliZ)

/-- Explicit `4 × 4` matrix form of `X₁ = X ⊗ I` (the imported N&C Ex. 2.27(c) computation). -/
theorem pauliX1_eq : pauliX1 = !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0] :=
  flattenFin4_pauliX_kronecker_pauliI

/-- Explicit `4 × 4` matrix form of `X₂ = I ⊗ X` (the imported N&C Ex. 2.27(b) computation). -/
theorem pauliX2_eq : pauliX2 = !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] :=
  flattenFin4_pauliI_kronecker_pauliX

/-- Explicit `4 × 4` matrix form of `Z₁ = Z ⊗ I` (the imported Kronecker computation). -/
theorem pauliZ1_eq : pauliZ1 = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] :=
  flattenFin4_pauliZ_kronecker_pauliI

/-- Explicit `4 × 4` matrix form of `Z₂ = I ⊗ Z` (the imported Kronecker computation). -/
theorem pauliZ2_eq : pauliZ2 = !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1] :=
  flattenFin4_pauliI_kronecker_pauliZ

/-- The CNOT gate is Hermitian: `cnotMatrixᴴ = cnotMatrix`. It is a real symmetric permutation
matrix (the transposition `|10⟩ ↔ |11⟩`), so its conjugate transpose equals itself — hence the
adjoint `U†` in the conjugation relations is `cnotMatrix` again. -/
theorem cnotMatrix_conjTranspose : cnotMatrixᴴ = cnotMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cnotMatrix, Matrix.conjTranspose_apply, Equiv.swap_apply_def]

/-- Explicit `4 × 4` matrix form of the CNOT gate `cnotMatrix` (control = qubit 1): the basis
permutation `|10⟩ ↔ |11⟩`. -/
theorem cnotMatrix_eq : cnotMatrix = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cnotMatrix, Equiv.swap_apply_def]

/-- **Exercise 10.36** (first relation): CNOT conjugates `X` on the control into `X` on both wires,
`U X₁ U† = X₁X₂`. -/
theorem cnotMatrix_conj_pauliX1 :
    cnotMatrix * pauliX1 * cnotMatrixᴴ = pauliX1 * pauliX2 := by
  rw [cnotMatrix_conjTranspose, pauliX1_eq, pauliX2_eq, cnotMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

/-- **Exercise 10.36** (second relation): CNOT leaves target `X` unchanged: `U X₂ U† = X₂`. -/
theorem cnotMatrix_conj_pauliX2 :
    cnotMatrix * pauliX2 * cnotMatrixᴴ = pauliX2 := by
  rw [cnotMatrix_conjTranspose, pauliX2_eq, cnotMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

/-- **Exercise 10.36** (third relation): CNOT leaves control `Z` unchanged: `U Z₁ U† = Z₁`. -/
theorem cnotMatrix_conj_pauliZ1 :
    cnotMatrix * pauliZ1 * cnotMatrixᴴ = pauliZ1 := by
  rw [cnotMatrix_conjTranspose, pauliZ1_eq, cnotMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

/-- **Exercise 10.36** (fourth relation): CNOT conjugates `Z` on the target into `Z` on both wires,
`U Z₂ U† = Z₁Z₂`. -/
theorem cnotMatrix_conj_pauliZ2 :
    cnotMatrix * pauliZ2 * cnotMatrixᴴ = pauliZ1 * pauliZ2 := by
  rw [cnotMatrix_conjTranspose, pauliZ1_eq, pauliZ2_eq, cnotMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

end AxQM.Concrete
