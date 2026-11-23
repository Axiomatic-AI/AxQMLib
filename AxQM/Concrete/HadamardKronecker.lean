/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Hadamard
import AxQM.Concrete.PauliKronecker

/-!
# Concrete: the 4×4 matrices `H ⊗ I` and `I ⊗ H` (Nielsen & Chuang, Exercise 4.16)

This file computes the explicit `4 × 4` matrix representations of the two Kronecker products a
**single Hadamard on one qubit of a two-qubit register** produces — `H ⊗ I` (Hadamard on the
top/first qubit) and `I ⊗ H` (Hadamard on the bottom/second qubit) — and records that each is
unitary. It parallels the Pauli Kronecker products of Exercise 2.27
(`AxQM/Concrete/PauliKronecker.lean`), whose `flattenFin4` re-indexing this file reuses.

## The exercise

N&C, Exercise 4.16 (p. 178) asks for the `4 × 4` unitary matrix, in the computational basis, of the
circuit that applies the Hadamard gate `H` to one qubit of a two-qubit register: first to the top
wire `x₂` (the most significant qubit), then to the bottom wire `x₁`. Applying a single-qubit gate
to one factor of a two-qubit register is the tensor (Kronecker) product of that gate with the
identity on the untouched qubit, so the two answers are `H ⊗ I` and `I ⊗ H`.

## The basis-ordering convention

Mathlib's Kronecker product `A ⊗ₖ B` (`Matrix.kroneckerMap (· * ·)`) is indexed by the *product*
type `Fin 2 × Fin 2`, with `(A ⊗ₖ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ * B i₂ j₂`. To recover the flat
`4 × 4` array N&C writes out, `flattenFin4` (from `Concrete/PauliKronecker.lean`) re-indexes the
product index by `finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4`, `(i, j) ↦ 2 * i + j` — the big-endian
computational-basis order `|00⟩, |01⟩, |10⟩, |11⟩` with the first (top) qubit most significant.

## Contents

* `flattenFin4_hadamardC_kronecker_pauliI` — `H ⊗ I`: the `4 × 4` matrix
  `(1/√2) !![1,0,1,0; 0,1,0,1; 1,0,-1,0; 0,1,0,-1]`, the answer to the first circuit.
* `flattenFin4_pauliI_kronecker_hadamardC` — `I ⊗ H`: the `4 × 4` matrix
  `(1/√2) !![1,1,0,0; 1,-1,0,0; 0,0,1,1; 0,0,1,-1]`, the answer to the second circuit.
* `hadamardC_kronecker_pauliI_mem_unitaryGroup` / `pauliI_kronecker_hadamardC_mem_unitaryGroup` —
  each is **unitary** (N&C's "unitary matrix"): the Kronecker product of two unitaries is unitary
  (`Matrix.kronecker_mem_unitary`), since `H` is unitary (Exercise 2.51,
  `hadamardC_mem_unitaryGroup`) and `I = 1` is unitary.

The complex Hadamard matrix `hadamardC` is from `AxQM.Concrete.Hadamard`; the identity
Pauli `pauliI` (`σ₀ = I = 1`) and the flattening `flattenFin4` are from
`AxQM.Concrete.PauliKronecker` (via `Concrete.PauliOuterProduct`).
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

/-- **Nielsen & Chuang, Exercise 4.16 (first circuit).** The `4 × 4` matrix, in the big-endian
computational basis `00, 01, 10, 11`, of the Hadamard gate applied to the **top (first) qubit** of
a two-qubit register — the Kronecker product `H ⊗ I`:
`(1/√2) !![1,0,1,0; 0,1,0,1; 1,0,-1,0; 0,1,0,-1]`. Each entry is `H(i₁,j₁) · I(i₂,j₂)`. -/
theorem flattenFin4_hadamardC_kronecker_pauliI :
    flattenFin4 (hadamardC ⊗ₖ pauliI) =
      (Real.sqrt 2 : ℂ)⁻¹ • !![1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, 1, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flattenFin4, hadamardC, pauliI, finProdFinEquiv, Fin.divNat, Fin.modNat]

/-- **Nielsen & Chuang, Exercise 4.16 (second circuit).** The `4 × 4` matrix, in the big-endian
computational basis `00, 01, 10, 11`, of the Hadamard gate applied to the **bottom (second) qubit**
of a two-qubit register — the Kronecker product `I ⊗ H`:
`(1/√2) !![1,1,0,0; 1,-1,0,0; 0,0,1,1; 0,0,1,-1]`. Each entry is `I(i₁,j₁) · H(i₂,j₂)`. -/
theorem flattenFin4_pauliI_kronecker_hadamardC :
    flattenFin4 (pauliI ⊗ₖ hadamardC) =
      (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1, 0, 0; 1, -1, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flattenFin4, hadamardC, pauliI, finProdFinEquiv, Fin.divNat, Fin.modNat]

/-- `H ⊗ I` is **unitary** (Nielsen & Chuang's "unitary matrix"): the Kronecker product of two
unitaries is unitary (`Matrix.kronecker_mem_unitary`), and `H` is unitary (Exercise 2.51,
`hadamardC_mem_unitaryGroup`) while `I = 1` is unitary. -/
theorem hadamardC_kronecker_pauliI_mem_unitaryGroup :
    hadamardC ⊗ₖ pauliI ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker_mem_unitary hadamardC_mem_unitaryGroup (by rw [pauliI]; exact one_mem _)

/-- `I ⊗ H` is **unitary** (Nielsen & Chuang's "unitary matrix"): the Kronecker product of two
unitaries is unitary (`Matrix.kronecker_mem_unitary`), and `I = 1` is unitary while `H` is unitary
(Exercise 2.51, `hadamardC_mem_unitaryGroup`). -/
theorem pauliI_kronecker_hadamardC_mem_unitaryGroup :
    pauliI ⊗ₖ hadamardC ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker_mem_unitary (by rw [pauliI]; exact one_mem _) hadamardC_mem_unitaryGroup

end AxQM.Concrete
