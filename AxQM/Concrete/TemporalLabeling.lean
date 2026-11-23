/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Sqrt2IntegerMatrix
import AxQM.Concrete.ModularMultiplication
import Mathlib.Data.Matrix.PEquiv
import ToMathlib.LinearAlgebra.Matrix.Permutation

/-!
# Temporal labeling: the population-permutation circuit (Nielsen & Chuang, Exercise 7.42)

*Temporal labeling* (§7.7.1, p. 333) prepares an *effective* pure state on an NMR ensemble by
summing the traceless observables of three experiments run on permuted copies of the thermal state.
The two permutations are performed by a small circuit `P` of controlled-NOT gates. Starting from the
diagonal two-spin density matrix (N&C 7.153)

`ρ₁ = diag(a, b, c, d)`

on the big-endian computational basis `|00⟩, |01⟩, |10⟩, |11⟩` (indices `0,1,2,3`), the circuit `P`
cyclically permutes the last three populations, and its adjoint `P†` runs the cycle backwards:

`ρ₂ = P ρ₁ P† = diag(a, c, d, b)`  (7.154),   `ρ₃ = P† ρ₁ P = diag(a, d, b, c)`  (7.155).

**Exercise 7.42** asks for a quantum circuit realizing `P` and `P†`.

## The circuit

The required map on the computational basis fixes `|00⟩` and 3-cycles the rest,
`|01⟩ ↦ |11⟩ ↦ |10⟩ ↦ |01⟩`. Two controlled-NOTs suffice:

`P = CNOT(control = 2nd qubit) · CNOT(control = 1st qubit)`,

i.e. apply `CNOT` with the first qubit controlling the second (`cnotMatrix`, the basis transposition
`|10⟩ ↔ |11⟩`), then `CNOT` with the second qubit controlling the first
(`cnotSecondControlMatrix`, the basis transposition `|01⟩ ↔ |11⟩`). The product is the permutation
matrix of the 3-cycle, and conjugation of a diagonal matrix by a permutation matrix simply permutes
the diagonal — which is exactly the population shuffle (7.154)/(7.155).

## Formalisation

The whole exercise is a computation about explicit `4 × 4` complex matrices — the `CNOT` matrices, a
diagonal density matrix, and a permutation. The statement of the exercise is in
`AxQM/NC/Ch7/Exercise7_42.lean`. The single genuinely general
fact used, `Matrix.permMatrix_mul_diagonal_mul_conjTranspose` (a permutation matrix conjugates a
diagonal matrix by permuting its diagonal), is in
`ToMathlib/LinearAlgebra/Matrix/PermutationUnitary.lean` (alongside
`Matrix.permMatrix_mem_unitaryGroup`), and is imported here.

## Fidelity

N&C's `ρ₁` has `a, b, c, d` positive reals summing to `1` (a probability distribution). The
statements here quantify over **arbitrary** complex `a, b, c, d`: the permutation identity holds
regardless of positivity or normalisation, so this is a faithful strengthening of the textbook
claim, not a weakening. Both `P` (giving `ρ₂`, 7.154) and `P†` (giving `ρ₃`, 7.155) are recorded, as
the exercise asks, and `P` is certified unitary (`temporalLabelCircuit_mem_unitaryGroup`) so it is a
genuine quantum circuit.
-/

namespace AxQM.Concrete

open Matrix

/-- **`ρ₁` of N&C (7.153)**: the diagonal two-spin density matrix with populations `(a, b, c, d)` on
the big-endian computational basis `|00⟩, |01⟩, |10⟩, |11⟩`. -/
noncomputable def temporalLabelRho1 (a b c d : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![a, b, c, d]

/-- **`ρ₂` of N&C (7.154)**: the populations cyclically permuted to `(a, c, d, b)`, the state
`P ρ₁ P†` obtained by the temporal-labeling circuit. -/
noncomputable def temporalLabelRho2 (a b c d : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![a, c, d, b]

/-- **`ρ₃` of N&C (7.155)**: the populations cyclically permuted to `(a, d, b, c)`, the state
`P† ρ₁ P` obtained by the inverse circuit. -/
noncomputable def temporalLabelRho3 (a b c d : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![a, d, b, c]

/-- The **`CNOT` gate matrix with the second qubit as control** (target = first qubit): the basis
permutation swapping `|01⟩ ↔ |11⟩` (indices `1 ↔ 3` in big-endian order), i.e.
`|q₀ q₁⟩ ↦ |q₀ ⊕ q₁, q₁⟩`. This is the mirror image of the library's `cnotMatrix` (control = first
qubit, `|10⟩ ↔ |11⟩`). -/
noncomputable def cnotSecondControlMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => if Equiv.swap 1 3 i = j then 1 else 0

/-- The **temporal-labeling permutation circuit `P`** (N&C, Exercise 7.42): first `CNOT` with the
first qubit controlling (`cnotMatrix`), then `CNOT` with the second qubit controlling
(`cnotSecondControlMatrix`). As a matrix product the later gate is on the left. -/
noncomputable def temporalLabelCircuit : Matrix (Fin 4) (Fin 4) ℂ :=
  cnotSecondControlMatrix * cnotMatrix

/-- The permutation of the computational basis realized by `temporalLabelCircuit`: the 3-cycle
`|01⟩ ↦ |11⟩ ↦ |10⟩ ↦ |01⟩` fixing `|00⟩` (as a function, `0 ↦ 0, 1 ↦ 2, 2 ↦ 3, 3 ↦ 1`). -/
def temporalLabelPerm : Equiv.Perm (Fin 4) := Equiv.swap 2 3 * Equiv.swap 1 3

/-- The library `CNOT` matrix (control = first qubit) is the permutation matrix of the transposition
`(2 3)`. -/
theorem cnotMatrix_eq_permMatrix : cnotMatrix = (Equiv.swap (2 : Fin 4) 3).permMatrix ℂ :=
  permMatrix_eq_of_ite _

/-- The second-control `CNOT` matrix is the permutation matrix of the transposition `(1 3)`. -/
theorem cnotSecondControlMatrix_eq_permMatrix :
    cnotSecondControlMatrix = (Equiv.swap (1 : Fin 4) 3).permMatrix ℂ :=
  permMatrix_eq_of_ite _

/-- The circuit `P` is the permutation matrix of the 3-cycle `temporalLabelPerm`; this is where the
two-`CNOT` product is identified with a single permutation (via anti-multiplicativity of
`permMatrix`). -/
theorem temporalLabelCircuit_eq_permMatrix :
    temporalLabelCircuit = temporalLabelPerm.permMatrix ℂ := by
  rw [temporalLabelCircuit, cnotMatrix_eq_permMatrix, cnotSecondControlMatrix_eq_permMatrix,
    ← Matrix.permMatrix_mul]
  rfl

/-- The temporal-labeling circuit `P` is unitary — a genuine quantum operation — because it is a
permutation matrix. -/
theorem temporalLabelCircuit_mem_unitaryGroup :
    temporalLabelCircuit ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [temporalLabelCircuit_eq_permMatrix]
  exact permMatrix_mem_unitaryGroup temporalLabelPerm

/-- **Exercise 7.42, the permutation `P` (N&C 7.154):** `P ρ₁ P† = ρ₂`, i.e. the circuit conjugation
sends the populations `(a, b, c, d)` to `(a, c, d, b)`. -/
theorem temporalLabelCircuit_conj_temporalLabelRho1 (a b c d : ℂ) :
    temporalLabelCircuit * temporalLabelRho1 a b c d * temporalLabelCircuitᴴ
      = temporalLabelRho2 a b c d := by
  rw [temporalLabelCircuit_eq_permMatrix, temporalLabelRho1,
    permMatrix_mul_diagonal_mul_conjTranspose, temporalLabelRho2]
  congr 1
  funext i; fin_cases i <;> rfl

/-- **Exercise 7.42, the adjoint permutation `P†` (N&C 7.155):** `P† ρ₁ P = ρ₃`, i.e. the inverse
circuit sends the populations `(a, b, c, d)` to `(a, d, b, c)`. -/
theorem temporalLabelCircuit_conjTranspose_conj_temporalLabelRho1 (a b c d : ℂ) :
    temporalLabelCircuitᴴ * temporalLabelRho1 a b c d * temporalLabelCircuit
      = temporalLabelRho3 a b c d := by
  rw [temporalLabelCircuit_eq_permMatrix, temporalLabelRho1, Matrix.conjTranspose_permMatrix]
  have h := permMatrix_mul_diagonal_mul_conjTranspose temporalLabelPerm⁻¹ ![a, b, c, d]
  rw [Matrix.conjTranspose_permMatrix, inv_inv] at h
  rw [h, temporalLabelRho3]
  congr 1
  funext i; fin_cases i <;> rfl

end AxQM.Concrete
