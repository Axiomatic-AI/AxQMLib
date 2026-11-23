/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.Matrix.Kronecker
import AxQM.Concrete.PauliOuterProduct

/-!
# Concrete: Kronecker products of the Pauli matrices (Nielsen & Chuang, Exercise 2.27)

This file computes the explicit
`4 × 4` matrix representations of a few tensor products of Pauli matrices and shows that
the tensor (Kronecker) product is not commutative.

N&C, Exercise 2.27 (p. 74) asks to calculate the matrix representation of the tensor
products of the Pauli operators (a) `X` and `Z`; (b) `I` and `X`; (c) `X` and `I`, and
then asks whether the tensor product is commutative.

## The `4 × 4` representation and the basis-ordering convention

Mathlib's Kronecker product `A ⊗ₖ B` (`Matrix.kroneckerMap (· * ·)`) is indexed by the
*product* type `Fin 2 × Fin 2`, with `(A ⊗ₖ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ * B i₂ j₂`.
To recover the flat `4 × 4` array N&C writes out, `flattenFin4` re-indexes the product
index by `finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4`, `(i, j) ↦ 2 * i + j` — exactly the
computational-basis order `|00⟩, |01⟩, |10⟩, |11⟩` used throughout Chapter 2.

## Contents

* `flattenFin4` — the reusable `Fin 2 × Fin 2 → Fin 4` re-indexing of a two-factor tensor
  product to its flat `4 × 4` matrix.
* `flattenFin4_pauliX_kronecker_pauliZ`, `flattenFin4_pauliI_kronecker_pauliX`,
  `flattenFin4_pauliX_kronecker_pauliI` — parts (a), (b), (c): the explicit `4 × 4`
  matrices.
* `flattenFin4_pauliZ_kronecker_pauliI`, `flattenFin4_pauliI_kronecker_pauliZ` — the two
  `Z`-factor explicit forms `Z ⊗ I` and `I ⊗ Z`, in the same family (reused by the two-qubit
  CNOT/Clifford Pauli-conjugation items, e.g. N&C Ex. 10.36/10.39).
* `pauliI_kronecker_pauliX_ne_pauliX_kronecker_pauliI` — the tensor product is **not**
  commutative: `I ⊗ X ≠ X ⊗ I`. This is the final question of the exercise, and its
  witnesses are precisely parts (b) and (c), which are different matrices.

The Pauli matrices `pauliX`, `pauliZ` are from `AxQM.Concrete.Pauli`; the identity
`pauliI` (`σ₀ = I`) is from `AxQM.Concrete.PauliOuterProduct`.
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

/-- Flatten a `Fin 2 × Fin 2`-indexed matrix (a two-factor tensor product) to its `4 × 4`
matrix representation, ordering the product index by
`finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4`, `(i, j) ↦ 2 * i + j` — i.e. the
computational-basis order `|00⟩, |01⟩, |10⟩, |11⟩`. -/
def flattenFin4 (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv M

/-- Matrix representation of `X ⊗ Z` (Nielsen & Chuang, Exercise 2.27(a)). -/
theorem flattenFin4_pauliX_kronecker_pauliZ :
    flattenFin4 (pauliX ⊗ₖ pauliZ) =
      !![0, 0, 1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, -1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flattenFin4, pauliX, pauliZ, finProdFinEquiv, Fin.divNat, Fin.modNat]

/-- Matrix representation of `I ⊗ X` (Nielsen & Chuang, Exercise 2.27(b)). -/
theorem flattenFin4_pauliI_kronecker_pauliX :
    flattenFin4 (pauliI ⊗ₖ pauliX) =
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flattenFin4, pauliI, pauliX, finProdFinEquiv, Fin.divNat, Fin.modNat]

/-- Matrix representation of `X ⊗ I` (Nielsen & Chuang, Exercise 2.27(c)). -/
theorem flattenFin4_pauliX_kronecker_pauliI :
    flattenFin4 (pauliX ⊗ₖ pauliI) =
      !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flattenFin4, pauliI, pauliX, finProdFinEquiv, Fin.divNat, Fin.modNat]

/-- Matrix representation of `Z ⊗ I` (the `Z`-factor companion of the parts (b), (c) above). -/
theorem flattenFin4_pauliZ_kronecker_pauliI :
    flattenFin4 (pauliZ ⊗ₖ pauliI) =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flattenFin4, pauliI, pauliZ, finProdFinEquiv, Fin.divNat, Fin.modNat]

/-- Matrix representation of `I ⊗ Z` (the `Z`-factor companion of the parts (b), (c) above). -/
theorem flattenFin4_pauliI_kronecker_pauliZ :
    flattenFin4 (pauliI ⊗ₖ pauliZ) =
      !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flattenFin4, pauliI, pauliZ, finProdFinEquiv, Fin.divNat, Fin.modNat]

/-- The tensor (Kronecker) product is **not** commutative: `I ⊗ X ≠ X ⊗ I`. This answers the
final question of Nielsen & Chuang, Exercise 2.27; the two sides are exactly parts (b) and
(c), which have different matrix representations — they already differ in the `(|00⟩, |01⟩)`
entry, `1` versus `0`. -/
theorem pauliI_kronecker_pauliX_ne_pauliX_kronecker_pauliI :
    pauliI ⊗ₖ pauliX ≠ pauliX ⊗ₖ pauliI := by
  intro h
  simpa [pauliX, pauliI] using congr_fun (congr_fun h (0, 0)) (0, 1)

end AxQM.Concrete
