/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliKronecker
import AxQM.Concrete.PauliEigenvectors

/-!
# Concrete: total angular momentum of two spin-½ particles (Nielsen & Chuang, Exercise 7.26)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 7.26 (p. 314)
asks to **verify the properties of the coupled states `|j, m_j⟩_J`** — that they are
simultaneous eigenstates of `J²` and `j_z` — by explicitly writing the `4 × 4` matrices
`J²` and `j_z` in the basis they define.

The two spin-½ particles live in `ℂ² ⊗ ℂ² ≅ ℂ⁴` (the computational basis
`|00⟩, |01⟩, |10⟩, |11⟩`, indexed by `Fin 4` via `2·i + j`, matching `flattenFin4`). The
**total angular-momentum operators** are the symmetric sums of the single-particle Pauli
operators (N&C, unnumbered equation before (7.97)):

`j_x = (X₁ + X₂)/2`, `j_y = (Y₁ + Y₂)/2`, `j_z = (Z₁ + Z₂)/2`, `J² = j_x² + j_y² + j_z²`,

where `A₁ = A ⊗ I` and `A₂ = I ⊗ A`. The **coupled basis** (N&C (7.93)–(7.96)) is

* `|0,0⟩_J = (|01⟩ − |10⟩)/√2` — the spin *singlet* (`j = 0`);
* `|1,−1⟩_J = |00⟩`, `|1,0⟩_J = (|01⟩ + |10⟩)/√2`, `|1,1⟩_J = |11⟩` — the spin *triplet*
  (`j = 1`).

## Contents

* `totalJx`, `totalJy`, `totalJz`, `totalJSq` — the four operators as `4 × 4` matrices,
  built from the Pauli matrices by Kronecker product, with their explicit matrix forms
  `totalJx_eq`, `totalJy_eq`, `totalJz_eq`, and `totalJSq_eq`. In particular
  `totalJz = diag(1, 0, 0, −1)` and
  `totalJSq = !![2,0,0,0; 0,1,1,0; 0,1,1,0; 0,0,0,2]` — the two matrices the exercise asks
  us to write out.
* `coupledSinglet`, `coupledTripletPlus`, `coupledTripletZero`, `coupledTripletMinus` — the
  four coupled-basis vectors.
* `..._mulVec_...` (eight theorems) — the **properties to verify**: each coupled state is an
  eigenvector of `J²` with eigenvalue `j(j+1)` (`0` for the singlet, `2` for the triplet)
  and simultaneously of `j_z` with its `j_z`-eigenvalue. Column by column these say exactly
  that `J²` and `j_z` are **diagonal in the coupled basis** with entries `(0,2,2,2)` and
  `(0,1,0,−1)`.
* `coupledBasis` and `coupledBasis_conjTranspose_mul_self` — the change-of-basis matrix `U`
  (its columns are the four states, in N&C's order `|0,0⟩, |1,−1⟩, |1,0⟩, |1,1⟩`) is
  unitary, `Uᴴ U = I`; i.e. the four states form an **orthonormal basis**.

Compare `Concrete.Pauli`, `Concrete.PauliEigenvectors` and `Concrete.PauliKronecker`.

## The `j_z` sign convention

N&C use the standard Pauli `Z = diag(1, −1)` (`Z|0⟩ = |0⟩`, `Z|1⟩ = −|1⟩`), so
`j_z = (Z₁ + Z₂)/2` sends `|00⟩ ↦ +|00⟩` and `|11⟩ ↦ −|11⟩`. The eigenvalues computed here
are therefore `+1` for `|00⟩` and `−1` for `|11⟩` — the **opposite sign** to the `m_j` labels
`|1,−1⟩_J = |00⟩`, `|1,1⟩_J = |11⟩` written in (7.94), (7.96). This is a spin-orientation
convention (which extremal state is called `m_j = +1`); the states are named here by their
*actual* `j_z`-eigenvalue (`…Plus` for `+1`, `…Minus` for `−1`). The convention-independent
physical content the exercise verifies — that the four states are **simultaneous eigenstates**
of `J²` and `j_z`, with `J²`-eigenvalue `j(j+1) ∈ {0, 2}` and `|j_z|`-eigenvalue `|m_j| ∈ {0, 1}`
— holds exactly. (Adopting `j_z = (Z₁ + Z₂)/2` with the opposite spin labelling `|0⟩ ↦` "down"
recovers N&C's `m_j` signs verbatim.)

## Design notes

Following `Concrete.Pauli`/`Concrete.PauliEigenvectors`, the whole exercise stays at the raw
matrix level: operators are `Matrix (Fin 4) (Fin 4) ℂ`, states are column vectors
`Fin 4 → ℂ`, a matrix acts by `Matrix.mulVec` (`M *ᵥ v`), each eigenvalue equation is
`M *ᵥ v = μ • v` with `μ` explicit, and the Hermitian inner product is `star u ⬝ᵥ v`
(`Matrix.dotProduct` of the conjugate, N&C eq. (2.14)). The `4 × 4` Kronecker products reuse
`flattenFin4` from `Concrete.PauliKronecker`, and the `1/√2` amplitude reuses `invSqrt2` from
`Concrete.PauliEigenvectors`. Every fact reduces to an entrywise computation.
-/

namespace AxQM.Concrete

open Matrix Complex
open scoped Kronecker

/-! ### The total angular-momentum operators -/

/-- The total angular-momentum `x`-operator `j_x = (X ⊗ I + I ⊗ X)/2` of two spin-½ particles,
as a `4 × 4` matrix in the computational basis `|00⟩, |01⟩, |10⟩, |11⟩`. -/
noncomputable def totalJx : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • flattenFin4 (pauliX ⊗ₖ pauliI + pauliI ⊗ₖ pauliX)

/-- The total angular-momentum `y`-operator `j_y = (Y ⊗ I + I ⊗ Y)/2`. -/
noncomputable def totalJy : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • flattenFin4 (pauliY ⊗ₖ pauliI + pauliI ⊗ₖ pauliY)

/-- The total angular-momentum `z`-operator `j_z = (Z ⊗ I + I ⊗ Z)/2`. -/
noncomputable def totalJz : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • flattenFin4 (pauliZ ⊗ₖ pauliI + pauliI ⊗ₖ pauliZ)

/-- The total angular-momentum-squared operator `J² = j_x² + j_y² + j_z²` (N&C (7.97)). -/
noncomputable def totalJSq : Matrix (Fin 4) (Fin 4) ℂ :=
  totalJx * totalJx + totalJy * totalJy + totalJz * totalJz

/-- The explicit matrix of `j_x = (X₁ + X₂)/2`. -/
theorem totalJx_eq :
    totalJx = !![0, 2⁻¹, 2⁻¹, 0; 2⁻¹, 0, 0, 2⁻¹; 2⁻¹, 0, 0, 2⁻¹; 0, 2⁻¹, 2⁻¹, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [totalJx, flattenFin4, pauliX, pauliI, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Matrix.add_apply]

/-- The explicit matrix of `j_y = (Y₁ + Y₂)/2`. -/
theorem totalJy_eq :
    totalJy = !![0, -(I / 2), -(I / 2), 0; I / 2, 0, 0, -(I / 2);
                 I / 2, 0, 0, -(I / 2); 0, I / 2, I / 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [totalJy, flattenFin4, pauliY, pauliI, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Matrix.add_apply] <;>
    ring

/-- The explicit matrix of `j_z = (Z₁ + Z₂)/2`: the diagonal matrix `diag(1, 0, 0, −1)`. This is
one of the two matrices Nielsen & Chuang, Exercise 7.26 asks us to write out. -/
theorem totalJz_eq :
    totalJz = !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [totalJz, flattenFin4, pauliZ, pauliI, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Matrix.add_apply] <;>
    norm_num

/-- The explicit matrix of `J² = j_x² + j_y² + j_z²`:
`!![2,0,0,0; 0,1,1,0; 0,1,1,0; 0,0,0,2]`. This is the second matrix Nielsen & Chuang,
Exercise 7.26 asks us to write out; it is block-diagonal (not diagonal) in the computational
basis, and its off-diagonal `1`s in the `|01⟩, |10⟩` block are exactly what the coupled basis
diagonalizes. -/
theorem totalJSq_eq :
    totalJSq = !![2, 0, 0, 0; 0, 1, 1, 0; 0, 1, 1, 0; 0, 0, 0, 2] := by
  rw [totalJSq, totalJx_eq, totalJy_eq, totalJz_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply] <;>
    ring_nf <;>
    simp [Complex.I_sq] <;>
    ring

/-! ### The coupled basis states -/

/-- The spin **singlet** `|0,0⟩_J = (|01⟩ − |10⟩)/√2` (N&C (7.93)); total angular momentum
`j = 0`, `m_j = 0`. -/
noncomputable def coupledSinglet : Fin 4 → ℂ := ![0, invSqrt2, -invSqrt2, 0]

/-- The triplet state `|00⟩` (N&C (7.94), labelled `|1,−1⟩_J`); `j = 1`, and a `j_z`-eigenstate
with eigenvalue `+1` under the standard `Z = diag(1,−1)` convention (see the module docstring). -/
noncomputable def coupledTripletPlus : Fin 4 → ℂ := ![1, 0, 0, 0]

/-- The triplet state `|1,0⟩_J = (|01⟩ + |10⟩)/√2` (N&C (7.95)); `j = 1`, `m_j = 0`. -/
noncomputable def coupledTripletZero : Fin 4 → ℂ := ![0, invSqrt2, invSqrt2, 0]

/-- The triplet state `|11⟩` (N&C (7.96), labelled `|1,1⟩_J`); `j = 1`, and a `j_z`-eigenstate
with eigenvalue `−1` under the standard `Z = diag(1,−1)` convention (see the module docstring). -/
noncomputable def coupledTripletMinus : Fin 4 → ℂ := ![0, 0, 0, 1]

/-! ### `j_z` eigenvalues: each coupled state is a `j_z`-eigenstate with eigenvalue `m_j` -/

/-- `j_z |0,0⟩_J = 0`: the singlet has `m_j = 0`. -/
theorem totalJz_mulVec_coupledSinglet :
    totalJz *ᵥ coupledSinglet = (0 : ℂ) • coupledSinglet := by
  rw [totalJz_eq]
  ext i
  fin_cases i <;>
    simp [coupledSinglet, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- `j_z |00⟩ = +|00⟩`: eigenvalue `+1` (N&C's `|1,−1⟩_J`; see the module docstring on signs). -/
theorem totalJz_mulVec_coupledTripletPlus :
    totalJz *ᵥ coupledTripletPlus = (1 : ℂ) • coupledTripletPlus := by
  rw [totalJz_eq]
  ext i
  fin_cases i <;>
    simp [coupledTripletPlus, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- `j_z |1,0⟩_J = 0`: the symmetric triplet state has `m_j = 0`. -/
theorem totalJz_mulVec_coupledTripletZero :
    totalJz *ᵥ coupledTripletZero = (0 : ℂ) • coupledTripletZero := by
  rw [totalJz_eq]
  ext i
  fin_cases i <;>
    simp [coupledTripletZero, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- `j_z |11⟩ = −|11⟩`: eigenvalue `−1` (N&C's `|1,1⟩_J`; see the module docstring on signs). -/
theorem totalJz_mulVec_coupledTripletMinus :
    totalJz *ᵥ coupledTripletMinus = (-1 : ℂ) • coupledTripletMinus := by
  rw [totalJz_eq]
  ext i
  fin_cases i <;>
    simp [coupledTripletMinus, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-! ### `J²` eigenvalues: each coupled state is a `J²`-eigenstate with eigenvalue `j(j+1)` -/

/-- `J² |0,0⟩_J = 0`: the singlet has `j = 0`, so `J²`-eigenvalue `j(j+1) = 0`. -/
theorem totalJSq_mulVec_coupledSinglet :
    totalJSq *ᵥ coupledSinglet = (0 : ℂ) • coupledSinglet := by
  rw [totalJSq_eq]
  ext i
  fin_cases i <;>
    simp [coupledSinglet, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- `J² |00⟩ = 2|00⟩`: the triplet has `j = 1`, so `J²`-eigenvalue `j(j+1) = 2`. -/
theorem totalJSq_mulVec_coupledTripletPlus :
    totalJSq *ᵥ coupledTripletPlus = (2 : ℂ) • coupledTripletPlus := by
  rw [totalJSq_eq]
  ext i
  fin_cases i <;>
    simp [coupledTripletPlus, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- `J² |1,0⟩_J = 2|1,0⟩_J`: `j = 1`, `J²`-eigenvalue `2`. -/
theorem totalJSq_mulVec_coupledTripletZero :
    totalJSq *ᵥ coupledTripletZero = (2 : ℂ) • coupledTripletZero := by
  rw [totalJSq_eq]
  ext i
  fin_cases i <;>
    simp [coupledTripletZero, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    ring

/-- `J² |11⟩ = 2|11⟩`: `j = 1`, `J²`-eigenvalue `2`. -/
theorem totalJSq_mulVec_coupledTripletMinus :
    totalJSq *ᵥ coupledTripletMinus = (2 : ℂ) • coupledTripletMinus := by
  rw [totalJSq_eq]
  ext i
  fin_cases i <;>
    simp [coupledTripletMinus, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-! ### The coupled basis is orthonormal -/

/-- The change-of-basis matrix `U` whose columns are the four coupled states, in Nielsen &
Chuang's order `|0,0⟩_J, |1,−1⟩_J, |1,0⟩_J, |1,1⟩_J` (singlet, `|00⟩`, symmetric triplet,
`|11⟩`). -/
noncomputable def coupledBasis : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0; invSqrt2, 0, invSqrt2, 0; -invSqrt2, 0, invSqrt2, 0; 0, 0, 0, 1]

/-- `1/√2` is fixed by the complex conjugation `starRingEnd`, the form in which the
conjugate-transpose entries of `coupledBasis` appear (`invSqrt2_star` phrased for
`starRingEnd`). -/
theorem invSqrt2_conj : (starRingEnd ℂ) invSqrt2 = invSqrt2 := invSqrt2_star

set_option maxRecDepth 1000 in
/-- The coupled basis is **orthonormal**: `Uᴴ U = I`. Hence the four states `|j, m_j⟩_J` form an
orthonormal basis of `ℂ⁴`, so writing `J²` and `j_z` "in that basis" is meaningful; combined
with the eigenvalue equations above, `Uᴴ J² U` and `Uᴴ j_z U` are the diagonal matrices
`diag(0,2,2,2)` and `diag(0,1,0,−1)`. -/
theorem coupledBasis_conjTranspose_mul_self :
    coupledBasisᴴ * coupledBasis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coupledBasis, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply,
      invSqrt2_conj, invSqrt2_mul_self] <;>
    norm_num

end AxQM.Concrete
