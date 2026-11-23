/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliOuterProduct
import ToMathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.Norm

/-!
# Concrete: eigendecomposition of the Pauli matrices (Nielsen & Chuang, Exercise 2.11)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 2.11
("Eigendecomposition of the Pauli matrices", p. 69) asks to find the **eigenvectors**,
**eigenvalues**, and **diagonal representations** of the Pauli matrices `X`, `Y`, `Z`.

Each Pauli matrix is Hermitian with eigenvalues `+1` and `-1`, and its two normalized
eigenvectors form an orthonormal basis of `ℂ²`; N&C's *diagonal representation*
(eq. (2.29), also called an *orthonormal decomposition*) writes the operator as
`A = (+1)|ψ₊⟩⟨ψ₊| + (-1)|ψ₋⟩⟨ψ₋|` over that eigenbasis. Concretely:

* `Z`: eigenvectors `|0⟩, |1⟩` (eigenvalues `+1, -1`); `Z = |0⟩⟨0| - |1⟩⟨1|`.
* `X`: eigenvectors `|+⟩ = (|0⟩+|1⟩)/√2`, `|-⟩ = (|0⟩-|1⟩)/√2` (eigenvalues `+1, -1`);
  `X = |+⟩⟨+| - |-⟩⟨-|`.
* `Y`: eigenvectors `|+i⟩ = (|0⟩+i|1⟩)/√2`, `|-i⟩ = (|0⟩-i|1⟩)/√2` (eigenvalues `+1, -1`);
  `Y = |+i⟩⟨+i| - |-i⟩⟨-i|`.

This is pure linear algebra over `ℂ²`. It builds directly on
`AxQM.Concrete.PauliOuterProduct`: the Pauli matrices `pauliX/pauliY/pauliZ`, the
computational-basis kets `ket 0 = |0⟩`, `ket 1 = |1⟩`, and the outer-product decomposition
`pauliZ_eq_ketBra : Z = |0⟩⟨0| - |1⟩⟨1|` — which, because `|0⟩, |1⟩` *are* the eigenvectors
of `Z`, is already its diagonal representation, so `Z` is handled entirely by reuse.

## Design notes

* Everything stays at the matrix level, matching `Concrete.Pauli`/`Concrete.PauliOuterProduct`:
  the eigenvectors are plain column vectors `Fin 2 → ℂ`, the matrix acts by `Matrix.mulVec`
  (`M *ᵥ v`), and an outer product `|v⟩⟨v|` is `Matrix.vecMulVec v (star v)` (the bra `⟨v|`
  being the conjugate of `|v⟩`, faithful to N&C eq. (2.20)). No `EuclideanSpace`/`LinearMap`
  machinery is needed. Each eigenvalue equation is stated as `M *ᵥ v = μ • v` with the
  eigenvalue `μ ∈ {1, -1}` explicit, and each diagonal representation as a `2 × 2` matrix
  identity, so every fact reduces to an entrywise computation.
* The normalization constant `1/√2` is packaged as `invSqrt2`, with `invSqrt2_mul_self`
  (`(1/√2)² = 1/2`) the one arithmetic fact the `X`/`Y` outer products need; the eigenvalue
  equations, being linear, do not use it. `invSqrt2` is real, so it is fixed by conjugation
  (`invSqrt2_star`).
* Orthonormality of each eigenpair is recorded via the Hermitian inner product `⟨u|v⟩ =
  star u ⬝ᵥ v` of N&C eq. (2.14) (`Matrix.dotProduct` of the conjugate): the `_dotProduct_self`
  facts give `‖·‖² = 1` and the `_dotProduct_` cross facts give orthogonality — together
  certifying "an orthonormal set of eigenvectors", which is what makes the outer-product
  sums genuine *diagonal representations* in N&C's sense.
-/

namespace AxQM.Concrete

open Matrix Complex

/-! ### The normalization constant `1/√2` and the self outer product `|v⟩⟨v|` -/

/-- The normalization constant `1/√2`, as a complex number. It is the shared coefficient of
the `X`- and `Y`-eigenvectors `|±⟩`, `|±i⟩`. -/
noncomputable def invSqrt2 : ℂ := (Real.sqrt 2 : ℂ)⁻¹

/-- `(1/√2)·(1/√2) = 1/2`: the single arithmetic fact behind the `X`/`Y` diagonal
representations and normalizations (each outer-product entry is a product of two `1/√2`s). -/
theorem invSqrt2_mul_self : invSqrt2 * invSqrt2 = 2⁻¹ := by
  rw [invSqrt2, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- `(1/√2)² = 1/2`, the squared form of `invSqrt2_mul_self`. -/
theorem invSqrt2_sq : invSqrt2 ^ 2 = 2⁻¹ := by rw [sq, invSqrt2_mul_self]

/-- `‖(1/√2 : ℂ)‖² = 1/2`: the squared magnitude of the shared amplitude of `|±⟩`, used when
normalizing the `X`-eigenstates. -/
theorem norm_invSqrt2_sq : ‖(invSqrt2 : ℂ)‖ ^ 2 = 2⁻¹ := by
  rw [invSqrt2, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2)), inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- `1/√2` is real, hence fixed by complex conjugation: `conj (1/√2) = 1/√2`. -/
theorem invSqrt2_star : star invSqrt2 = invSqrt2 := by simp [invSqrt2]

/-- `1/√2 ≠ 0`. -/
theorem invSqrt2_ne_zero : invSqrt2 ≠ 0 := by rw [invSqrt2]; simp

/-- The self outer product `|v⟩⟨v|` of a column vector `v : Fin 2 → ℂ`, as the `2 × 2`
matrix `vecMulVec v (star v)` with `(a, b)` entry `vₐ · conj v_b` (the bra `⟨v|` is the
conjugate of the ket `|v⟩`). When `v` is a unit vector this is the rank-one orthogonal
projector onto `v`; a diagonal representation is a signed sum of such projectors. -/
def outerSelf (v : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := vecMulVec v (star v)

/-- The `(a, b)` entry of `|v⟩⟨v|` is `vₐ · conj v_b`. -/
theorem outerSelf_apply (v : Fin 2 → ℂ) (a b : Fin 2) :
    outerSelf v a b = v a * star (v b) := rfl

/-! ### Eigendecomposition of `Z`

The eigenvectors of `Z` are the computational-basis kets `|0⟩, |1⟩` (`ket 0`, `ket 1` from
`PauliOuterProduct`), with eigenvalues `+1, -1`. Its diagonal representation
`Z = |0⟩⟨0| - |1⟩⟨1|` coincides with the outer-product expansion `pauliZ_eq_ketBra`. -/

/-- `|0⟩` is an eigenvector of `Z` with eigenvalue `+1`: `Z|0⟩ = |0⟩`. -/
theorem pauliZ_mulVec_ket_zero : pauliZ *ᵥ ket 0 = (1 : ℂ) • ket 0 := by
  ext i; fin_cases i <;> simp [pauliZ, ket, Matrix.mulVec]

/-- `|1⟩` is an eigenvector of `Z` with eigenvalue `-1`: `Z|1⟩ = -|1⟩`. -/
theorem pauliZ_mulVec_ket_one : pauliZ *ᵥ ket 1 = (-1 : ℂ) • ket 1 := by
  ext i; fin_cases i <;> simp [pauliZ, ket, Matrix.mulVec]

/-- The diagonal representation of `Z`: `Z = |0⟩⟨0| - |1⟩⟨1|`. This is exactly the
outer-product expansion `pauliZ_eq_ketBra`, since `|0⟩, |1⟩` are the eigenvectors of `Z`
(`outerSelf (ket i) = ketBra i i` by definition). -/
theorem pauliZ_eq_outerSelf_sub : pauliZ = outerSelf (ket 0) - outerSelf (ket 1) :=
  pauliZ_eq_ketBra

/-! ### Eigendecomposition of `X`

The eigenvectors of `X` are `|+⟩ = (|0⟩+|1⟩)/√2` and `|-⟩ = (|0⟩-|1⟩)/√2`, with eigenvalues
`+1, -1`; the diagonal representation is `X = |+⟩⟨+| - |-⟩⟨-|`. -/

/-- The `X`-eigenvector `|+⟩ = (|0⟩ + |1⟩)/√2 = (1/√2, 1/√2)`, eigenvalue `+1`. -/
noncomputable def xPlus : Fin 2 → ℂ := ![invSqrt2, invSqrt2]

/-- The `X`-eigenvector `|-⟩ = (|0⟩ - |1⟩)/√2 = (1/√2, -1/√2)`, eigenvalue `-1`. -/
noncomputable def xMinus : Fin 2 → ℂ := ![invSqrt2, -invSqrt2]

/-- Both components of `|+⟩ = (1/√2, 1/√2)` equal `1/√2`: the definitional unfold of
`xPlus`, provided at its definition site so every consumer inherits it. -/
@[simp] theorem xPlus_apply (i : Fin 2) : xPlus i = invSqrt2 := by fin_cases i <;> rfl

/-- `|+⟩` is an eigenvector of `X` with eigenvalue `+1`: `X|+⟩ = |+⟩`. -/
theorem pauliX_mulVec_xPlus : pauliX *ᵥ xPlus = (1 : ℂ) • xPlus := by
  ext i; fin_cases i <;> simp [pauliX, xPlus, Matrix.mulVec]

/-- `|-⟩` is an eigenvector of `X` with eigenvalue `-1`: `X|-⟩ = -|-⟩`. -/
theorem pauliX_mulVec_xMinus : pauliX *ᵥ xMinus = (-1 : ℂ) • xMinus := by
  ext i; fin_cases i <;> simp [pauliX, xMinus, Matrix.mulVec]

/-- `X` flips the computational-basis ket: `X|i⟩ = |i ⊕ 1⟩`. The matrix-action companion of the
`Z`-ket eigenvalue lemmas `pauliZ_mulVec_ket_zero`/`_one`, on the standard basis vector
`ket i = Pi.single i 1`. -/
theorem pauliX_mulVec_ket (i : Fin 2) : pauliX *ᵥ ket i = ket (i + 1) := by
  ext j; fin_cases i <;> fin_cases j <;> simp [pauliX, ket, Matrix.mulVec]

/-- `Y` flips the computational-basis ket with a phase: `Y|i⟩ = i · (-1)ⁱ · |i ⊕ 1⟩`
(`Y|0⟩ = i|1⟩`, `Y|1⟩ = -i|0⟩`). The `Y` companion of `pauliX_mulVec_ket` / `pauliZ_mulVec_ket_*`,
on the standard basis vector `ket i = Pi.single i 1`, read off from `pauliY = !![0, -I; I, 0]`. -/
theorem pauliY_mulVec_ket (i : Fin 2) :
    pauliY *ᵥ ket i = (Complex.I * (-1) ^ (i : ℕ)) • ket (i + 1) := by
  ext j; fin_cases i <;> fin_cases j <;> simp [pauliY, ket, Matrix.mulVec]

/-- `|+⟩` is a unit vector: `⟨+|+⟩ = 1`. -/
theorem xPlus_dotProduct_self : star xPlus ⬝ᵥ xPlus = 1 := by
  simp only [xPlus, dotProduct, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, invSqrt2_star, invSqrt2_mul_self]
  norm_num

/-- `|-⟩` is a unit vector: `⟨-|-⟩ = 1`. -/
theorem xMinus_dotProduct_self : star xMinus ⬝ᵥ xMinus = 1 := by
  simp only [xMinus, dotProduct, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, star_neg, invSqrt2_star, neg_mul, mul_neg, neg_neg, invSqrt2_mul_self]
  norm_num

/-- `|+⟩` and `|-⟩` are orthogonal: `⟨+|-⟩ = 0`. -/
theorem xPlus_dotProduct_xMinus : star xPlus ⬝ᵥ xMinus = 0 := by
  simp only [xPlus, xMinus, dotProduct, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, invSqrt2_star, mul_neg]
  ring

/-- `|+⟩` is nonzero (so it is a genuine eigenvector). -/
theorem xPlus_ne_zero : xPlus ≠ 0 := by
  intro h; have := xPlus_dotProduct_self; rw [h] at this; simp at this

/-- `|-⟩` is nonzero (so it is a genuine eigenvector). -/
theorem xMinus_ne_zero : xMinus ≠ 0 := by
  intro h; have := xMinus_dotProduct_self; rw [h] at this; simp at this

/-- The diagonal representation of `X`: `X = |+⟩⟨+| - |-⟩⟨-|`. -/
theorem pauliX_eq_outerSelf_sub : pauliX = outerSelf xPlus - outerSelf xMinus := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [pauliX, outerSelf, vecMulVec_apply, Pi.star_apply, Matrix.sub_apply,
      ] <;>
    simp [xPlus, xMinus, invSqrt2_star] <;>
    ring_nf <;> simp [invSqrt2_sq]

/-! ### Eigendecomposition of `Y`

The eigenvectors of `Y` are `|+i⟩ = (|0⟩+i|1⟩)/√2` and `|-i⟩ = (|0⟩-i|1⟩)/√2`, with
eigenvalues `+1, -1`; the diagonal representation is `Y = |+i⟩⟨+i| - |-i⟩⟨-i|`. -/

/-- The `Y`-eigenvector `|+i⟩ = (|0⟩ + i|1⟩)/√2 = (1/√2, i/√2)`, eigenvalue `+1`. -/
noncomputable def yPlus : Fin 2 → ℂ := ![invSqrt2, invSqrt2 * I]

/-- The `Y`-eigenvector `|-i⟩ = (|0⟩ - i|1⟩)/√2 = (1/√2, -i/√2)`, eigenvalue `-1`. -/
noncomputable def yMinus : Fin 2 → ℂ := ![invSqrt2, -(invSqrt2 * I)]

/-- `|+i⟩` is an eigenvector of `Y` with eigenvalue `+1`: `Y|+i⟩ = |+i⟩`. -/
theorem pauliY_mulVec_yPlus : pauliY *ᵥ yPlus = (1 : ℂ) • yPlus := by
  ext i
  fin_cases i
  all_goals simp [pauliY, yPlus, Matrix.mulVec, mul_comm]
  ring_nf
  rw [Complex.I_sq]; ring

/-- `|-i⟩` is an eigenvector of `Y` with eigenvalue `-1`: `Y|-i⟩ = -|-i⟩`. -/
theorem pauliY_mulVec_yMinus : pauliY *ᵥ yMinus = (-1 : ℂ) • yMinus := by
  ext i
  fin_cases i
  all_goals simp [pauliY, yMinus, Matrix.mulVec, mul_comm]
  ring_nf
  rw [Complex.I_sq]; ring

/-- `|+i⟩` is a unit vector: `⟨+i|+i⟩ = 1`. -/
theorem yPlus_dotProduct_self : star yPlus ⬝ᵥ yPlus = 1 := by
  simp only [yPlus, dotProduct, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, star_mul', invSqrt2_star]
  ring_nf
  rw [show star I = -I from Complex.conj_I, invSqrt2_sq]; ring_nf; rw [Complex.I_sq]; norm_num

/-- `|-i⟩` is a unit vector: `⟨-i|-i⟩ = 1`. -/
theorem yMinus_dotProduct_self : star yMinus ⬝ᵥ yMinus = 1 := by
  simp only [yMinus, dotProduct, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, star_neg, star_mul', invSqrt2_star]
  ring_nf
  rw [show star I = -I from Complex.conj_I, invSqrt2_sq]; ring_nf; rw [Complex.I_sq]; norm_num

/-- `|+i⟩` and `|-i⟩` are orthogonal: `⟨+i|-i⟩ = 0`. -/
theorem yPlus_dotProduct_yMinus : star yPlus ⬝ᵥ yMinus = 0 := by
  simp only [yPlus, yMinus, dotProduct, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, star_mul', invSqrt2_star]
  ring_nf
  rw [show star I = -I from Complex.conj_I, invSqrt2_sq]; ring_nf; rw [Complex.I_sq]; norm_num

/-- `|+i⟩` is nonzero (so it is a genuine eigenvector). -/
theorem yPlus_ne_zero : yPlus ≠ 0 := by
  intro h; have := yPlus_dotProduct_self; rw [h] at this; simp at this

/-- `|-i⟩` is nonzero (so it is a genuine eigenvector). -/
theorem yMinus_ne_zero : yMinus ≠ 0 := by
  intro h; have := yMinus_dotProduct_self; rw [h] at this; simp at this

/-- The diagonal representation of `Y`: `Y = |+i⟩⟨+i| - |-i⟩⟨-i|`. -/
theorem pauliY_eq_outerSelf_sub : pauliY = outerSelf yPlus - outerSelf yMinus := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [pauliY, outerSelf, vecMulVec_apply, Pi.star_apply, Matrix.sub_apply,
      ] <;>
    simp [yPlus, yMinus, invSqrt2_star, Complex.conj_I] <;>
    ring_nf <;> simp only [invSqrt2_sq] <;> ring

/-! ### Reflections about the `-1`-eigenvectors are the Pauli matrices

For each Pauli `P ∈ {X, Y, Z}` with `-1`-eigenvector `|ψ₋⟩`, the reflection `I - 2|ψ₋⟩⟨ψ₋|`
equals `P` itself. Indeed `|ψ₋⟩` is fixed (with sign flip) by `P`, so `P = |ψ₊⟩⟨ψ₊| - |ψ₋⟩⟨ψ₋|`
and `I = |ψ₊⟩⟨ψ₊| + |ψ₋⟩⟨ψ₋|` give `I - 2|ψ₋⟩⟨ψ₋| = P`. These are the concrete matrix core of
Nielsen & Chuang Problem 6.2(2): the three oracles `U_{|ψᵢ⟩} = I - 2|ψᵢ⟩⟨ψᵢ|` for
`|ψ₁⟩ = |1⟩`, `|ψ₂⟩ = |-⟩`, `|ψ₃⟩ = |-i⟩` are exactly the Pauli matrices `Z`, `X`, `Y`. -/

/-- **N&C Problem 6.2(2), `Z` case.** The reflection about `|1⟩` is `Z`:
`I - 2|1⟩⟨1| = Z` (since `Z = |0⟩⟨0| - |1⟩⟨1|` and `I = |0⟩⟨0| + |1⟩⟨1|`). -/
theorem one_sub_two_smul_outerSelf_ket_one :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) - (2 : ℂ) • outerSelf (ket 1) = pauliZ := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [pauliZ, outerSelf, ket, Matrix.vecMulVec_apply, Pi.single_apply]

/-- **N&C Problem 6.2(2), `X` case.** The reflection about `|-⟩ = (|0⟩ - |1⟩)/√2` is `X`:
`I - 2|-⟩⟨-| = X`. -/
theorem one_sub_two_smul_outerSelf_xMinus :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) - (2 : ℂ) • outerSelf xMinus = pauliX := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [pauliX, outerSelf, Matrix.one_apply, Matrix.smul_apply, Matrix.sub_apply,
      vecMulVec_apply, Pi.star_apply] <;>
    simp [xMinus, invSqrt2_star] <;>
    ring_nf <;> simp only [invSqrt2_sq] <;> ring

/-- **N&C Problem 6.2(2), `Y` case.** The reflection about `|-i⟩ = (|0⟩ - i|1⟩)/√2` is `Y`:
`I - 2|-i⟩⟨-i| = Y`. -/
theorem one_sub_two_smul_outerSelf_yMinus :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) - (2 : ℂ) • outerSelf yMinus = pauliY := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [pauliY, outerSelf, Matrix.one_apply, Matrix.smul_apply, Matrix.sub_apply,
      vecMulVec_apply, Pi.star_apply] <;>
    simp [yMinus, invSqrt2_star, Complex.conj_I] <;>
    ring_nf <;> simp only [invSqrt2_sq, Complex.I_sq] <;> ring

end AxQM.Concrete
