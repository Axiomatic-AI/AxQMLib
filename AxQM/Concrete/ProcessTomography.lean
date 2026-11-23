/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli
import Mathlib.Data.Matrix.Basis

/-!
# Concrete: single-qubit quantum process tomography (Nielsen & Chuang, Box 8.5)

This file records the linear-algebra
**reconstruction identity** behind quantum process tomography for a single qubit — Nielsen &
Chuang's Box 8.5, eq. (8.179).

A single-qubit quantum operation is written in the fixed operator basis `Ẽ₀ = I`, `Ẽ₁ = X`,
`Ẽ₂ = -iY`, `Ẽ₃ = Z` (`tomoBasis`) as `E(ρ) = Σ_{mn} χ_{mn} Ẽ_m ρ Ẽ_n†` (`chiProcess`), the `4 × 4`
Hermitian matrix `χ` being the object process tomography determines. Box 8.5 gives the closed-form
reconstruction of `χ` from experimentally measured outputs: with the `2 × 2`-block matrix

`Λ = (1/2) [[I, X], [X, -I]]`   (`chiLambda`, N&C eq. (8.178))

and the block matrix of measured density matrices `M`, block `(a,b)` = `E(|a⟩⟨b|)` (`chiGrid`),

`χ = Λ M Λ`   (`chiLambda_chiGrid_chiLambda`, N&C eq. (8.179)).

## Index convention

All `4 × 4` matrices carry the index type `Fin 2 × Fin 2`, so the `2 × 2`-block structure that N&C
writes by hand is *literal*: the first component selects the block, the second the entry within it.
Under `(hi, lo) ↦ 2·hi + lo` this matches N&C's flat operator index `m ∈ {0,1,2,3}` for `χ`/`Λ`, and
the computational-basis pair `(a, i)` for `M`. `Λ` is symmetric, so the same matrix serves on both
sides of the sandwich.

## Proof strategy

The identity holds for **every** `χ` — it is a linear-algebra fact about the operator-sum
superoperator and its reconstruction, the physical (Hermitian, trace-preserving) content living only
in the interpretation. It is proved by decomposing the grid into rank-one pieces
`tomoOuter m n = Ẽ_m |·⟩⟨·| Ẽ_n†` (`chiGrid_eq`), reducing to the elementary-matrix identity
`Λ (Ẽ_m |·⟩⟨·| Ẽ_n†) Λ = single m n 1` (`chiLambda_tomoOuter_chiLambda`), which factors through two
duality facts saying `Λ` is dual to the operator basis (`chiLambda_dual_left`,
`chiLambda_dual_right`). Every operator-basis entry is real, so the conjugations are inert.

It is the
shared foundation for the two exercises on process tomography: **Exercise 8.34** (two qubits,
`Λ₂ = Λ ⊗ Λ` with a permutation matrix, N&C eqs. (8.180)–(8.181)) and **Exercise 8.35** (a worked
single-qubit example).
-/

namespace AxQM.Concrete

open Matrix
open scoped Matrix

noncomputable section

/-- Box 8.5 fixed operator basis `{I, X, -iY, Z}`, indexed by `Fin 2 × Fin 2`
(`m ↦ Ẽ_(2·m.1+m.2)`), reusing the shared Pauli matrices `Concrete.pauliX/Y/Z`. -/
def tomoBasis : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ
  | (0, 0) => 1
  | (0, 1) => pauliX
  | (1, 0) => (-Complex.I) • pauliY
  | (1, 1) => pauliZ

/-- Lambda from Box 8.5: the block matrix `(1/2)·[[I, X], [X, -I]]`. -/
def chiLambda : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun pq ai =>
    (2 : ℂ)⁻¹ * (if pq.1 = ai.1
                 then (if pq.1 = 0 then 1 else -1) * (if pq.2 = ai.2 then 1 else 0)
                 else (if pq.2 = ai.2 then 0 else 1))

/-- The process `E(ρ) = Σ χ_mn Ẽ_m ρ Ẽ_n†`. -/
def chiProcess (χ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ m, ∑ n, χ m n • (tomoBasis m * ρ * (tomoBasis n)ᴴ)

/-- The block matrix of measured outputs, block `(a,b)` = `E(|a⟩⟨b|)`. -/
def chiGrid (χ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun ai bj => chiProcess χ (Matrix.single ai.1 bj.1 1) ai.2 bj.2

/-- The rank-one piece `Ẽ_m |·⟩⟨·| Ẽ_n†`, as a block matrix over `Fin 2 × Fin 2`. -/
def tomoOuter (m n : Fin 2 × Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun ai bj => tomoBasis m ai.2 ai.1 * star (tomoBasis n bj.2 bj.1)

/-- Left duality: `Σ_A Λ(P,A)·(Ẽ_m)_{A.2,A.1} = δ(P,m)`. -/
theorem chiLambda_dual_left (P m : Fin 2 × Fin 2) :
    ∑ A : Fin 2 × Fin 2, chiLambda P A * tomoBasis m A.2 A.1 = if P = m then 1 else 0 := by
  obtain ⟨p1, p2⟩ := P
  obtain ⟨m1, m2⟩ := m
  fin_cases p1 <;> fin_cases p2 <;> fin_cases m1 <;> fin_cases m2 <;>
    simp [chiLambda, tomoBasis, pauliX, pauliY, pauliZ, Matrix.smul_apply, smul_eq_mul,
      Fintype.sum_prod_type, Fin.sum_univ_two, Prod.ext_iff] <;> norm_num [Complex.ext_iff]

/-- Right duality: `Σ_B conj((Ẽ_n)_{B.2,B.1})·Λ(B,R) = δ(n,R)`. -/
theorem chiLambda_dual_right (n R : Fin 2 × Fin 2) :
    ∑ B : Fin 2 × Fin 2, star (tomoBasis n B.2 B.1) * chiLambda B R = if n = R then 1 else 0 := by
  obtain ⟨n1, n2⟩ := n
  obtain ⟨r1, r2⟩ := R
  fin_cases n1 <;> fin_cases n2 <;> fin_cases r1 <;> fin_cases r2 <;>
    simp [chiLambda, tomoBasis, pauliX, pauliY, pauliZ, Matrix.smul_apply, smul_eq_mul,
      Fintype.sum_prod_type, Fin.sum_univ_two, Prod.ext_iff] <;> norm_num [Complex.ext_iff]

/-- Extract a matrix triple product against a single-entry matrix:
`(A · single a b 1 · B†)_{ij} = A_{ia} · conj(B_{jb})`. Stated over an arbitrary finite index
type so both the single-qubit reconstruction here and the two-qubit lift can reuse it. -/
theorem mul_single_mul_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (a b i j : ι) :
    (A * Matrix.single a b (1 : ℂ) * Bᴴ) i j = A i a * star (B j b) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
  · rw [Matrix.single_mul_apply_same, one_mul, Matrix.conjTranspose_apply]
  · intro x _ hx
    have hzero : (Matrix.single a b (1 : ℂ) * Bᴴ) x j = 0 :=
      Matrix.single_mul_apply_of_ne _ _ _ _ _ hx _
    rw [hzero, mul_zero]

/-- The grid decomposes into the rank-one pieces weighted by `χ`. -/
theorem chiGrid_eq (χ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    chiGrid χ = ∑ m, ∑ n, χ m n • tomoOuter m n := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [chiGrid, Matrix.of_apply, chiProcess, Matrix.sum_apply, Matrix.smul_apply,
    mul_single_mul_conjTranspose, tomoOuter, smul_eq_mul]

/-- Sandwiching a rank-one piece by `Λ` recovers the elementary matrix `single m n 1`. -/
theorem chiLambda_tomoOuter_chiLambda (m n : Fin 2 × Fin 2) :
    chiLambda * tomoOuter m n * chiLambda = Matrix.single m n 1 := by
  ext P R
  simp only [Matrix.mul_apply, tomoOuter, Matrix.of_apply]
  simp_rw [← mul_assoc, ← Finset.sum_mul, chiLambda_dual_left]
  simp_rw [mul_assoc, ← Finset.mul_sum, chiLambda_dual_right]
  rw [Matrix.single_apply]
  split_ifs <;> simp_all

/-- **Box 8.5 process reconstruction** (Nielsen & Chuang eq. (8.179)):
`χ = Λ (block matrix of measured outputs) Λ`. -/
theorem chiLambda_chiGrid_chiLambda (χ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    chiLambda * chiGrid χ * chiLambda = χ := by
  rw [chiGrid_eq]
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    chiLambda_tomoOuter_chiLambda, Matrix.smul_single, smul_eq_mul, mul_one,
    ← Matrix.matrix_eq_sum_single]

end

end AxQM.Concrete
