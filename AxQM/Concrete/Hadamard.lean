/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import ToMathlib.Data.Real.Sqrt
import ToMathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Complex.Basic
import ToMathlib.LinearAlgebra.Matrix.Hermitian
import ToMathlib.LinearAlgebra.UnitaryGroup
import ToMathlib.LinearAlgebra.Matrix.HermitianUnitary
import Mathlib.Tactic.LinearCombination

/-!
# Concrete: the Hadamard matrix and its `n`-fold tensor (Kronecker) power

This file defines the single-qubit Hadamard matrix `H` and its `n`-fold tensor power `H^{⊗n}` over
`ℝ`, proves the closed entry formula of Nielsen & Chuang, Exercise 2.33 (p. 74), and — for the qubit
*operator* work of Chapter 2 — the complex-entried Hadamard `H` together with its Hermiticity,
involution `H² = I`, and unitarity (membership in `Matrix.unitaryGroup`).

## The exercise

N&C write the one-qubit Hadamard operator (eq. 2.54) as
`H = (1/√2) [(|0⟩ + |1⟩)⟨0| + (|0⟩ − |1⟩)⟨1|]`, i.e. the real `2 × 2` matrix
`(1/√2) !![1, 1; 1, -1]`, and ask to show that the Hadamard transform on `n` qubits
`H^{⊗n}` may be written (eq. 2.55) as
`H^{⊗n} = (1/√(2ⁿ)) ∑_{x,y} (-1)^{x·y} |x⟩⟨y|`,
where `x, y` range over `n`-bit strings and `x·y = ∑ᵢ xᵢ yᵢ` is the bitwise dot product.
Finally it asks for an explicit matrix for `H^{⊗2}`.

## What is formalised

* `hadamard` — the `2 × 2` real matrix `(√2)⁻¹ • !![1, 1; 1, -1]` of eq. (2.54), and
  `hadamard_apply` — its entrywise closed form `H a b = (√2)⁻¹ (-1)^{a b}`.
* `hadamardPow n` — the `n`-fold tensor power, indexed by `n`-bit strings `Fin n → Fin 2`,
  defined by the honest block (Kronecker) recursion
  `H^{⊗(n+1)} x y = H (x 0) (y 0) · H^{⊗n} (tail x) (tail y)`. Its faithfulness as *the*
  tensor power is certified by `hadamardPow_apply`, the standard characterisation that a
  Kronecker-power entry is the product of the factor entries: `H^{⊗n} x y = ∏ᵢ H (xᵢ) (yᵢ)`.
* `hadamardPow_apply_eq` — **eq. (2.55)**: `H^{⊗n} x y = (√(2ⁿ))⁻¹ (-1)^{∑ᵢ xᵢ yᵢ}`. This is
  the exercise's main claim, proved (not assumed): the entry is the *product* `∏ᵢ H(xᵢ,yᵢ)`,
  and the closed form drops out of the single-qubit formula by distributing the product.
* `hadamardPow_two_submatrix` — the explicit `4 × 4` matrix for `H^{⊗2}`, in N&C's
  big-endian basis order `00, 01, 10, 11` (given by `bitPair2`).
* `hadamardC` — the same Hadamard `(√2)⁻¹ • !![1, 1; 1, -1]` but with **complex** entries
  (eq. 2.85), the form needed as an *operator* on the qubit's state space `ℂ²`. Its structural
  facts, matching the per-matrix facts of the Pauli file: `hadamardC_isHermitian` (`Hᴴ = H`),
  `hadamardC_mul_self` (`H² = I`, the involution), and `hadamardC_mem_unitaryGroup` — the
  formalisation of **Nielsen & Chuang, Exercise 2.51** (`H` is unitary, `Hᴴ H = I`), a one-line
  consequence of Hermiticity and the involution via `Matrix.IsHermitian.mem_unitaryGroup`.

These are the statements of N&C Exercises 2.33 and 2.51 (`AxQM/NC/Ch2/Exercise2_33.lean` and
`AxQM/NC/Ch2/Exercise2_51.lean`). The Hadamard gate `hadamardGate : Evolution qubit`, built on
`hadamardC_mem_unitaryGroup`, is in `AxQM/Postulates/API/HadamardGate.lean`.

## Design notes

* **Index type.** `n`-bit strings are `Fin n → Fin 2`, so an entry of `H^{⊗n}` is indexed by
  a pair of strings and the tensor power is a `Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℝ`.
  This makes the product-of-entries characterisation `∏ᵢ H(xᵢ,yᵢ)` a clean `Finset.prod`
  over `Fin n`, and the dot product `x·y` the natural `∑ᵢ (xᵢ).val (yᵢ).val : ℕ`.
* **Real vs. complex.** N&C's Hadamard has real entries. For the tensor-power identity (2.33) —
  a pure matrix identity with no physical content — `hadamard : Matrix (Fin 2) (Fin 2) ℝ` is
  faithful and keeps the `√2` bookkeeping (`sqrt_two_pow`) on `ℝ` where it is cleanest. The
  qubit gate operators of Chapter 2 act on `EuclideanSpace ℂ (Fin 2)`, so unitarity (2.51) is
  stated for the complex-entried `hadamardC : Matrix (Fin 2) (Fin 2) ℂ`; the two are the same
  matrix over their respective scalar rings (mirroring how the Pauli matrices are kept complex).
* **Unitarity via Hermitian ∧ involution.** `H` is real-symmetric, hence Hermitian, and squares
  to `I`; so `Hᴴ H = H H = I`, exactly the input shape of `Matrix.IsHermitian.mem_unitaryGroup`.
  This mirrors `pauliX_mem_unitaryGroup` etc. in `Concrete/Pauli.lean`, and reuses
  `hadamardC_isHermitian` / `hadamardC_mul_self` — the latter is also N&C Exercise 2.52 (`H² = I`).
* **`(-1)^{x·y}` as an integer power.** The exponent `∑ᵢ (xᵢ).val (yᵢ).val` is a genuine `ℕ`
  (not a residue mod 2); since `(-1 : ℝ)` has order `2`, `(-1)^k` depends only on parity, so
  this matches N&C's `(-1)^{x·y}` exactly.
-/

namespace AxQM.Concrete

open Matrix

/-- The single-qubit Hadamard matrix `H = (1/√2) !![1, 1; 1, -1]` (Nielsen & Chuang,
eq. 2.54). Its columns are `(|0⟩ + |1⟩)/√2` and `(|0⟩ − |1⟩)/√2`. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt 2)⁻¹ • !![1, 1; 1, -1]

/-- The single-qubit Hadamard entries in closed form: `H a b = (√2)⁻¹ (-1)^{a b}`. This is
the `n = 1` case of eq. (2.55): `H(0,0) = H(0,1) = H(1,0) = 1/√2` and `H(1,1) = -1/√2`. -/
theorem hadamard_apply (a b : Fin 2) :
    hadamard a b = (Real.sqrt 2)⁻¹ * (-1) ^ (a.val * b.val) := by
  fin_cases a <;> fin_cases b <;> simp [hadamard]

/-- The `n`-fold tensor (Kronecker) power `H^{⊗n}` of the Hadamard matrix, indexed by the
`n`-bit strings `Fin n → Fin 2`. Defined by the block recursion of the Kronecker product:
`H^{⊗0} = I` (a `1 × 1` matrix on the singleton index) and
`H^{⊗(n+1)} x y = H (x 0) (y 0) · H^{⊗n} (tail x) (tail y)`, i.e. the first qubit contributes
the Hadamard factor `H (x 0) (y 0)` and the remaining `n` qubits contribute `H^{⊗n}`. -/
noncomputable def hadamardPow : (n : ℕ) → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℝ
  | 0 => 1
  | n + 1 => fun x y => hadamard (x 0) (y 0) * hadamardPow n (Fin.tail x) (Fin.tail y)

/-- A Kronecker-power entry is the product of the factor entries:
`H^{⊗n} x y = ∏ᵢ H (xᵢ) (yᵢ)`. This is the textbook characterisation of the tensor power,
so it certifies that `hadamardPow` really is `H^{⊗n}` (rather than a definition rigged to the
answer). -/
theorem hadamardPow_apply (n : ℕ) (x y : Fin n → Fin 2) :
    hadamardPow n x y = ∏ i, hadamard (x i) (y i) := by
  induction n with
  | zero =>
      have hxy : x = y := Subsingleton.elim x y
      subst hxy
      simp [hadamardPow]
  | succ n ih =>
      simp only [hadamardPow]
      rw [ih (Fin.tail x) (Fin.tail y), Fin.prod_univ_succ]
      rfl

/-- `√2 ^ n = √(2ⁿ)`: pulling the square root through a power, on `ℝ`. -/
theorem sqrt_two_pow (n : ℕ) : Real.sqrt 2 ^ n = Real.sqrt (2 ^ n) := by
  have h : (2 : ℝ) ^ n = (Real.sqrt 2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt]
    norm_num
  rw [h, Real.sqrt_sq (by positivity)]

/-- **Nielsen & Chuang, Exercise 2.33 (eq. 2.55).** The Hadamard transform on `n` qubits has
the closed form `H^{⊗n} x y = (√(2ⁿ))⁻¹ (-1)^{x·y}`, where `x·y = ∑ᵢ xᵢ yᵢ` is the bitwise
dot product of the `n`-bit strings `x, y`. Proved from the product-of-entries formula
`hadamardPow_apply` by distributing the single-qubit closed form over the product. -/
theorem hadamardPow_apply_eq (n : ℕ) (x y : Fin n → Fin 2) :
    hadamardPow n x y
      = (Real.sqrt (2 ^ n))⁻¹ * (-1) ^ (∑ i, (x i).val * (y i).val) := by
  rw [hadamardPow_apply]
  simp_rw [hadamard_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
    Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [inv_pow, sqrt_two_pow]

/-- The four `2`-bit strings listed in Nielsen & Chuang's big-endian order `00, 01, 10, 11`
(the first component is the most significant bit). Used to reindex `H^{⊗2}` as an explicit
`4 × 4` matrix. -/
def bitPair2 : Fin 4 → (Fin 2 → Fin 2) := ![![0, 0], ![0, 1], ![1, 0], ![1, 1]]

/-- **Nielsen & Chuang, Exercise 2.33 (explicit `H^{⊗2}`).** In the big-endian basis order
`00, 01, 10, 11` (via `bitPair2`), the two-qubit Hadamard transform is the `4 × 4` matrix
`(1/2) !![1,1,1,1; 1,-1,1,-1; 1,1,-1,-1; 1,-1,-1,1]`. Each entry is `(1/2)(-1)^{x·y}` by the
`n = 2` case of eq. (2.55). -/
theorem hadamardPow_two_submatrix :
    (hadamardPow 2).submatrix bitPair2 bitPair2
      = (2⁻¹ : ℝ) • !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1] := by
  have hc : (Real.sqrt ((2 : ℝ) ^ 2))⁻¹ = 2⁻¹ := by
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  ext i j
  simp only [Matrix.submatrix_apply, hadamardPow_apply_eq, hc]
  fin_cases i <;> fin_cases j <;> norm_num [bitPair2, Fin.sum_univ_two]

/-! ### The complex Hadamard matrix and its unitarity (Nielsen & Chuang, Exercise 2.51)

The Hadamard `H = (1/√2) !![1, 1; 1, -1]` again, now over `ℂ` — the entry ring in which it is
an operator on the qubit's state space `EuclideanSpace ℂ (Fin 2)`. Like each Pauli matrix it is
Hermitian and an involution, and unitarity is the one-line consequence
`Hᴴ H = H H = I` via `Matrix.IsHermitian.mem_unitaryGroup`. -/

open Matrix Complex in
/-- The single-qubit Hadamard matrix `H = (1/√2) !![1, 1; 1, -1]` with **complex** entries
(Nielsen & Chuang, eq. 2.85). This is the operator form of `hadamard`, used to build the qubit
Hadamard gate; the two are the same matrix over `ℝ` resp. `ℂ`. -/
noncomputable def hadamardC : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ))⁻¹ • !![1, 1; 1, -1]

/-- Entry formula for the complex Hadamard matrix (the `ℂ` twin of `hadamard_apply`):
`hadamardC a b = (√2)⁻¹ * (-1) ^ (a * b)`. -/
theorem hadamardC_apply (a b : Fin 2) :
    hadamardC a b = (Real.sqrt 2 : ℂ)⁻¹ * (-1) ^ ((a : ℕ) * (b : ℕ)) := by
  fin_cases a <;> fin_cases b <;> simp [hadamardC, Matrix.smul_apply]

/-- The complex Hadamard matrix is Hermitian (`Hᴴ = H`): its entries `±1/√2` are real, and the
matrix is symmetric. -/
theorem hadamardC_isHermitian : hadamardC.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hadamardC, Matrix.conjTranspose_apply]

/-- The Hadamard normalisation scalar squares to `½`: `(√2)⁻¹ * (√2)⁻¹ = 2⁻¹` over `ℂ`. Shared by
the Hadamard involution and the Hadamard-conjugation lemmas, where the two `(√2)⁻¹` factors of
`H = (√2)⁻¹ !![1,1;1,-1]` combine. -/
theorem inv_sqrt_two_mul_self : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 2⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- The Hadamard matrix is an involution: `H² = I`. The scalar `((√2)⁻¹)² = 2⁻¹` combines with
`!![1,1;1,-1]² = 2 • I` to give the identity. (This is also Nielsen & Chuang, Exercise 2.52.) -/
theorem hadamardC_mul_self : hadamardC * hadamardC = 1 := by
  have hc : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ * 2 = 1 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hBB : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 1; 1, -1]
      = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  rw [hadamardC, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hBB, smul_smul, hc, one_smul]

/-- **Nielsen & Chuang, Exercise 2.51: the Hadamard gate `H` is unitary.** `H ∈ unitaryGroup`,
i.e. `Hᴴ H = I` (N&C's definition of unitary), from `hadamardC_isHermitian` and the involution
`hadamardC_mul_self` via `Matrix.IsHermitian.mem_unitaryGroup`. -/
theorem hadamardC_mem_unitaryGroup : hadamardC ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  hadamardC_isHermitian.mem_unitaryGroup hadamardC_mul_self

/-- Conjugation by the Hadamard gate is **multiplicative** (because `H² = I`):
`H (A B) H = (H A H) (H B H)`. Inserting `H H = 1` between `A` and `B` splits the conjugation over
the product; the reusable step for pushing a pair of Hadamards through a product of gates. -/
theorem hadamardC_conj_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    hadamardC * (A * B) * hadamardC
      = (hadamardC * A * hadamardC) * (hadamardC * B * hadamardC) := by
  rw [show (hadamardC * A * hadamardC) * (hadamardC * B * hadamardC)
        = hadamardC * A * (hadamardC * hadamardC) * B * hadamardC by noncomm_ring,
    hadamardC_mul_self]
  noncomm_ring

/-- Double-conjugation by the Hadamard gate is the **identity** (because `H² = I`):
`H (H A H) H = A`. The two `H H = 1` cancellations recover `A`; used to write `U = H (H U H) H`
before decomposing `H U H`. -/
theorem hadamardC_conj_conj (A : Matrix (Fin 2) (Fin 2) ℂ) :
    hadamardC * (hadamardC * A * hadamardC) * hadamardC = A := by
  rw [show hadamardC * (hadamardC * A * hadamardC) * hadamardC
        = (hadamardC * hadamardC) * A * (hadamardC * hadamardC) by noncomm_ring,
    hadamardC_mul_self, one_mul, mul_one]

/-- The Hadamard matrix is the phase `i` times the shared rotation-product core
`(√2)⁻¹ !![-i, -i; -i, i]` (` = -i H`): `H = i • ((√2)⁻¹ • !![-i, -i; -i, i])`. This is the common
final step of the Hadamard rotation-decomposition identities — the `R_x`–`R_z`–`R_x` product of
Exercise 4.4 (`HadamardRotation.lean`) and the `R_x`–`R_y` product of Exercise 7.31
(`HadamardRyRx.lean`) both evaluate to this matrix `-i H`, so multiplying by `e^{iπ/2} = i` recovers
`H` identically. Proved entrywise, closing each entry with `i² = -1` (`Complex.I_sq`). -/
theorem hadamardC_eq_I_smul_negIH :
    hadamardC = Complex.I • ((Real.sqrt 2 : ℂ)⁻¹ •
      !![-Complex.I, -Complex.I; -Complex.I, Complex.I]) := by
  rw [smul_smul, hadamardC]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_zero, Fin.mk_one,
      smul_eq_mul] <;>
    first
      | linear_combination (Real.sqrt 2 : ℂ)⁻¹ * Complex.I_sq
      | linear_combination (-(Real.sqrt 2 : ℂ)⁻¹) * Complex.I_sq

end AxQM.Concrete
