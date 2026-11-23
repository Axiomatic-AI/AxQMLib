/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Hadamard
import AxQM.Concrete.AxisAngleGateValues
import ToMathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Concrete: circuit matrices over `H, S, CNOT, Toffoli` are `2⁻ᵏ⸍² M` (Gaussian `M`)

This file is the mathematical core of the
first half of **Nielsen & Chuang, Exercise 4.45** (p. 198). N&C ask one to show that a unitary `U`
implemented by an `n`-qubit circuit built from the Hadamard `H`, phase `S`, `CNOT` and Toffoli
gates always has the form `U = 2⁻ᵏ⸍² M` for some integer `k`, where `M` is a `2ⁿ × 2ⁿ` matrix with
*complex integer* (Gaussian-integer, `ℤ[i]`) entries; and to repeat the exercise with the Toffoli
gate replaced by the `π/8` gate `T`.

This file develops the **reusable closure engine** and the **`H, S, CNOT, Toffoli` (Gaussian)
variant**; the `T`-gate variant — which needs the strictly larger cyclotomic ring `ℤ[ζ₈]`, with a
*proved* refutation that the literal `ℤ[i]` reading is false for `T` — is developed in
`AxQM/Concrete/Sqrt2CyclotomicMatrix.lean`, which reuses this same engine over a different
coefficient subring.

## The mathematical content and how it is captured

Since the library has no gate-set / circuit datatype (a circuit's unitary is just a product of the
matrices of its gates, and a gate on chosen wires is a Kronecker embedding of a small gate into the
`n`-qubit register), the exercise's content is exactly a **closure** statement:

* a scalar/matrix predicate `IsSqrt2ScaledIn R U := ∃ k, ∃ M over R, U = (√2)⁻¹ᵏ • M` — "`U` is a
  common power `2⁻ᵏ⸍²` times a matrix with entries in the subring `R ⊆ ℂ`" — where `(√2)⁻¹ᵏ = 2⁻ᵏ⸍²`
  (`sqrt_two_inv_pow_eq_rpow`);
* the predicate is closed under matrix product (`IsSqrt2ScaledIn.mul`, adding the `k`s), Kronecker
  product (`IsSqrt2ScaledIn.kron`, the tensoring-with-identity that embeds a gate), reindexing
  (`IsSqrt2ScaledIn.submatrix`, placing a gate on arbitrary wires), and contains the identity —
  i.e. the `IsSqrt2ScaledIn R` matrices of a fixed size form a `Submonoid`
  (`sqrt2ScaledMatrixSubmonoid`), so any list of them (a circuit) has a product of the same form
  (`isSqrt2ScaledIn_list_prod`);
* each generating gate has the form: `hadamardC` with `k = 1` (`isSqrt2ScaledIn_hadamardC`), and
  `sMatrix`, `cnotMatrix`, `toffoliMatrix` with `k = 0` (their entries already lie in the ring).

These pieces compose to the exercise: any circuit unitary — a product of embedded gates — is
`2⁻ᵏ⸍² M`. The theorem `exists_two_pow_neg_half_smul_gaussian` restates the predicate in N&C's
explicit `2⁻ᵏ⸍² • M` shape (entries certified `∃ a b : ℤ, · = a + b·i`), and
`exists_circuit_form_gaussian` packages "product of a list of such matrices ⇒ that form".

## The coefficient ring

`H, S, CNOT, Toffoli` → `gaussianIntSubring = ℤ[i]` (the Gaussian integers, exactly N&C's "complex
integer entries"). `H = 2⁻¹⸍² !![1,1;1,-1]`, `S = diag(1, i)`, and `CNOT`/`Toffoli` are `0/1`
permutation matrices — all with `ℤ[i]` entries.

## Faithfulness and generality

The theorems range over an arbitrary finite index type `m` (a superset of `Fin (2ⁿ)`), so
specialising to a `2ⁿ`-dimensional register is not a weakening; the `k` is a genuine natural number
and `M` a genuine matrix over the ring, matching "`2⁻ᵏ⸍² M`, `M` with integer entries" verbatim.
Compare the universality analysis in `AxQM/NC/Ch4/Exercise4_43.lean`. The statement of
Exercise 4.45 is in `AxQM/NC/Ch4/Exercise4_45.lean`, and the `T`-variant is in
`AxQM/Concrete/Sqrt2CyclotomicMatrix.lean`.
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

noncomputable section

variable {m n p q m' n' : Type*}

/-- **The `√2`-scaled-integer form.** A complex matrix `U` *is `√2`-scaled over the subring `R ⊆ ℂ`*
when `U = (√2)⁻¹ᵏ • M` for some `k : ℕ` and some matrix `M` with entries in `R`; since
`(√2)⁻¹ᵏ = 2⁻ᵏ⸍²` (`sqrt_two_inv_pow_eq_rpow`), this is Nielsen & Chuang's `2⁻ᵏ⸍² M` form with the
integer scale `k` shared across all entries. The gate ring of the `H, S, CNOT, Toffoli` variant of
Exercise 4.45 is `R = ℤ[i]` (`gaussianIntSubring`); the `T` variant uses `R = ℤ[ζ₈]`. -/
def IsSqrt2ScaledIn (R : Subring ℂ) (U : Matrix m n ℂ) : Prop :=
  ∃ (k : ℕ) (M : Matrix m n R), U = ((Real.sqrt 2 : ℂ))⁻¹ ^ k • M.map R.subtype

/-- A matrix all of whose entries already lie in `R` is `√2`-scaled over `R` (with `k = 0`). -/
theorem isSqrt2ScaledIn_of_forall_mem {R : Subring ℂ} (U : Matrix m n ℂ)
    (h : ∀ i j, U i j ∈ R) : IsSqrt2ScaledIn R U := by
  refine ⟨0, Matrix.of fun i j => ⟨U i j, h i j⟩, ?_⟩
  ext i j
  simp [Matrix.map_apply]

/-- The identity matrix is `√2`-scaled over any subring `R` (its entries are `0` and `1`). -/
theorem isSqrt2ScaledIn_one (R : Subring ℂ) [DecidableEq m] :
    IsSqrt2ScaledIn R (1 : Matrix m m ℂ) :=
  isSqrt2ScaledIn_of_forall_mem _ fun i j => by
    rw [Matrix.one_apply]; split <;> simp [R.one_mem, R.zero_mem]

/-- **Closure under matrix product** (the exercise's key step): the product of two `√2`-scaled
matrices over `R` is `√2`-scaled over `R`, with the powers `k` added — `(√2)⁻ᵏᴬ MA · (√2)⁻ᵏᴮ MB
= (√2)⁻⁽ᵏᴬ⁺ᵏᴮ⁾ (MA·MB)` and `MA·MB` has entries in `R` because `R` is a ring. -/
theorem IsSqrt2ScaledIn.mul {R : Subring ℂ} [Fintype m]
    {A B : Matrix m m ℂ} (hA : IsSqrt2ScaledIn R A) (hB : IsSqrt2ScaledIn R B) :
    IsSqrt2ScaledIn R (A * B) := by
  obtain ⟨kA, MA, rfl⟩ := hA
  obtain ⟨kB, MB, rfl⟩ := hB
  refine ⟨kA + kB, MA * MB, ?_⟩
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add]
  congr 1
  exact (Matrix.map_mul).symm

/-- **Closure under Kronecker product** — the tensoring-with-identity that embeds a gate acting on a
subset of the wires into the whole `n`-qubit register. The powers `k` again add. -/
theorem IsSqrt2ScaledIn.kron {R : Subring ℂ} {A : Matrix m n ℂ} {B : Matrix p q ℂ}
    (hA : IsSqrt2ScaledIn R A) (hB : IsSqrt2ScaledIn R B) :
    IsSqrt2ScaledIn R (A ⊗ₖ B) := by
  obtain ⟨kA, MA, rfl⟩ := hA
  obtain ⟨kB, MB, rfl⟩ := hB
  refine ⟨kA + kB, MA ⊗ₖ MB, ?_⟩
  have hmap : (MA.map R.subtype) ⊗ₖ (MB.map R.subtype) = (MA ⊗ₖ MB).map R.subtype := by
    ext ⟨i, k⟩ ⟨j, l⟩; simp [Matrix.kroneckerMap_apply, Matrix.map_apply]
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, ← pow_add, hmap]

/-- **Closure under reindexing** — a `√2`-scaled matrix stays `√2`-scaled after relabelling its
rows/columns (placing a gate on arbitrary wires, or reindexing a Kronecker tower to `Fin (2ⁿ)`). -/
theorem IsSqrt2ScaledIn.submatrix {R : Subring ℂ} {U : Matrix m n ℂ}
    (hU : IsSqrt2ScaledIn R U) (e : m' → m) (f : n' → n) :
    IsSqrt2ScaledIn R (U.submatrix e f) := by
  obtain ⟨k, M, rfl⟩ := hU
  refine ⟨k, M.submatrix e f, ?_⟩
  ext i j
  simp [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.map_apply]

/-- **The submonoid of `√2`-scaled matrices over `R`.** Bundling `isSqrt2ScaledIn_one` and
`IsSqrt2ScaledIn.mul`: the `IsSqrt2ScaledIn R` matrices of a fixed size are closed under products
and contain the identity, so a whole circuit (a list of gate matrices) has a product of the same
form (`isSqrt2ScaledIn_list_prod`). -/
def sqrt2ScaledMatrixSubmonoid (R : Subring ℂ) (m : Type*) [Fintype m] [DecidableEq m] :
    Submonoid (Matrix m m ℂ) where
  carrier := {U | IsSqrt2ScaledIn R U}
  mul_mem' := IsSqrt2ScaledIn.mul
  one_mem' := isSqrt2ScaledIn_one R

/-- **A circuit is `√2`-scaled** (the exercise, structurally): the product of a list of matrices,
each of which is `√2`-scaled over `R` — e.g. each an embedded `H`/`S`/`CNOT`/`Toffoli` gate —
is again `√2`-scaled over `R`. -/
theorem isSqrt2ScaledIn_list_prod (R : Subring ℂ) [Fintype m] [DecidableEq m]
    (L : List (Matrix m m ℂ)) (h : ∀ U ∈ L, IsSqrt2ScaledIn R U) :
    IsSqrt2ScaledIn R L.prod := by
  have : L.prod ∈ sqrt2ScaledMatrixSubmonoid R m := list_prod_mem h
  exact this

/-- The scale `(√2)⁻¹ᵏ` is exactly Nielsen & Chuang's `2⁻ᵏ⸍²`. -/
theorem sqrt_two_inv_pow_eq_rpow (k : ℕ) :
    ((Real.sqrt 2 : ℂ))⁻¹ ^ k = (((2 : ℝ) ^ (-(k : ℝ) / 2) : ℝ) : ℂ) := by
  rw [Real.rpow_div_two_eq_sqrt _ (by norm_num), Real.rpow_neg (by positivity)]
  push_cast
  rw [Real.rpow_natCast]
  simp [inv_pow]

/-! ### The Gaussian coefficient ring -/

/-- **The Gaussian integers `ℤ[i] ⊆ ℂ`**, `{a + b·i : a, b ∈ ℤ}` — Nielsen & Chuang's "complex
integers", the entry ring of the `H, S, CNOT, Toffoli` variant of Exercise 4.45. -/
def gaussianIntSubring : Subring ℂ where
  carrier := {z | ∃ a b : ℤ, z = a + b * Complex.I}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩; exact ⟨a + c, b + d, by push_cast; ring⟩
  mul_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c - b * d, a * d + b * c, ?_⟩
    push_cast
    linear_combination (b * d : ℂ) * Complex.I_mul_I
  neg_mem' := by rintro x ⟨a, b, rfl⟩; exact ⟨-a, -b, by push_cast; ring⟩

/-- Membership in `ℤ[i]` unfolds to "has integer real and imaginary parts". -/
theorem mem_gaussianIntSubring_iff {z : ℂ} :
    z ∈ gaussianIntSubring ↔ ∃ a b : ℤ, z = a + b * Complex.I := Iff.rfl

/-- `i ∈ ℤ[i]`. -/
theorem complexI_mem_gaussianIntSubring : Complex.I ∈ gaussianIntSubring := ⟨0, 1, by simp⟩

/-! ### The `CNOT` and Toffoli permutation matrices -/

/-- The **`CNOT` gate matrix** (control = first qubit), the basis permutation swapping `|10⟩ ↔ |11⟩`
(indices `2 ↔ 3` in the big-endian order `00, 01, 10, 11`). -/
def cnotMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => if Equiv.swap 2 3 i = j then 1 else 0

/-- The **Toffoli gate matrix** (controls = first two qubits), the basis permutation swapping
`|110⟩ ↔ |111⟩` (indices `6 ↔ 7` in the big-endian order `000, …, 111`). -/
def toffoliMatrix : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if Equiv.swap 6 7 i = j then 1 else 0

/-- Every permutation matrix (`0/1` entries) is `√2`-scaled over any subring `R` (with `k = 0`). -/
theorem isSqrt2ScaledIn_permMatrix (R : Subring ℂ) [DecidableEq m] (σ : Equiv.Perm m) :
    IsSqrt2ScaledIn R (Matrix.of fun i j => if σ i = j then (1 : ℂ) else 0) :=
  isSqrt2ScaledIn_of_forall_mem _ fun i j => by
    simp only [Matrix.of_apply]; split <;> simp [R.one_mem, R.zero_mem]

/-! ### Each generating gate is `√2`-scaled (over a suitable ring) -/

/-- The Hadamard gate `H = 2⁻¹⸍² !![1, 1; 1, -1]` is `√2`-scaled over any subring `R` (with `k = 1`
and `M = !![1, 1; 1, -1]`, whose entries `±1` lie in every subring). -/
theorem isSqrt2ScaledIn_hadamardC (R : Subring ℂ) : IsSqrt2ScaledIn R hadamardC := by
  refine ⟨1, (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) R), ?_⟩
  rw [pow_one, hadamardC]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

/-- The phase gate `S = diag(1, i)` is `√2`-scaled over any subring `R` containing `i` (`k = 0`). -/
theorem isSqrt2ScaledIn_sMatrix (R : Subring ℂ) (hi : Complex.I ∈ R) :
    IsSqrt2ScaledIn R sMatrix :=
  isSqrt2ScaledIn_of_forall_mem _ fun i j => by
    fin_cases i <;> fin_cases j <;> simp [sMatrix, R.one_mem, R.zero_mem, hi]

/-- The `CNOT` matrix is `√2`-scaled over any subring `R` (a `0/1` permutation matrix). -/
theorem isSqrt2ScaledIn_cnotMatrix (R : Subring ℂ) : IsSqrt2ScaledIn R cnotMatrix :=
  isSqrt2ScaledIn_permMatrix R _

/-- The Toffoli matrix is `√2`-scaled over any subring `R` (a `0/1` permutation matrix). -/
theorem isSqrt2ScaledIn_toffoliMatrix (R : Subring ℂ) : IsSqrt2ScaledIn R toffoliMatrix :=
  isSqrt2ScaledIn_permMatrix R _

/-! ### The `H, S, CNOT, Toffoli` gate set over the Gaussian integers -/

/-- `H` is a `√2`-scaled Gaussian-integer matrix. -/
theorem isSqrt2Gaussian_hadamardC : IsSqrt2ScaledIn gaussianIntSubring hadamardC :=
  isSqrt2ScaledIn_hadamardC _

/-- `S` is a `√2`-scaled Gaussian-integer matrix. -/
theorem isSqrt2Gaussian_sMatrix : IsSqrt2ScaledIn gaussianIntSubring sMatrix :=
  isSqrt2ScaledIn_sMatrix _ complexI_mem_gaussianIntSubring

/-- `CNOT` is a `√2`-scaled Gaussian-integer matrix. -/
theorem isSqrt2Gaussian_cnotMatrix : IsSqrt2ScaledIn gaussianIntSubring cnotMatrix :=
  isSqrt2ScaledIn_cnotMatrix _

/-- Toffoli is a `√2`-scaled Gaussian-integer matrix. -/
theorem isSqrt2Gaussian_toffoliMatrix : IsSqrt2ScaledIn gaussianIntSubring toffoliMatrix :=
  isSqrt2ScaledIn_toffoliMatrix _

/-! ### N&C's explicit `2⁻ᵏ⸍² M` form (Gaussian variant) -/

/-- **Nielsen & Chuang, Exercise 4.45, explicit form (Gaussian variant).** A `√2`-scaled
Gaussian-integer matrix `U` is `2⁻ᵏ⸍² M` with `M` a matrix of genuine complex integers
(`∃ a b : ℤ, M i j = a + b·i`). -/
theorem exists_two_pow_neg_half_smul_gaussian (U : Matrix m n ℂ)
    (hU : IsSqrt2ScaledIn gaussianIntSubring U) :
    ∃ (k : ℕ) (M : Matrix m n ℂ),
      (∀ i j, ∃ a b : ℤ, M i j = a + b * Complex.I) ∧
        U = (((2 : ℝ) ^ (-(k : ℝ) / 2) : ℝ) : ℂ) • M := by
  obtain ⟨k, M, rfl⟩ := hU
  refine ⟨k, M.map gaussianIntSubring.subtype, fun i j => ?_, ?_⟩
  · rw [Matrix.map_apply]; exact (M i j).2
  · rw [sqrt_two_inv_pow_eq_rpow]

/-- **Nielsen & Chuang, Exercise 4.45 (`H, S, CNOT, Toffoli`).** The unitary of any circuit — the
product `L.prod` of a list `L` of matrices each of which is a `√2`-scaled Gaussian-integer matrix
(e.g. an embedded `H`/`S`/`CNOT`/`Toffoli` gate) — has the form `2⁻ᵏ⸍² M` with `M` a `2ⁿ × 2ⁿ`
Gaussian-integer matrix. -/
theorem exists_circuit_form_gaussian [Fintype m] [DecidableEq m]
    (L : List (Matrix m m ℂ)) (h : ∀ U ∈ L, IsSqrt2ScaledIn gaussianIntSubring U) :
    ∃ (k : ℕ) (M : Matrix m m ℂ),
      (∀ i j, ∃ a b : ℤ, M i j = a + b * Complex.I) ∧
        L.prod = (((2 : ℝ) ^ (-(k : ℝ) / 2) : ℝ) : ℂ) • M :=
  exists_two_pow_neg_half_smul_gaussian _ (isSqrt2ScaledIn_list_prod _ L h)

end

end AxQM.Concrete
