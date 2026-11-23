/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import ToMathlib.LinearAlgebra.Matrix.Hermitian
import ToMathlib.LinearAlgebra.UnitaryGroup
import ToMathlib.LinearAlgebra.Matrix.HermitianUnitary
import ToMathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Complex.Basic
import ToMathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Module

/-!
# Concrete: the Pauli matrices and the combination `n · σ`

This file defines the three `2 × 2` Pauli matrices `X`, `Y`, `Z` over `ℂ` and, for a real
three-vector `n`, the Hermitian combination

`pauliDot n = n₀ • X + n₁ • Y + n₂ • Z`  ("`n · σ`"),

together with its two structural facts:

* `pauliDot_isHermitian` — `n · σ` is Hermitian (this is the combination used throughout
  Chapter 2).
* `pauliDot_mul_self` — `(n · σ)² = ‖n‖² • I` (with `‖n‖² = n₀² + n₁² + n₂²`), and its
  corollary `pauliDot_mul_self_of_unit` giving `(n · σ)² = I` for a unit vector.

The **per-matrix** facts of Nielsen & Chuang, Exercise 2.19 ("the Pauli matrices are
Hermitian and unitary") are formalized here too:

* `pauliX_mul_self`, `pauliY_mul_self`, `pauliZ_mul_self` — each Pauli matrix is an
  involution (`σ² = I`), the anticommutation-free diagonal case of `pauliDot_mul_self`.
* `pauliX_isHermitian`, `pauliY_isHermitian`, `pauliZ_isHermitian` — `σᴴ = σ`.
* `pauliX_mem_unitaryGroup`, `pauliY_mem_unitaryGroup`, `pauliZ_mem_unitaryGroup` — each
  `σ` is unitary in the sense of N&C (`σᴴ σ = I`, i.e. membership in `Matrix.unitaryGroup`),
  immediate from being Hermitian and an involution. (`σ₀ = I` is trivially both, via
  Mathlib's `Matrix.isHermitian_one` / `unitary` structure on `1`.)

The trace facts of Nielsen & Chuang, Exercise 2.36 ("the Pauli matrices except `I` have trace
zero") are formalized here too:

* `pauliX_trace`, `pauliY_trace`, `pauliZ_trace` — each non-identity Pauli matrix is traceless
  (`tr σ = 0`), by summing its diagonal entries (`0 + 0`, `0 + 0`, and `1 + (-1)`).
* `trace_one_fin_two` — the exception `σ₀ = I` has trace `2 ≠ 0`, so `I` is genuinely the one
  Pauli matrix that is *not* traceless.

The anticommutation relations of Nielsen & Chuang, Exercise 2.41 are formalized here too, along
with an indexed Pauli family `pauli : Fin 4 → M₂(ℂ)` (`σ₀ = I`, `σ₁ = X`, `σ₂ = Y`, `σ₃ = Z`):

* `pauliX_anticomm_pauliY`, `pauliY_anticomm_pauliZ`, `pauliX_anticomm_pauliZ` — the three
  anticommutators `{σᵢ, σⱼ} = σᵢ σⱼ + σⱼ σᵢ = 0` for the distinct pairs from `{X, Y, Z}` (eq. 2.75).
* `pauli_mul_self` — `σᵢ² = I` for every `i = 0, 1, 2, 3` (eq. 2.76), and `pauli_anticomm` — the
  anticommutation relations in indexed form (`{σᵢ, σⱼ} = 0` for distinct `i, j ∈ {1, 2, 3}`).

These are the shared foundation for the many Chapter 2 items about `n · σ` — the rotation
and exponential formulas (Ex 2.35, Ex 4.5), the eigenprojectors `P± = (I ± n·σ)/2`
(Ex 2.60), Tsirelson's inequality (Prob 2.3), and the functional-calculus decomposition
`f(θ n·σ) = …` (Prob 2.1).

## Design notes

* The direction `n` is modelled as a bare `Fin 3 → ℝ` and normalization as the scalar
  hypothesis `n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1`, rather than as `EuclideanSpace ℝ (Fin 3)`
  with `‖n‖ = 1`. This keeps the statements self-contained and the `n · σ` algebra a
  direct `2 × 2` computation, and matches how N&C writes `n̂ · σ ≡ Σᵢ nᵢ σᵢ`.
* `pauliDot_eq` collapses the definitional sum into a single explicit `2 × 2` matrix; every
  later fact is proved by reducing to this closed form and computing entrywise.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The Pauli `X` matrix `!![0, 1; 1, 0]`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix `!![0, -i; i, 0]`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- The Pauli `Z` matrix `!![1, 0; 0, -1]`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The combination `n · σ = n₀ • X + n₁ • Y + n₂ • Z` for a real three-vector `n`. This is
Nielsen & Chuang's `n̂ · σ ≡ Σᵢ nᵢ σᵢ`. -/
def pauliDot (n : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (n 0 : ℂ) • pauliX + (n 1 : ℂ) • pauliY + (n 2 : ℂ) • pauliZ

/-- `n · σ` as a single explicit `2 × 2` matrix. -/
theorem pauliDot_eq (n : Fin 3 → ℝ) :
    pauliDot n =
      !![(n 2 : ℂ), (n 0 : ℂ) - (n 1 : ℂ) * I;
         (n 0 : ℂ) + (n 1 : ℂ) * I, -(n 2 : ℂ)] := by
  simp only [pauliDot, pauliX, pauliY, pauliZ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff]

/-- The `ẑ`-axis combination `ẑ · σ` is the Pauli `Z` matrix: `pauliDot ![0, 0, 1] = Z`. -/
theorem pauliDot_axisZ : pauliDot (![0, 0, 1] : Fin 3 → ℝ) = pauliZ := by
  rw [pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- `pauliDot` is additive in its vector argument. -/
theorem pauliDot_add (u w : Fin 3 → ℝ) : pauliDot (u + w) = pauliDot u + pauliDot w := by
  simp only [pauliDot, Pi.add_apply, Complex.ofReal_add]
  module

/-- `pauliDot` is ℝ-homogeneous in its vector argument (as a `ℂ`-scalar multiple). -/
theorem pauliDot_smul (a : ℝ) (u : Fin 3 → ℝ) :
    pauliDot (a • u) = (a : ℂ) • pauliDot u := by
  simp only [pauliDot, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  module

/-- `pauliDot` subtracts. -/
theorem pauliDot_sub (u w : Fin 3 → ℝ) : pauliDot (u - w) = pauliDot u - pauliDot w := by
  simp only [pauliDot, Pi.sub_apply, Complex.ofReal_sub]
  module

/-- `pauliDot` negates. -/
theorem pauliDot_neg (u : Fin 3 → ℝ) : pauliDot (-u) = -pauliDot u := by
  simp only [pauliDot, Pi.neg_apply, Complex.ofReal_neg]
  module

/-- `n · σ` is never the identity matrix: its diagonal `(n₂, −n₂)` cannot be `(1, 1)`
(`n₂ = 1` and `−n₂ = 1` are incompatible). A pure-matrix fact used to show the eigenprojectors
`½(1 ± n·σ)` are nonzero (Exercise 2.60). -/
theorem pauliDot_ne_one (n : Fin 3 → ℝ) : pauliDot n ≠ 1 := by
  intro hmat
  have e00 := congrFun (congrFun hmat 0) 0
  have e11 := congrFun (congrFun hmat 1) 1
  rw [pauliDot_eq] at e00 e11
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.one_apply_eq, Matrix.of_apply] at e00 e11
  rw [e00] at e11
  norm_num at e11

/-- `n · σ` is never `−1`: its diagonal `(n₂, −n₂)` cannot be `(−1, −1)` (`n₂ = −1` and `−n₂ = −1`
are incompatible). A pure-matrix fact used to show the eigenprojectors `½(1 ± n·σ)` are nonzero
(Exercise 2.60). -/
theorem pauliDot_ne_neg_one (n : Fin 3 → ℝ) : pauliDot n ≠ -1 := by
  intro hmat
  have e00 := congrFun (congrFun hmat 0) 0
  have e11 := congrFun (congrFun hmat 1) 1
  rw [pauliDot_eq] at e00 e11
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.neg_apply, Matrix.one_apply_eq, Matrix.of_apply] at e00 e11
  rw [e00] at e11
  norm_num at e11

/-- `n · σ` equals its own conjugate transpose (its entries are `n₂`, `n₀ ∓ i n₁`, `-n₂`,
each fixed by conjugation because `n` is real). -/
theorem pauliDot_conjTranspose (n : Fin 3 → ℝ) : (pauliDot n)ᴴ = pauliDot n := by
  rw [pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, Complex.ext_iff]

/-- `n · σ` is Hermitian, for any real three-vector `n` (Nielsen & Chuang, Exercise 2.19). -/
theorem pauliDot_isHermitian (n : Fin 3 → ℝ) : (pauliDot n).IsHermitian :=
  pauliDot_conjTranspose n

/-- `(n · σ)² = ‖n‖² • I`, where `‖n‖² = n₀² + n₁² + n₂²`. The cross terms cancel because the
Pauli matrices anticommute; the diagonal terms sum the squared components. -/
theorem pauliDot_mul_self (n : Fin 3 → ℝ) :
    pauliDot n * pauliDot n =
      (((n 0) ^ 2 + (n 1) ^ 2 + (n 2) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    push_cast <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

/-- For a unit vector `n` (`n₀² + n₁² + n₂² = 1`), `(n · σ)² = I`. This is the involution
property underlying the eigenprojectors `P± = (I ± n·σ)/2` and the functional calculus of
`θ n·σ`. -/
theorem pauliDot_mul_self_of_unit {n : Fin 3 → ℝ}
    (h : (n 0) ^ 2 + (n 1) ^ 2 + (n 2) ^ 2 = 1) :
    pauliDot n * pauliDot n = 1 := by
  rw [pauliDot_mul_self, h]; simp

/-! ### Each Pauli matrix is Hermitian and unitary (Nielsen & Chuang, Exercise 2.19)

N&C define an operator to be *Hermitian* when it equals its own adjoint (`σᴴ = σ`, here
`Matrix.IsHermitian`) and *unitary* when `σᴴ σ = I` (here membership in
`Matrix.unitaryGroup`). For each Pauli matrix both hold, and unitarity is a one-line
consequence of Hermiticity together with the involution `σ² = I`. -/

/-- Pauli `X` is an involution: `X² = I`. -/
theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli `Y` is an involution: `Y² = I`. The off-diagonal product `(-i)(i) = 1` fills the
diagonal, and the cross terms vanish. -/
theorem pauliY_mul_self : pauliY * pauliY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli `Z` is an involution: `Z² = I`. -/
theorem pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli `X` is Hermitian (`Xᴴ = X`); its entries `0, 1, 1, 0` are real. -/
theorem pauliX_isHermitian : pauliX.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]

/-- Pauli `Y` is Hermitian (`Yᴴ = Y`); conjugating and transposing swaps `∓i` back to
themselves (`conj (∓i) = ±i`). -/
theorem pauliY_isHermitian : pauliY.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.conjTranspose_apply]

/-- Pauli `Z` is Hermitian (`Zᴴ = Z`); its entries `1, 0, 0, -1` are real. -/
theorem pauliZ_isHermitian : pauliZ.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose_apply]

/-- Pauli `X` is unitary (`Xᴴ X = I`, i.e. `X ∈ unitaryGroup`), from Hermiticity and
`X² = I`. -/
theorem pauliX_mem_unitaryGroup : pauliX ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  pauliX_isHermitian.mem_unitaryGroup pauliX_mul_self

/-- Pauli `Y` is unitary (`Yᴴ Y = I`, i.e. `Y ∈ unitaryGroup`), from Hermiticity and
`Y² = I`. -/
theorem pauliY_mem_unitaryGroup : pauliY ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  pauliY_isHermitian.mem_unitaryGroup pauliY_mul_self

/-- Pauli `Z` is unitary (`Zᴴ Z = I`, i.e. `Z ∈ unitaryGroup`), from Hermiticity and
`Z² = I`. -/
theorem pauliZ_mem_unitaryGroup : pauliZ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  pauliZ_isHermitian.mem_unitaryGroup pauliZ_mul_self

/-! ### The Pauli matrices except `I` have trace zero (Nielsen & Chuang, Exercise 2.36)

The trace of a `2 × 2` matrix is the sum of its two diagonal entries. For `X` and `Y` both
diagonal entries are `0`; for `Z` they are `1` and `-1`, which cancel. Hence all three
non-identity Pauli matrices are traceless. The identity `σ₀ = I` is the sole exception: its
trace is `2` (`trace_one_fin_two`). -/

/-- Pauli `X` is traceless: `tr X = 0` (its diagonal entries are both `0`). -/
theorem pauliX_trace : pauliX.trace = 0 := by
  simp [pauliX, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- Pauli `Y` is traceless: `tr Y = 0` (its diagonal entries are both `0`). -/
theorem pauliY_trace : pauliY.trace = 0 := by
  simp [pauliY, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- Pauli `Z` is traceless: `tr Z = 0` (its diagonal entries `1` and `-1` cancel). -/
theorem pauliZ_trace : pauliZ.trace = 0 := by
  simp [pauliZ, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- The identity `σ₀ = I` is the exception in Nielsen & Chuang, Exercise 2.36: the `2 × 2`
identity matrix has trace `2`, hence is *not* traceless, unlike `X`, `Y`, `Z`. -/
theorem trace_one_fin_two : (1 : Matrix (Fin 2) (Fin 2) ℂ).trace = 2 := by
  simp [Matrix.trace_one]

/-! ### Anticommutation relations and the indexed Pauli family (Nielsen & Chuang, Exercise 2.41)

Exercise 2.41 asks to verify two relations. First the **anticommutation relations** (eq. 2.75)

`{σᵢ, σⱼ} = σᵢ σⱼ + σⱼ σᵢ = 0`   for `i ≠ j`, both drawn from `{1, 2, 3}` (i.e. `X`, `Y`, `Z`),

stated below as the three distinct unordered pairs; each product is `±i` times the remaining
Pauli matrix, and the two orders differ by a sign, so their sum vanishes. (`{·,·}` denotes the
anticommutator; we write it out as `A * B + B * A = 0` to match the textbook literally.)

Second, `σᵢ² = I` (eq. 2.76) for **all four** `i = 0, 1, 2, 3`. To capture N&C's indexed
statement uniformly — including `σ₀ = I` — we introduce the family `pauli : Fin 4 → M₂(ℂ)` with
`pauli 0 = I` and `pauli 1, 2, 3 = X, Y, Z`, and prove `pauli_mul_self` (`σᵢ² = I` for every `i`)
and `pauli_anticomm` (`{σᵢ, σⱼ} = 0` for distinct `i, j ≠ 0`, i.e. both in `{1, 2, 3}`, the
non-zero indices being exactly N&C's set). The per-matrix involutions `pauliX_mul_self`,
`pauliY_mul_self`, `pauliZ_mul_self` above supply the `i = 1, 2, 3` cases, and `1 * 1 = 1` the
`i = 0` case. -/

/-- Anticommutation of `X` and `Y` (Nielsen & Chuang, eq. 2.75): `{X, Y} = X Y + Y X = 0`.
`X Y = diag(i, -i)` and `Y X = diag(-i, i)`, so the sum is the zero matrix. -/
theorem pauliX_anticomm_pauliY : pauliX * pauliY + pauliY * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY]

/-- Anticommutation of `Y` and `Z` (Nielsen & Chuang, eq. 2.75): `{Y, Z} = Y Z + Z Y = 0`. -/
theorem pauliY_anticomm_pauliZ : pauliY * pauliZ + pauliZ * pauliY = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, pauliZ]

/-- Anticommutation of `X` and `Z` (Nielsen & Chuang, eq. 2.75): `{X, Z} = X Z + Z X = 0`. -/
theorem pauliX_anticomm_pauliZ : pauliX * pauliZ + pauliZ * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ]

/-- The Pauli matrices indexed by `Fin 4` in Nielsen & Chuang's convention: `σ₀ = I`, `σ₁ = X`,
`σ₂ = Y`, `σ₃ = Z`. This packages the four matrices as a single family so the exercise's
statements (`σᵢ² = I` for `i = 0, 1, 2, 3`; `{σᵢ, σⱼ} = 0` for `i ≠ j` from `{1, 2, 3}`) can be
expressed uniformly over the index. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![1, pauliX, pauliY, pauliZ]

/-- Every Pauli matrix is an involution (Nielsen & Chuang, eq. 2.76): `σᵢ² = I` for
`i = 0, 1, 2, 3`. For `i = 0` this is `I² = I`; for `i = 1, 2, 3` it is the per-matrix involution
of `X`, `Y`, `Z`. -/
theorem pauli_mul_self (i : Fin 4) : pauli i * pauli i = 1 := by
  fin_cases i <;>
    simp [pauli, pauliX_mul_self, pauliY_mul_self, pauliZ_mul_self]

/-- The anticommutation relations in indexed form (Nielsen & Chuang, eq. 2.75): for distinct
non-identity indices `i, j` — i.e. `i ≠ j`, both in `{1, 2, 3}`, expressed as `i, j ≠ 0` since
`0` is the sole excluded index of `Fin 4` — the anticommutator vanishes, `σᵢ σⱼ + σⱼ σᵢ = 0`.
The identity `σ₀ = I` is excluded because `{I, σ} = 2σ ≠ 0`, and the equal-index diagonal because
`{σ, σ} = 2σ² = 2I ≠ 0`. -/
theorem pauli_anticomm {i j : Fin 4} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    pauli i * pauli j + pauli j * pauli i = 0 := by
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hi
      | exact absurd rfl hj
      | exact absurd rfl hij
      | (ext a b; fin_cases a <;> fin_cases b <;> simp [pauli, pauliX, pauliY, pauliZ])

/-- Each indexed Pauli matrix is Hermitian: `σᵢᴴ = σᵢ` for `i = 0, 1, 2, 3`. For `i = 0` this is
`Iᴴ = I` (`Matrix.isHermitian_one`); for `i = 1, 2, 3` it is `pauliX/Y/Z_isHermitian`. -/
theorem pauli_isHermitian (m : Fin 4) : (pauli m).IsHermitian := by
  fin_cases m
  · exact Matrix.isHermitian_one
  · exact pauliX_isHermitian
  · exact pauliY_isHermitian
  · exact pauliZ_isHermitian

/-- Entrywise Hermiticity of a Pauli matrix: `conj (σₘ a b) = σₘ b a`, read off `pauli_isHermitian`
via `Matrix.conjTranspose_apply`. -/
theorem pauli_conj_apply (m : Fin 4) (a b : Fin 2) : star (pauli m a b) = pauli m b a := by
  have h := congrFun (congrFun (pauli_isHermitian m) b) a
  rwa [Matrix.conjTranspose_apply] at h

/-- **Single-qubit trace orthogonality** (the `d = 2` case of Nielsen & Chuang, Exercise 2.39):
`tr(σᵢ σⱼ) = 2 δᵢⱼ`. Since each `σ` is an involution (`σ² = I`), the diagonal case gives `tr I = 2`;
the off-diagonal products are traceless. This is the `n = 1` case of the Hilbert–Schmidt
orthogonality of the `n`-fold Pauli strings (`Concrete.pauliString_trace_mul`). -/
theorem pauli_trace_mul (i j : Fin 4) :
    (pauli i * pauli j).trace = if i = j then (2 : ℂ) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [pauli, pauliX, pauliY, pauliZ, Matrix.trace_fin_two, Complex.ext_iff] <;> norm_num

end AxQM.Concrete
