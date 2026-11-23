/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Data.Real.Sqrt
import AxQM.Concrete.PauliKronecker

/-!
# Concrete: the spin-flip channel and its operator-sum representation (N&C, Exercise 8.5)

This file computes the operator-sum
(Kraus) representation of the single-qubit quantum operation obtained from the two-qubit
"spin-flip" interaction of Nielsen & Chuang, Exercise 8.5 (p. 361). The statement of the exercise
is in `AxQM/NC/Ch8/Exercise8_5.lean`.

## The exercise

A single-qubit principal system interacts with a single-qubit environment, prepared in the state
`|0⟩`, through the unitary (eq. 8.17)

`U = X/√2 ⊗ I + Y/√2 ⊗ X`,

where the first tensor factor acts on the system and the second on the environment. The exercise
asks for the resulting quantum operation `E(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†)` in the operator-sum
representation `E(ρ) = Σₖ Eₖ ρ Eₖ†`, with operation elements `Eₖ = ⟨eₖ|U|e₀⟩` (N&C eqs. 8.9–8.10).

Reading `Eₖ = ⟨k|U|0⟩` off `U` (the environment matrix element at `|0⟩`) gives

`E₀ = X/√2`,   `E₁ = Y/√2`,

so the operation is the equal-weight bit-and-phase mixture `E(ρ) = ½ XρX + ½ YρY`, a genuine
(trace-preserving) quantum operation.

## Contents

* `matrixPartialTraceRight` — the partial trace over the second (environment) tensor factor of a
  `(a × b)`-indexed matrix, `(tr_env M) i j = Σₑ M (i,e) (j,e)`, packaged as a `ℂ`-linear map; with
  `matrixPartialTraceRight_kronecker` (`tr_env (M ⊗ₖ N) = tr(N) • M`) fixing it as the genuine
  partial trace.
* `spinFlipScale` — the scalar `1/√2`, with `spinFlipScale_mul_self` (`(1/√2)² = 1/2`).
* `spinFlipU` — the interaction unitary `U = (X/√2) ⊗ I + (Y/√2) ⊗ X`, with `spinFlipU_isHermitian`,
  `spinFlipU_mul_self` (`U² = I`), and `spinFlipU_mem_unitaryGroup` (`U` is unitary).
* `spinFlipKraus` — the operation elements `E₀ = X/√2`, `E₁ = Y/√2`, with
  `spinFlipKraus_eq_matrixElement` deriving them as the environment matrix elements `⟨k|U|0⟩` of `U`
  (N&C eq. 8.10), and `spinFlipKraus_completeness` the completeness relation `Σₖ Eₖ† Eₖ = I`.
* `spinFlipChannel` — the quantum operation `E(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†)`, with:
  * `spinFlipChannel_eq_kraus` — the **operator-sum representation** `E(ρ) = Σₖ Eₖ ρ Eₖ†`;
  * `spinFlipChannel_eq` — the explicit closed form `E(ρ) = ½ XρX + ½ YρY`.

## Design notes

* **Faithfulness.** The operator-sum representation is proved as the identity between the physical
  reduced dynamics `tr_env(U (ρ ⊗ |0⟩⟨0|) U†)` (the left-hand side of N&C eq. 8.9) and the sum
  `Σₖ Eₖ ρ Eₖ†` (eq. 8.10), for an arbitrary input `ρ` — not merely a computation of the operation
  elements. The operation elements are additionally certified to be the environment matrix elements
  `⟨k|U|0⟩` of `U`, so they are *derived* from `U` in the way N&C prescribes rather than posited.
* **Matrix-level, structural proofs.** The unitary `U` is represented as a Kronecker sum of Pauli
  matrices, `ρ ⊗ |0⟩⟨0|` via `Matrix.kroneckerMap`, and the reduced dynamics via
  `matrixPartialTraceRight`; the operator-sum identity is then a structural computation using the
  Kronecker mixed-product rule `Matrix.mul_kronecker_mul`, the Pauli involution/anticommutation
  relations from `Concrete.Pauli`, and `matrixPartialTraceRight_kronecker`, with no entrywise
  brute force. `U` is Hermitian and an involution (`U² = I`), so its unitarity reduces to
  `Matrix.IsHermitian.mem_unitaryGroup` exactly as for the individual Pauli matrices.
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

/-- The **partial trace over the second (environment) tensor factor** of a matrix indexed by a
product type `a × b`: `(tr_env M) i j = Σₑ M (i, e) (j, e)`, i.e. `Σₑ (I ⊗ ⟨e|) M (I ⊗ |e⟩)` read
entrywise. Packaged as a `ℂ`-linear map so that `map_add`, `map_smul`, `map_sum` are available; its
defining property `tr_env (M ⊗ₖ N) = tr(N) • M` is `matrixPartialTraceRight_kronecker`. -/
def matrixPartialTraceRight {a b : Type*} [Fintype b] :
    Matrix (a × b) (a × b) ℂ →ₗ[ℂ] Matrix a a ℂ where
  toFun M := Matrix.of fun i j => ∑ e, M (i, e) (j, e)
  map_add' M N := by ext i j; simp [Finset.sum_add_distrib]
  map_smul' c M := by ext i j; simp [Finset.mul_sum]

@[simp]
theorem matrixPartialTraceRight_apply {a b : Type*} [Fintype b]
    (M : Matrix (a × b) (a × b) ℂ) (i j : a) :
    matrixPartialTraceRight M i j = ∑ e, M (i, e) (j, e) := rfl

/-- **The partial trace over the second factor of a Kronecker product**: `tr_env (M ⊗ₖ N) =
tr(N) • M`. This is the characterizing property that identifies `matrixPartialTraceRight` as the
genuine partial trace: tracing out the environment factor `N` returns the system factor `M` scaled
by `tr(N)`. -/
theorem matrixPartialTraceRight_kronecker {a b : Type*} [Fintype b]
    (M : Matrix a a ℂ) (N : Matrix b b ℂ) :
    matrixPartialTraceRight (M ⊗ₖ N) = N.trace • M := by
  ext i j
  simp only [matrixPartialTraceRight_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.trace, Matrix.diag_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- The scalar `1/√2 = (√2)⁻¹` (as a complex number), the amplitude appearing in the spin-flip
interaction `U = (X/√2) ⊗ I + (Y/√2) ⊗ X`. -/
noncomputable def spinFlipScale : ℂ := (Real.sqrt 2)⁻¹

/-- `(1/√2)² = 1/2`: the squared amplitude, used to normalize the operator sum. -/
theorem spinFlipScale_mul_self : spinFlipScale * spinFlipScale = 1 / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [spinFlipScale, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv, h2]
  push_cast
  norm_num

/-- The amplitude `1/√2` is real, hence fixed by complex conjugation: `star (1/√2) = 1/√2`. -/
theorem spinFlipScale_star : star spinFlipScale = spinFlipScale := by
  rw [spinFlipScale, ← Complex.ofReal_inv]
  exact Complex.conj_ofReal _

/-- The **spin-flip interaction unitary** (Nielsen & Chuang, eq. 8.17):
`U = (X/√2) ⊗ I + (Y/√2) ⊗ X`, where the first Kronecker factor acts on the system and the second
on the environment. Both `X ⊗ I` and `Y ⊗ X` are Hermitian, so `U` is Hermitian; the Pauli
anticommutation `{X, Y} = 0` makes it an involution, hence unitary. -/
noncomputable def spinFlipU : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  spinFlipScale • (pauliX ⊗ₖ pauliI) + spinFlipScale • (pauliY ⊗ₖ pauliX)

/-- The **operation elements** (Kraus operators) of the spin-flip channel: `E₀ = X/√2` and
`E₁ = Y/√2` (Nielsen & Chuang, eq. 8.17). These are the environment matrix elements `⟨k|U|0⟩` of
`U` (`spinFlipKraus_eq_matrixElement`). -/
noncomputable def spinFlipKraus : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![spinFlipScale • pauliX, spinFlipScale • pauliY]

/-- The **spin-flip quantum operation** `E(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†)`: the reduced dynamics of
the principal qubit when it interacts with an environment prepared in `|0⟩` via `U` and the
environment is then discarded (Nielsen & Chuang, eq. 8.9). -/
noncomputable def spinFlipChannel (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  matrixPartialTraceRight (spinFlipU * (ρ ⊗ₖ ketBra 0 0) * spinFlipUᴴ)

@[simp] theorem spinFlipKraus_zero : spinFlipKraus 0 = spinFlipScale • pauliX := rfl

@[simp] theorem spinFlipKraus_one : spinFlipKraus 1 = spinFlipScale • pauliY := rfl

/-- **`U` is Hermitian.** Both summands `X ⊗ I` and `Y ⊗ X` are Hermitian (Kronecker products of
Hermitian Pauli matrices) and the amplitude `1/√2` is real, so `Uᴴ = U`. -/
theorem spinFlipU_isHermitian : spinFlipU.IsHermitian := by
  have hX : pauliXᴴ = pauliX := pauliX_isHermitian
  have hY : pauliYᴴ = pauliY := pauliY_isHermitian
  have hI : pauliIᴴ = pauliI := Matrix.conjTranspose_one
  unfold Matrix.IsHermitian spinFlipU
  simp only [conjTranspose_add, conjTranspose_smul, Matrix.conjTranspose_kronecker, hX, hY, hI,
    spinFlipScale_star]

/-- **`U² = I`.** Expanding `U² = ½[(X⊗I)² + (XY+YX)⊗X + (Y⊗X)²]`, the cross term vanishes by the
Pauli anticommutation `{X, Y} = 0`, and `(X⊗I)² = (Y⊗X)² = I`, so `U² = ½·2·I = I`. -/
theorem spinFlipU_mul_self : spinFlipU * spinFlipU = 1 := by
  have hPP : (pauliX ⊗ₖ pauliI) * (pauliX ⊗ₖ pauliI) = 1 := by
    rw [← Matrix.mul_kronecker_mul, pauliX_mul_self]
    simp only [pauliI, one_mul, Matrix.one_kronecker_one]
  have hQQ : (pauliY ⊗ₖ pauliX) * (pauliY ⊗ₖ pauliX) = 1 := by
    rw [← Matrix.mul_kronecker_mul, pauliY_mul_self, pauliX_mul_self, Matrix.one_kronecker_one]
  have hcross : (pauliX ⊗ₖ pauliI) * (pauliY ⊗ₖ pauliX)
      + (pauliY ⊗ₖ pauliX) * (pauliX ⊗ₖ pauliI) = 0 := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [pauliI, one_mul, mul_one, ← Matrix.add_kronecker, pauliX_anticomm_pauliY,
      Matrix.zero_kronecker]
  have expand : spinFlipU * spinFlipU = (1 / 2 : ℂ) • ((pauliX ⊗ₖ pauliI) * (pauliX ⊗ₖ pauliI)
      + ((pauliX ⊗ₖ pauliI) * (pauliY ⊗ₖ pauliX) + (pauliY ⊗ₖ pauliX) * (pauliX ⊗ₖ pauliI))
      + (pauliY ⊗ₖ pauliX) * (pauliY ⊗ₖ pauliX)) := by
    rw [spinFlipU]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      spinFlipScale_mul_self, smul_add]
    abel
  rw [expand, hPP, hQQ, hcross]
  module

/-- **`U` is unitary** (`U ∈ unitaryGroup`), from `Matrix.IsHermitian.mem_unitaryGroup` applied to
the Hermitian involution `U`: a Hermitian matrix squaring to `I` is unitary. This certifies that
`E(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†)` is a genuine reduced dynamics of a closed two-qubit evolution. -/
theorem spinFlipU_mem_unitaryGroup : spinFlipU ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  spinFlipU_isHermitian.mem_unitaryGroup spinFlipU_mul_self

/-- **The operation elements are the environment matrix elements of `U`** (Nielsen & Chuang,
eq. 8.10): `Eₖ = ⟨k|U|0⟩`, read entrywise as `(Eₖ) i j = U (i, k) (j, 0)`. This is the derivation of
`E₀ = X/√2`, `E₁ = Y/√2`: contracting the environment slot of `U` against `⟨k|` on the left and
`|0⟩` on the right selects the `k`-th operation element. -/
theorem spinFlipKraus_eq_matrixElement (k i j : Fin 2) :
    spinFlipKraus k i j = spinFlipU (i, k) (j, 0) := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [spinFlipU, spinFlipKraus, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.kroneckerMap_apply, pauliI, pauliX, pauliY]

/-- **The completeness relation** (Nielsen & Chuang, eq. 8.14): `Σₖ Eₖ† Eₖ = I`. Since each `Eₖ =
(1/√2)·σ` with `σ` a Hermitian involution, `Eₖ† Eₖ = (1/2)·σ² = (1/2)·I`, and the two terms sum to
`I`. This certifies the spin-flip operation is trace preserving. -/
theorem spinFlipKraus_completeness :
    ∑ k, (spinFlipKraus k)ᴴ * spinFlipKraus k = 1 := by
  have hX : pauliXᴴ = pauliX := pauliX_isHermitian
  have hY : pauliYᴴ = pauliY := pauliY_isHermitian
  rw [Fin.sum_univ_two, spinFlipKraus_zero, spinFlipKraus_one]
  simp only [conjTranspose_smul, hX, hY, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    spinFlipScale_star, spinFlipScale_mul_self, pauliX_mul_self, pauliY_mul_self]
  module

/-! ### The operator-sum representation

The two products of `X` with `|0⟩⟨0|` (and `|1⟩⟨0|`) that arise when conjugating `ρ ⊗ |0⟩⟨0|` by
`U`, expressed in the outer-product basis. -/

private theorem pauliX_mul_ketBra_zero_zero : pauliX * ketBra 0 0 = ketBra 1 0 := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [pauliX, ketBra_apply, Matrix.mul_apply]

private theorem ketBra_zero_zero_mul_pauliX : ketBra 0 0 * pauliX = ketBra 0 1 := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [pauliX, ketBra_apply, Matrix.mul_apply]

private theorem ketBra_one_zero_mul_pauliX : ketBra 1 0 * pauliX = ketBra 1 1 := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [pauliX, ketBra_apply, Matrix.mul_apply]

private theorem ketBra_trace (i j : Fin 2) : (ketBra i j).trace = if i = j then 1 else 0 := by
  rw [ketBra_eq_single]; fin_cases i <;> fin_cases j <;> simp [Matrix.trace, Matrix.diag]

/-- **The spin-flip channel in closed form**: `E(ρ) = ½ XρX + ½ YρY`. Conjugating `ρ ⊗ |0⟩⟨0|` by
`U` and tracing out the environment: the mixed-product rule reduces `U (ρ ⊗ |0⟩⟨0|) U†` to a
Kronecker sum whose environment factors are `|0⟩⟨0|`, `|0⟩⟨1|`, `|1⟩⟨0|`, `|1⟩⟨1|`; only the two
diagonal ones survive the partial trace (`tr|0⟩⟨1| = tr|1⟩⟨0| = 0`), leaving
`(1/√2)²(XρX) + (1/√2)²(YρY) = ½ XρX + ½ YρY`. -/
theorem spinFlipChannel_eq (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinFlipChannel ρ =
      (1 / 2 : ℂ) • (pauliX * ρ * pauliX) + (1 / 2 : ℂ) • (pauliY * ρ * pauliY) := by
  rw [spinFlipChannel, spinFlipU_isHermitian, spinFlipU]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  -- fold each three-fold product into a single Kronecker product (mixed-product rule)
  simp only [← Matrix.mul_kronecker_mul]
  -- simplify the environment factors `I·|0⟩⟨0|·I`, `I·|0⟩⟨0|·X`, `X·|0⟩⟨0|·I`, `X·|0⟩⟨0|·X`
  simp only [pauliI, one_mul, mul_one, pauliX_mul_ketBra_zero_zero, ketBra_zero_zero_mul_pauliX,
    ketBra_one_zero_mul_pauliX]
  -- push the partial trace through; only the diagonal environment factors survive
  simp only [map_add, map_smul, matrixPartialTraceRight_kronecker, ketBra_trace]
  norm_num
  simp only [smul_smul, spinFlipScale_mul_self]

/-- **The operator-sum (Kraus) representation of the spin-flip channel** (Nielsen & Chuang,
eqs. 8.9–8.10 for Exercise 8.5): the reduced dynamics equals the sum over the operation elements,
`E(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†) = Σₖ Eₖ ρ Eₖ†`, with `E₀ = X/√2`, `E₁ = Y/√2`. This is the answer
the exercise asks for: the spin-flip interaction produces the operator-sum quantum operation with
these two operation elements. -/
theorem spinFlipChannel_eq_kraus (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinFlipChannel ρ = ∑ k, spinFlipKraus k * ρ * (spinFlipKraus k)ᴴ := by
  rw [spinFlipChannel_eq, Fin.sum_univ_two, spinFlipKraus_zero, spinFlipKraus_one]
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [pauliX_isHermitian, pauliY_isHermitian]
  simp only [spinFlipScale_star, spinFlipScale_mul_self]

end AxQM.Concrete
