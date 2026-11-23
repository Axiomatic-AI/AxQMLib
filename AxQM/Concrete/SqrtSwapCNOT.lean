/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HeisenbergSwap
import AxQM.Concrete.AxisAngleGateValues

/-!
# Concrete: universality of `√SWAP` — a `CNOT` from `√SWAP` and single-qubit gates

*Nielsen & Chuang, Exercise 7.52 (Universality of the Heisenberg Hamiltonian), Part 3.*

Parts 1 and 2 (`AxQM/Concrete/HeisenbergSwap.lean`) built, from the Heisenberg exchange evolution
`exp(−iφ S⃗₁·S⃗₂)`, the swap operation (`heisenbergEvolution_pi`) and the `√SWAP` gate
`sqrtSwapHeis = exp(−i(π/2) S⃗₁·S⃗₂)` in closed form. This file discharges the final clause of the
exercise: **`√SWAP` together with single-qubit operations is universal** — it composes into a
controlled-`NOT`.

Everything is pure `2⊗2 = 4`-dimensional complex-matrix mathematics: every statement
names only concrete matrices (`sqrtSwapHeis`, the swap matrix, the phase gate `sMatrix`, the
Hadamard `hadamardC`, `pauliZ`) and `Complex.exp`. The statement of the exercise is in
`AxQM/NC/Ch7/Exercise7_52.lean`.

## The construction

Write `√SWAP = sqrtSwapHeis`, `S = sMatrix = diag(1, i)`, `S† = diag(1, −i)`, `Z = pauliZ`,
`H = hadamardC`, and let `A ⊗ B` act as `A` on qubit 1, `B` on qubit 2. The controlled-`Z` gate is
obtained from two `√SWAP`s, a middle `Z` on qubit 1, and a pair of single-qubit phase corrections:

`(S ⊗ S†) · √SWAP · (Z ⊗ 1) · √SWAP = e^{−iπ/4} · CZ`   (`sqrtSwapHeis_controlledZ`),

and conjugating the target qubit of `CZ` by a Hadamard turns it into `CNOT`
(`hadamardC_conj_twoQubitCZ`, the standard `CZ ↦ CNOT` identity). Composing,

`(1 ⊗ H) · (S ⊗ S†) · √SWAP · (Z ⊗ 1) · √SWAP · (1 ⊗ H) = e^{−iπ/4} · CNOT`
(`sqrtSwapHeisCNOT_eq`, the headline).

The global phase `e^{−iπ/4}` is physically irrelevant, so this is exactly a `CNOT` built from
`√SWAP` and single-qubit gates — Exercise 7.52's universality claim.

## Proof strategy

Substitute the Part-2 closed form `sqrtSwapHeis = heisPhase • (1 − i·SWAP)`
(`sqrtSwapHeis_eq_smul`, `heisPhase = e^{iπ/8}·(√2/2)`). The two `√SWAP`s contribute `heisPhase²`,
pulled out as a scalar; the remaining product of the **un-phased** factor `(1 − i·SWAP)` with
`(Z ⊗ 1)` and the phase corrections is a *Gaussian-integer* `4×4` matrix identity
`(S ⊗ S†)·(1 − i·SWAP)·(Z ⊗ 1)·(1 − i·SWAP) = −2i · CZ`
(`sPhaseKron_mul_swapExpr_mul_pauliZKron_mul_swapExpr`), verified entrywise. The two transcendental
scalars combine cleanly: `heisPhase² · (−2i) = e^{−iπ/4}` (`heisPhase_sq_mul_neg_two_I`).
-/

open Matrix
open scoped Kronecker

namespace AxQM.Concrete

/-- The **two-qubit controlled-`Z` gate** `CZ = diag(1, 1, 1, −1)` on `Fin 2 × Fin 2`: it flips the
sign of `|11⟩` and fixes every other computational basis state. Symmetric between control and
target. -/
noncomputable def twoQubitCZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal fun p => if p = ((1 : Fin 2), (1 : Fin 2)) then -1 else 1

/-- Entrywise form of `CZ`: `CZ i j = 1` on the diagonal except `CZ (1,1) (1,1) = −1`, and `0`
off-diagonal. -/
theorem twoQubitCZ_apply (i j : Fin 2 × Fin 2) :
    twoQubitCZ i j = if i = j then (if i = ((1 : Fin 2), (1 : Fin 2)) then -1 else 1) else 0 := by
  simp [twoQubitCZ, Matrix.diagonal_apply]

/-- The **two-qubit controlled-`NOT` gate** `CNOT` on `Fin 2 × Fin 2` with qubit 1 the control and
qubit 2 the target: `CNOT |a, b⟩ = |a, a + b⟩` (flip the target iff the control is `|1⟩`). A real
permutation matrix. -/
noncomputable def twoQubitCNOT : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j => if i = (j.1, j.1 + j.2) then 1 else 0

/-- Entrywise form of `CNOT`: `CNOT i j = 1` iff `i = (j.1, j.1 + j.2)` (the `+`-on-`Fin 2` flip of
the target by the control), else `0`. -/
theorem twoQubitCNOT_apply (i j : Fin 2 × Fin 2) :
    twoQubitCNOT i j = if i = (j.1, j.1 + j.2) then 1 else 0 := rfl

/-- The two-qubit **CNOT is Hermitian**, `CNOTᴴ = CNOT`: it is the real symmetric permutation
matrix of the involutive basis map `|a, b⟩ ↦ |a, a + b⟩`. -/
theorem twoQubitCNOT_conjTranspose : twoQubitCNOTᴴ = twoQubitCNOT := by
  ext i j
  obtain ⟨i1, i2⟩ := i; obtain ⟨j1, j2⟩ := j
  simp only [Matrix.conjTranspose_apply, twoQubitCNOT_apply]
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp

/-- The two-qubit **CNOT is an involution**, `CNOT² = I`: applying `|a, b⟩ ↦ |a, a + b⟩` twice
restores the state (`a + (a + b) = b` in `Fin 2`). -/
theorem twoQubitCNOT_mul_self : twoQubitCNOT * twoQubitCNOT = 1 := by
  ext i j
  obtain ⟨i1, i2⟩ := i; obtain ⟨j1, j2⟩ := j
  simp only [Matrix.mul_apply, twoQubitCNOT_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp

/-- The two-qubit **CNOT is unitary** (`CNOTᴴ CNOT = I`, i.e. membership in `Matrix.unitaryGroup`),
immediate from being Hermitian (`twoQubitCNOT_conjTranspose`) and an involution
(`twoQubitCNOT_mul_self`). -/
theorem twoQubitCNOT_mem_unitaryGroup :
    twoQubitCNOT ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  Matrix.IsHermitian.mem_unitaryGroup twoQubitCNOT_conjTranspose twoQubitCNOT_mul_self

/-- Entrywise form of `S† = diag(1, −i)`: the adjoint of the phase gate `S = sMatrix = diag(1, i)`
is `!![1, 0; 0, −i]`. -/
theorem sMatrix_conjTranspose : sMatrix.conjTranspose = !![1, 0; 0, -Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sMatrix, Matrix.conjTranspose_apply]

/-- **`S† = S³`: the phase gate is a fourth root of unity.**
`sMatrixᴴ = sMatrix · sMatrix · sMatrix` — both sides are `diag(1, -i)` (`S = diag(1, i)`,
`i³ = -i = conj i`); a `2 × 2` entrywise computation. Expresses the adjoint phase gate `S†` as a
product of the phase gate `S`, so `S†` lies in the monoid generated by `S` — the reuse the Deutsch
single-qubit submonoid's `{S, S†}` generators need. -/
theorem sMatrix_conjTranspose_eq_mul_self_mul_self :
    sMatrix.conjTranspose = sMatrix * sMatrix * sMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.I_mul_I]

/-- The **global-phase scalar** `heisPhase = e^{iπ/8}·(√2/2)` of the `√SWAP` closed form: the value
`c` for which `sqrtSwapHeis = c·(1 − i·SWAP)` (see `sqrtSwapHeis_eq_smul`). -/
noncomputable def heisPhase : ℂ :=
  Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) * ((Real.sqrt 2 / 2 : ℝ) : ℂ)

/-- **The `√SWAP` closed form as a single scalar multiple of `1 − i·SWAP`.** Refactoring
`sqrtSwapHeis_eq`, `sqrtSwapHeis = heisPhase • (1 − i·SWAP)` with `heisPhase = e^{iπ/8}·(√2/2)`.
This is the convenient form for the universality computation: the two `√SWAP`s then contribute the
single scalar `heisPhase²`. -/
theorem sqrtSwapHeis_eq_smul :
    sqrtSwapHeis = heisPhase • ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      - Complex.I • twoQubitSwap) := by
  rw [sqrtSwapHeis_eq, heisPhase]
  module

/-- **The two transcendental phases collapse:** `heisPhase² · (−2i) = e^{−iπ/4}`. Indeed
`heisPhase² = (e^{iπ/8})²·(√2/2)² = e^{iπ/4}·½`, so `heisPhase²·(−2i) = e^{iπ/4}·(−i) = e^{−iπ/4}`.
This is where the `e^{iπ/8}` global phase of the Heisenberg `√SWAP` and the `−2i` from the
Gaussian-integer core produce the physical `e^{−iπ/4}` of the `CNOT` construction. -/
theorem heisPhase_sq_mul_neg_two_I :
    heisPhase ^ 2 * (-2 * Complex.I) = Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I) := by
  have hsq : ((Real.sqrt 2 / 2 : ℝ) : ℂ) ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hnI : (1 / 2 : ℂ) * (-2 * Complex.I)
      = Complex.exp (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast; ring
  rw [heisPhase, mul_pow, hsq, pow_two, ← Complex.exp_add, mul_assoc, hnI, ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- **The Gaussian-integer core of the controlled-`Z` construction.** Sandwiching `(Z ⊗ 1)` between
two copies of the un-phased `√SWAP` factor `(1 − i·SWAP)` and applying the single-qubit phase
corrections `S = diag(1, i)` on qubit 1 and `S† = diag(1, −i)` on qubit 2 yields `−2i · CZ`:
`(S ⊗ S†)·(1 − i·SWAP)·(Z ⊗ 1)·(1 − i·SWAP) = −2i · CZ`. Every entry is a Gaussian integer, so this
is a finite entrywise verification; the `√2`/`e^{iπ/8}` factors of the true `√SWAP` are carried
separately as the scalar `heisPhase²`. -/
theorem sPhaseKron_mul_swapExpr_mul_pauliZKron_mul_swapExpr :
    (sMatrix ⊗ₖ sMatrix.conjTranspose)
        * ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - Complex.I • twoQubitSwap)
        * (pauliZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
        * ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - Complex.I • twoQubitSwap)
      = (-2 * Complex.I) • twoQubitCZ := by
  rw [sMatrix_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoQubitSwap_apply, twoQubitCZ_apply, sMatrix, pauliZ, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.sub_apply, Matrix.smul_apply, Prod.ext_iff] <;>
    norm_num [Complex.ext_iff]

/-- **Nielsen & Chuang, Exercise 7.52, Part 3 (controlled-`Z` from `√SWAP`).** Two `√SWAP`s, a
central `Z` on qubit 1, and the single-qubit phase corrections `S ⊗ S†` compose into the
controlled-`Z` gate, up to the physically irrelevant global phase `e^{−iπ/4}`:
`(S ⊗ S†) · √SWAP · (Z ⊗ 1) · √SWAP = e^{−iπ/4} · CZ`. -/
theorem sqrtSwapHeis_controlledZ :
    (sMatrix ⊗ₖ sMatrix.conjTranspose) * sqrtSwapHeis * (pauliZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
        * sqrtSwapHeis
      = Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I) • twoQubitCZ := by
  rw [sqrtSwapHeis_eq_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [sPhaseKron_mul_swapExpr_mul_pauliZKron_mul_swapExpr, smul_smul, ← pow_two,
    heisPhase_sq_mul_neg_two_I]

/-- **Conjugating the target qubit of `CZ` by a Hadamard gives `CNOT`.** `(1 ⊗ H) · CZ · (1 ⊗ H) =
CNOT` — the standard identity turning a controlled-`Z` into a controlled-`NOT`, since `H Z H = X`
on the target. -/
theorem hadamardC_conj_twoQubitCZ :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ hadamardC) * twoQubitCZ
        * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ hadamardC)
      = twoQubitCNOT := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoQubitCZ_apply, twoQubitCNOT_apply, hadamardC, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, Prod.ext_iff] <;>
    norm_num [inv_sqrt_two_mul_self]

/-- The **`√SWAP` implementation of `CNOT`**: the explicit circuit conjugating the controlled-`Z`
construction `(S ⊗ S†) · √SWAP · (Z ⊗ 1) · √SWAP` by a Hadamard on the target qubit. By
`sqrtSwapHeisCNOT_eq` it equals `CNOT` up to a global phase — Exercise 7.52's universality of the
Heisenberg `√SWAP`. -/
noncomputable def sqrtSwapHeisCNOT : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ hadamardC)
    * ((sMatrix ⊗ₖ sMatrix.conjTranspose) * sqrtSwapHeis
        * (pauliZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * sqrtSwapHeis)
    * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ hadamardC)

/-- **Nielsen & Chuang, Exercise 7.52, Part 3 (the universality of `√SWAP`).** The `√SWAP` gate of
the Heisenberg exchange interaction, composed with single-qubit gates, implements a
controlled-`NOT`: `sqrtSwapHeisCNOT = e^{−iπ/4} · CNOT`. Since the global phase `e^{−iπ/4}` is
physically irrelevant,
`√SWAP` is universal — the concluding claim of Exercise 7.52.

Proof: the middle bracket is `e^{−iπ/4} · CZ` (`sqrtSwapHeis_controlledZ`), and Hadamard-conjugating
the target turns `CZ` into `CNOT` (`hadamardC_conj_twoQubitCZ`); the scalar factors through. -/
theorem sqrtSwapHeisCNOT_eq :
    sqrtSwapHeisCNOT = Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I) • twoQubitCNOT := by
  rw [sqrtSwapHeisCNOT, sqrtSwapHeis_controlledZ, Matrix.mul_smul, Matrix.smul_mul,
    hadamardC_conj_twoQubitCZ]

end AxQM.Concrete
