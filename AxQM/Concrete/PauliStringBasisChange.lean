/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliString
import AxQM.Concrete.HadamardPauliConjugation
import AxQM.Concrete.AxisAngleGateValues
import ToMathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Concrete: local single-qubit basis change reducing `X ⊗ Y ⊗ Z` to `Z ⊗ Z ⊗ Z`

This file supplies the matrix core of Nielsen & Chuang, **Exercise 4.51** — "construct a quantum
circuit to simulate the Hamiltonian `H = X₁ ⊗ Y₂ ⊗ Z₃`, performing `e^{-iΔt H}` for any `Δt`".
The exercise statement is in `AxQM/NC/Ch4/Exercise4_51.lean`.

## The construction (N&C §4.7.3)

N&C's simulation algorithm reduces any tensor-product Pauli Hamiltonian `⊗ₖ σ_{c(k)}` to the
all-`Z` case `Z ⊗ ⋯ ⊗ Z` (whose `e^{-iΔt}` circuit is Figure 4.19, a parity computation into an
ancilla, a conditional phase, and an uncompute) by **single-qubit basis changes**: an `X` or `Y`
factor is conjugated to a `Z` factor by a local unitary. Concretely, with

* `B₁ = H` (Hadamard):    `H · Z · Hᴴ = X`   (`hadamardC_mul_pauliZ_mul_hadamardC`);
* `B₂ = S·H` (`basisChangeY`): `(SH) · Z · (SH)ᴴ = Y`  (`basisChangeY_conj_pauliZ`);
* `B₃ = I`:                `I · Z · Iᴴ = Z`,

the local tensor unitary `B = B₁ ⊗ B₂ ⊗ B₃` satisfies `B · (Z ⊗ Z ⊗ Z) · Bᴴ = X ⊗ Y ⊗ Z`, and
hence, for any complex scalar `s` (in the exercise `s = -iΔt`),
`exp(s · (X ⊗ Y ⊗ Z)) = B · exp(s · (Z ⊗ Z ⊗ Z)) · Bᴴ`. Applying `B` locally, running the `Z⊗Z⊗Z`
simulation, and undoing `B` is the circuit for `e^{-iΔt H}`.

## What is proved

* `kronFamily` — the `n`-fold tensor product `⨂ₖ Aₖ` of a family of single-qubit operators,
  defined entrywise `(⨂ₖ Aₖ)(i,j) = ∏ₖ Aₖ(iₖ)(jₖ)` on the register index `Fin n → Fin 2`,
  matching the entrywise form of `pauliString` (so `pauliString g = ⨂ₖ σ_{gₖ}`,
  `pauliString_eq_kronFamily`).
* `kronFamily_mul` — the **mixed-product property** `(⨂ₖ Aₖ)(⨂ₖ Bₖ) = ⨂ₖ (Aₖ Bₖ)`, the
  algebraic engine of the reduction; `kronFamily_conjTranspose` (`(⨂ₖ Aₖ)ᴴ = ⨂ₖ Aₖᴴ`),
  `kronFamily_one` (`⨂ₖ 1 = 1`) and `kronFamily_smul_family` (`⨂ₖ (cₖ • Aₖ) = (∏ₖ cₖ) • ⨂ₖ Aₖ`)
  are its unit/adjoint/scalar companions.
* `basisChangeY` / `sMatrix_conj_pauliX` / `sMatrix_conj_pauliY` / `sMatrix_conj_pauliZ` /
  `basisChangeY_conj_pauliZ` — the `Y` basis-change gate `S·H`, the single-qubit phase-gate tableau
  `S·X·Sᴴ = Y`, `S·Y·Sᴴ = -X`, `S·Z·Sᴴ = Z` (N&C Ex 10.39), and `(SH)·Z·(SH)ᴴ = Y`.
* `pauliString_conj_kronFamily` — the operator identity `B · (Z⊗Z⊗Z) · Bᴴ = X⊗Y⊗Z`, and
* `pauliString_exp_smul_conj_kronFamily` — its exponentiated form `exp(s·(X⊗Y⊗Z)) =
  B · exp(s·(Z⊗Z⊗Z)) · Bᴴ` for any `s : ℂ` (via `Matrix.exp_units_conj`, `B` unitary).
-/

open Matrix Complex

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The `n`-fold tensor product of single-qubit operators -/

/-- The **`n`-fold tensor product** `A₀ ⊗ A₁ ⊗ ⋯ ⊗ A_{n-1}` of a family of single-qubit operators
`A : Fin n → M₂(ℂ)`, as an operator on the `n`-qubit register `Fin n → Fin 2`, defined entrywise by
the product of the per-qubit entries `(⨂ₖ Aₖ)(i,j) = ∏ₖ Aₖ(iₖ)(jₖ)`. This matches the entrywise
form of `pauliString` (`pauliString g = kronFamily (σ_{g·})`, `pauliString_eq_kronFamily`), so the
mixed-product property `kronFamily_mul` conjugates a Pauli string factor-by-factor. -/
def kronFamily (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun i j => ∏ k, A k (i k) (j k)

@[simp]
theorem kronFamily_apply (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin n → Fin 2) :
    kronFamily A i j = ∏ k, A k (i k) (j k) := rfl

/-- A Pauli string is the tensor product of its per-qubit Pauli factors:
`pauliString g = kronFamily (fun k => pauli (g k))`. Definitional, since both are the entrywise
product `∏ₖ σ_{gₖ}(iₖ)(jₖ)`. -/
theorem pauliString_eq_kronFamily (g : Fin n → Fin 4) :
    pauliString g = kronFamily (fun k => pauli (g k)) := rfl

/-- **Mixed-product property of the tensor product** `(⨂ₖ Aₖ)(⨂ₖ Bₖ) = ⨂ₖ (Aₖ Bₖ)`. The `(i,j)`
entry of the product, `∑_l (∏ₖ Aₖ(iₖ)(lₖ))(∏ₖ Bₖ(lₖ)(jₖ))`, collapses under `Finset.prod_univ_sum`
into `∏ₖ ∑ₐ Aₖ(iₖ)(a) Bₖ(a)(jₖ) = ∏ₖ (Aₖ Bₖ)(iₖ)(jₖ)`: summing over intermediate register states
`l` is choosing an intermediate index per qubit. This is the algebraic engine of the basis-change
reduction (conjugation acts factor-by-factor). -/
theorem kronFamily_mul (A B : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    kronFamily A * kronFamily B = kronFamily (fun k => A k * B k) := by
  ext i j
  simp only [kronFamily, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun l _ => Finset.prod_mul_distrib.symm

/-- The conjugate transpose of a tensor product is the tensor product of the conjugate transposes,
`(⨂ₖ Aₖ)ᴴ = ⨂ₖ Aₖᴴ`. Entrywise, `star (∏ₖ Aₖ(jₖ)(iₖ)) = ∏ₖ star (Aₖ(jₖ)(iₖ)) = ∏ₖ Aₖᴴ(iₖ)(jₖ)`
(`map_prod` of the ring conjugation). -/
theorem kronFamily_conjTranspose (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (kronFamily A)ᴴ = kronFamily (fun k => (A k)ᴴ) := by
  ext i j
  rw [Matrix.conjTranspose_apply, kronFamily_apply, kronFamily_apply, ← starRingEnd_apply,
    map_prod]
  exact Finset.prod_congr rfl fun k _ => by rw [starRingEnd_apply, Matrix.conjTranspose_apply]

/-- The tensor product of identities is the identity, `⨂ₖ 1 = 1`. Entrywise
`∏ₖ (if iₖ = jₖ then 1 else 0)` is `1` when `i = j` (every factor `1`) and `0` otherwise (some
qubit factor vanishes). -/
theorem kronFamily_one : kronFamily (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  ext i j
  simp only [kronFamily_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [ite_eq_right h]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)

/-- Pulling per-qubit scalars out of a tensor product: `⨂ₖ (cₖ • Aₖ) = (∏ₖ cₖ) • ⨂ₖ Aₖ`. Entrywise
the `(i, j)` entry is `∏ₖ cₖ Aₖ(iₖ)(jₖ) = (∏ₖ cₖ)(∏ₖ Aₖ(iₖ)(jₖ))` by `Finset.prod_mul_distrib`. -/
theorem kronFamily_smul_family (c : Fin n → ℂ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    kronFamily (fun k => c k • A k) = (∏ k, c k) • kronFamily A := by
  ext i j
  simp only [kronFamily_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib]

/-! ### The single-qubit basis-change gates -/

/-- The **`Y` basis-change gate** `S·H` (phase gate after Hadamard): the single-qubit unitary that
conjugates `Z` to `Y` (`basisChangeY_conj_pauliZ`). It is the composite reducing a `Y` factor of a
Pauli Hamiltonian to a `Z` factor (N&C §4.7.3); `H` alone reduces an `X` factor. -/
noncomputable def basisChangeY : Matrix (Fin 2) (Fin 2) ℂ := sMatrix * hadamardC

/-- **Phase-gate conjugation** `S·X·Sᴴ = Y` (N&C Exercise 10.39): the phase gate `S = diag(1, i)`
rotates `X` into `Y`. A direct `2 × 2` computation. -/
theorem sMatrix_conj_pauliX : sMatrix * pauliX * sMatrixᴴ = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sMatrix, pauliX, pauliY, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]

/-- **Phase-gate conjugation** `S·Y·Sᴴ = -X` (N&C Exercise 10.39): the phase gate `S = diag(1, i)`
rotates `Y` into `-X`. A direct `2 × 2` computation. -/
theorem sMatrix_conj_pauliY : sMatrix * pauliY * sMatrixᴴ = -pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sMatrix, pauliX, pauliY, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]

/-- **Phase-gate conjugation** `S·Z·Sᴴ = Z` (N&C Exercise 10.39): the phase gate `S = diag(1, i)`
fixes `Z`. A direct `2 × 2` computation. -/
theorem sMatrix_conj_pauliZ : sMatrix * pauliZ * sMatrixᴴ = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sMatrix, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

/-- The `Y` basis-change gate conjugates `Z` to `Y`: `(SH) · Z · (SH)ᴴ = Y`. Splitting the
adjoint `(SH)ᴴ = H·Sᴴ` (Hadamard Hermitian) and regrouping, this is `S·(H·Z·H)·Sᴴ = S·X·Sᴴ = Y`
via `hadamardC_mul_pauliZ_mul_hadamardC` and `sMatrix_conj_pauliX`. -/
theorem basisChangeY_conj_pauliZ : basisChangeY * pauliZ * basisChangeYᴴ = pauliY := by
  have hHadj : hadamardCᴴ = hadamardC := hadamardC_isHermitian
  rw [basisChangeY, Matrix.conjTranspose_mul, hHadj, ← sMatrix_conj_pauliX,
    ← hadamardC_mul_pauliZ_mul_hadamardC]
  simp only [Matrix.mul_assoc]

/-- The `Y` basis-change gate is unitary: `(SH)(SH)ᴴ = 1`. Both `S` and `H` are unitary, so
`SH·(SH)ᴴ = S·(H·Hᴴ)·Sᴴ = S·Sᴴ = 1` (`hadamardC_mul_self`, `sMatrix_mem_unitaryGroup`). -/
theorem basisChangeY_mul_conjTranspose : basisChangeY * basisChangeYᴴ = 1 := by
  have hHadj : hadamardCᴴ = hadamardC := hadamardC_isHermitian
  have hS : sMatrix * sMatrixᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp sMatrix_mem_unitaryGroup
  rw [basisChangeY, Matrix.conjTranspose_mul, hHadj]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc hadamardC, hadamardC_mul_self, Matrix.one_mul, hS]

/-- The `Y` basis-change gate is unitary: `(SH)ᴴ(SH) = 1`. As `basisChangeY_mul_conjTranspose`
with the factors reversed (`Sᴴ·(Hᴴ·H)·... `). -/
theorem basisChangeY_conjTranspose_mul : basisChangeYᴴ * basisChangeY = 1 := by
  have hHadj : hadamardCᴴ = hadamardC := hadamardC_isHermitian
  have hS : sMatrixᴴ * sMatrix = 1 := Matrix.mem_unitaryGroup_iff'.mp sMatrix_mem_unitaryGroup
  rw [basisChangeY, Matrix.conjTranspose_mul, hHadj]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc sMatrixᴴ, hS, Matrix.one_mul, hadamardC_mul_self]

/-! ### The three-qubit basis-change reduction `X ⊗ Y ⊗ Z = B (Z ⊗ Z ⊗ Z) Bᴴ` -/

/-- The **local basis-change family** `B = (B₁, B₂, B₃) = (H, SH, I)` for Exercise 4.51: the three
single-qubit gates whose tensor product `kronFamily basisChangeFamily` conjugates `Z ⊗ Z ⊗ Z` to
`X ⊗ Y ⊗ Z`. Qubit 1 (`X`) is reduced by Hadamard, qubit 2 (`Y`) by `S·H`, qubit 3 (`Z`) is left
alone. -/
noncomputable def basisChangeFamily : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![hadamardC, basisChangeY, 1]

/-- Each local gate `Bₖ` conjugates `Z` to the target Pauli `σ_{c(k)}` of `X ⊗ Y ⊗ Z`:
`Bₖ · Z · Bₖᴴ = pauli (![1,2,3] k)` (i.e. `X`, `Y`, `Z` for `k = 0, 1, 2`). The per-qubit inputs to
`pauliString_conj_kronFamily`. -/
theorem basisChangeFamily_conj_pauliZ (k : Fin 3) :
    basisChangeFamily k * pauliZ * (basisChangeFamily k)ᴴ = pauli (![1, 2, 3] k) := by
  fin_cases k
  · simpa [basisChangeFamily, pauli] using
      (by rw [hadamardC_isHermitian]; exact hadamardC_mul_pauliZ_mul_hadamardC :
        hadamardC * pauliZ * hadamardCᴴ = pauliX)
  · simpa [basisChangeFamily, pauli] using basisChangeY_conj_pauliZ
  · simp [basisChangeFamily, pauli]

/-- Each local gate `Bₖ` is unitary: `Bₖ · Bₖᴴ = 1`. The per-qubit inputs to the unitarity of
`kronFamily basisChangeFamily`. -/
theorem basisChangeFamily_mul_conjTranspose (k : Fin 3) :
    basisChangeFamily k * (basisChangeFamily k)ᴴ = 1 := by
  fin_cases k
  · simpa [basisChangeFamily] using
      (by rw [hadamardC_isHermitian]; exact hadamardC_mul_self :
        hadamardC * hadamardCᴴ = 1)
  · simpa [basisChangeFamily] using basisChangeY_mul_conjTranspose
  · simp [basisChangeFamily]

/-- Each local gate `Bₖ` is unitary: `Bₖᴴ · Bₖ = 1`. -/
theorem basisChangeFamily_conjTranspose_mul (k : Fin 3) :
    (basisChangeFamily k)ᴴ * basisChangeFamily k = 1 := by
  fin_cases k
  · simpa [basisChangeFamily] using
      (by rw [hadamardC_isHermitian]; exact hadamardC_mul_self :
        hadamardCᴴ * hadamardC = 1)
  · simpa [basisChangeFamily] using basisChangeY_conjTranspose_mul
  · simp [basisChangeFamily]

/-- **Exercise 4.51, matrix form: the basis-change reduction of the tensor Pauli Hamiltonian.**
The local tensor unitary `B = H ⊗ SH ⊗ I` conjugates the all-`Z` Hamiltonian to the target:
`B · (Z ⊗ Z ⊗ Z) · Bᴴ = X ⊗ Y ⊗ Z`. Reducing both Pauli strings to `kronFamily` and applying the
mixed-product property twice (`kronFamily_mul`, `kronFamily_conjTranspose`) turns the left side into
`⨂ₖ (Bₖ · Z · Bₖᴴ)`, which is `⨂ₖ σ_{c(k)} = X ⊗ Y ⊗ Z` factor-by-factor
(`basisChangeFamily_conj_pauliZ`). -/
theorem pauliString_conj_kronFamily :
    kronFamily basisChangeFamily * pauliString ![3, 3, 3] * (kronFamily basisChangeFamily)ᴴ
      = pauliString ![1, 2, 3] := by
  have hZ : pauliString (![3, 3, 3] : Fin 3 → Fin 4) = kronFamily (fun _ => pauliZ) := by
    rw [pauliString_eq_kronFamily]
    congr 1
    funext k
    fin_cases k <;> simp [pauli]
  rw [hZ, kronFamily_conjTranspose, kronFamily_mul, kronFamily_mul, pauliString_eq_kronFamily]
  congr 1
  funext k
  exact basisChangeFamily_conj_pauliZ k

/-- The tensor unitary `B = H ⊗ SH ⊗ I` is unitary: `B · Bᴴ = 1`. Factor-by-factor from the
per-qubit unitarity (`basisChangeFamily_mul_conjTranspose`), via `kronFamily_mul`, `kronFamily_one`.
-/
theorem kronFamily_basisChangeFamily_mul_conjTranspose :
    kronFamily basisChangeFamily * (kronFamily basisChangeFamily)ᴴ = 1 := by
  rw [kronFamily_conjTranspose, kronFamily_mul]
  simp only [basisChangeFamily_mul_conjTranspose, kronFamily_one]

/-- The tensor unitary `B = H ⊗ SH ⊗ I` is unitary: `Bᴴ · B = 1`. -/
theorem kronFamily_basisChangeFamily_conjTranspose_mul :
    (kronFamily basisChangeFamily)ᴴ * kronFamily basisChangeFamily = 1 := by
  rw [kronFamily_conjTranspose, kronFamily_mul]
  simp only [basisChangeFamily_conjTranspose_mul, kronFamily_one]

/-- **Exercise 4.51, exponentiated form: the circuit for `e^{-iΔt H}`.** For any complex scalar
`s` (physically `s = -iΔt`), the propagator of the target Hamiltonian is the local conjugation of
the all-`Z` propagator: `exp(s · (X ⊗ Y ⊗ Z)) = B · exp(s · (Z ⊗ Z ⊗ Z)) · Bᴴ`. Since `s • H` is
conjugated by `B` exactly as `H` is (`pauliString_conj_kronFamily`), and `B` is unitary — hence a
unit with inverse `Bᴴ` — `Matrix.exp_units_conj` pushes the conjugation through the exponential.
This is the algebraic content of "apply the local basis changes `B`, run the `Z ⊗ Z ⊗ Z`
simulation of Figure 4.19, undo `B`". -/
theorem pauliString_exp_smul_conj_kronFamily (s : ℂ) :
    NormedSpace.exp (s • pauliString ![1, 2, 3])
      = kronFamily basisChangeFamily * NormedSpace.exp (s • pauliString ![3, 3, 3])
          * (kronFamily basisChangeFamily)ᴴ := by
  let u : (Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)ˣ :=
    ⟨kronFamily basisChangeFamily, (kronFamily basisChangeFamily)ᴴ,
      kronFamily_basisChangeFamily_mul_conjTranspose,
      kronFamily_basisChangeFamily_conjTranspose_mul⟩
  have hconj : s • pauliString ![1, 2, 3]
      = kronFamily basisChangeFamily * (s • pauliString ![3, 3, 3])
          * (kronFamily basisChangeFamily)ᴴ := by
    rw [← pauliString_conj_kronFamily, Matrix.mul_smul, Matrix.smul_mul]
  rw [hconj]
  exact Matrix.exp_units_conj u (s • pauliString ![3, 3, 3])

/-! ### The flat computational-basis (register) indexing `Fin (2ⁿ)` -/

/-- Reindexing a register-conjugation `W A Wᴴ` by a bijection `e` distributes over the three
factors: `(W A Wᴴ).submatrix e e = (W.submatrix e e)(A.submatrix e e)(W.submatrix e e)ᴴ`. This is
the transport carrying the bit-string statements (`kronFamily`, `pauliString`) to the flat
`Fin (2ⁿ)` indexing of `pauliStringStd`, since `submatrix` by an equiv on both indices is a
`⋆`-algebra map (`Matrix.submatrix_mul_equiv`, `Matrix.conjTranspose_submatrix`). -/
theorem submatrix_conj_equiv {m l : Type*} [Fintype m] [Fintype l]
    (e : l ≃ m) (W A : Matrix m m ℂ) :
    (W * A * Wᴴ).submatrix e e
      = W.submatrix e e * A.submatrix e e * (W.submatrix e e)ᴴ := by
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

/-- The **Std-indexed tensor product** `⨂ₖ Aₖ` on the flat register `Fin (2ⁿ)`: `kronFamily A`
reindexed from bit strings `Fin n → Fin 2` to `Fin (2ⁿ)` along `finFunctionFinEquiv`, exactly as
`pauliStringStd` reindexes `pauliString`. This is the operator `B = ⨂ₖ Aₖ` in the flat
computational-basis ordering that the `n`-qubit register `qudit (2ⁿ)` uses; the physics wrapper
(`Postulates/API/PauliStringSimulation.lean`) promotes `kronFamilyStd basisChangeFamily` to a
unitary `Evolution`. -/
noncomputable def kronFamilyStd (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (kronFamily A).submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm

/-- **Exercise 4.51, the reduction on the flat register `Fin (2³)`.** The Std-indexed basis change
`B = H ⊗ SH ⊗ I` conjugates the all-`Z` string to the target: `B · (Z⊗Z⊗Z) · Bᴴ = X⊗Y⊗Z`, on the
`Fin (2³)` computational basis that `pauliStringStd` (and the register `qudit (2³)`) use. The flat
image of `pauliString_conj_kronFamily`, obtained by `submatrix_conj_equiv`. -/
theorem kronFamilyStd_basisChangeFamily_conj_pauliStringStd :
    kronFamilyStd basisChangeFamily * pauliStringStd ![3, 3, 3]
        * (kronFamilyStd basisChangeFamily)ᴴ
      = pauliStringStd ![1, 2, 3] := by
  simp only [kronFamilyStd, pauliStringStd]
  rw [← submatrix_conj_equiv, pauliString_conj_kronFamily]

/-- The Std basis change is unitary: `B · Bᴴ = 1` on `Fin (2³)`. The flat image of
`kronFamily_basisChangeFamily_mul_conjTranspose` (`submatrix` of `1` by an equiv is `1`). -/
theorem kronFamilyStd_basisChangeFamily_mul_conjTranspose :
    kronFamilyStd basisChangeFamily * (kronFamilyStd basisChangeFamily)ᴴ = 1 := by
  simp only [kronFamilyStd, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, kronFamily_basisChangeFamily_mul_conjTranspose,
    Matrix.submatrix_one_equiv]

/-- The Std basis change is unitary: `Bᴴ · B = 1` on `Fin (2³)`. -/
theorem kronFamilyStd_basisChangeFamily_conjTranspose_mul :
    (kronFamilyStd basisChangeFamily)ᴴ * kronFamilyStd basisChangeFamily = 1 := by
  simp only [kronFamilyStd, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, kronFamily_basisChangeFamily_conjTranspose_mul,
    Matrix.submatrix_one_equiv]

end AxQM.Concrete
