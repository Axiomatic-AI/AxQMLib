/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import ToMathlib.Data.Real.Sqrt
import ToMathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Complex.Basic
import ToMathlib.LinearAlgebra.UnitaryGroup

/-!
# Concrete: two-level decomposition of the 4×4 quantum Fourier transform (N&C Ex 4.37)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.37 (p. 191) asks
for a decomposition of the transform (eq. 4.52)

```
        ⎡ 1   1   1   1 ⎤
  F = ½ ⎢ 1   i  -1  -i ⎥        (Fⱼₖ = ½ · iʲᵏ,  j,k ∈ {0,1,2,3})
        ⎢ 1  -1   1  -1 ⎥
        ⎣ 1  -i  -1   i ⎦
```

— the two-qubit quantum Fourier transform (the `N = 4` discrete Fourier transform matrix) — into
a product of **two-level unitaries**: unitary matrices that act non-trivially on at most two of
the four computational basis vectors (i.e. agree with the identity outside a single 2×2 principal
submatrix).

## The decomposition

We use the radix-2 (Cooley–Tukey) factorisation of the DFT, `F = B · (H ⊕ H) · P`, in which every
sparse factor splits into a pair of *disjoint* 2×2 blocks — and disjoint blocks each embed as a
genuine two-level unitary. Concretely

```
  F = qftFactorH02 · qftFactorG13 · qftFactorH01 · qftFactorH23 · qftFactorSwap
```

where, writing `H = (√2)⁻¹ !![1,1; 1,-1]` for the Hadamard block and
`G = (√2)⁻¹ !![1,i; 1,-i]` for the "twiddled" Hadamard block,

* `qftFactorH02` — `H` on the coordinate pair `{0,2}` (identity on `{1,3}`);
* `qftFactorG13` — `G` on `{1,3}` (identity on `{0,2}`);
* `qftFactorH01` — `H` on `{0,1}`;
* `qftFactorH23` — `H` on `{2,3}`;
* `qftFactorSwap` — the transposition (bit-reversal swap) of `{1,2}`.

The five factors compose to `F` exactly: the two Hadamard-magnitude layers each contribute a
`(√2)⁻¹` per block, and the two `(√2)⁻¹` factors that meet on each basis vector multiply to the
overall `½` prefactor of (4.52) (`qftFour_eq_prod`). Each factor is a two-level unitary
(`qftFactor…_isTwoLevelUnitary`), and — as a product of unitaries — `F` is itself unitary
(`qftFour_mem_unitaryGroup`).

## Design notes

* **A concrete existence result.** The exercise asks only to *provide* a decomposition, so this is
  an explicit construction, not an appeal to the general §4.5.1 algorithm (N&C's Gaussian-style
  procedure, which would produce up to `d(d-1)/2 = 6` factors with irrational Givens entries). The
  FFT route gives a cleaner five-factor product whose blocks are Hadamard/twiddle gates and a
  permutation, and it never needs the general theorem.
* **Genuine two-level factors.** Each factor equals the identity outside one 2×2 block, so scalars
  cannot be pulled through the whole matrix; the definitions carry the `(√2)⁻¹` entries inline.
  The product proof instead groups the two disjoint-block layers (`H02·G13` and `H01·H23`), each of
  which *does* factor as `(√2)⁻¹ • (Gaussian-integer matrix)`, so the only irrational arithmetic is
  the single scalar identity `(√2)⁻¹ · (√2)⁻¹ = ½`.
* **Generality.** The statement of Exercise 4.37 is in `AxQM/NC/Ch4/Exercise4_37.lean`.
  `IsTwoLevelUnitary` is stated here in general `d` dimensions so it can be reused for the
  neighbouring two-level items (Ex 4.38, Ex 4.39, §4.5.1).
-/

namespace AxQM.Concrete

open Matrix

/-- A `d × d` complex matrix `U` is a **two-level unitary** (Nielsen & Chuang §4.5.1) when it is
unitary and acts non-trivially on at most two computational basis vectors: there are indices
`p, q` such that `U` agrees with the identity on every entry lying outside the `{p,q} × {p,q}`
principal submatrix. Allowing `p = q` includes the one-level (single-phase) case, so this captures
"acts non-trivially on two-or-fewer components". -/
def IsTwoLevelUnitary {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
    ∃ p q : Fin d, ∀ i j : Fin d,
      (i ≠ p ∧ i ≠ q) ∨ (j ≠ p ∧ j ≠ q) → U i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j

/-- The normalisation scalar squares to `½`: `(√2)⁻¹ · (√2)⁻¹ = 2⁻¹` over `ℂ`. Used in the product
identity, where the two Hadamard-layer factors of `(√2)⁻¹` combine into the `½` of (4.52). -/
theorem invSqrtTwo_mul_self : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 2⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- `(√2)² = 2` over `ℂ`. Used to close the diagonal entries of the `star U · U = I` unitarity
checks, where two `(√2)⁻¹` factors combine as `(√2²)⁻¹ = 2⁻¹`. -/
theorem sqrtTwo_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- The 4×4 quantum Fourier transform `F` of Nielsen & Chuang eq. (4.52), `Fⱼₖ = ½ · iʲᵏ`:
`½ !![1,1,1,1; 1,i,-1,-i; 1,-1,1,-1; 1,-i,-1,i]`. This is the `N = 4` discrete Fourier transform
matrix, i.e. the two-qubit QFT. -/
noncomputable def qftFour : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • !![1, 1, 1, 1; 1, Complex.I, -1, -Complex.I;
     1, -1, 1, -1; 1, -Complex.I, -1, Complex.I]

/-- First factor: the Hadamard block `H = (√2)⁻¹ !![1,1; 1,-1]` acting on the coordinate pair
`{0,2}`, identity on `{1,3}`. A two-level unitary. -/
noncomputable def qftFactorH02 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(Real.sqrt 2 : ℂ)⁻¹, 0, (Real.sqrt 2 : ℂ)⁻¹, 0; 0, 1, 0, 0;
     (Real.sqrt 2 : ℂ)⁻¹, 0, -(Real.sqrt 2 : ℂ)⁻¹, 0; 0, 0, 0, 1]

/-- Second factor: the twiddled Hadamard block `G = (√2)⁻¹ !![1,i; 1,-i]` acting on the coordinate
pair `{1,3}`, identity on `{0,2}`. A two-level unitary. -/
noncomputable def qftFactorG13 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, (Real.sqrt 2 : ℂ)⁻¹, 0, Complex.I * (Real.sqrt 2 : ℂ)⁻¹;
     0, 0, 1, 0; 0, (Real.sqrt 2 : ℂ)⁻¹, 0, -(Complex.I * (Real.sqrt 2 : ℂ)⁻¹)]

/-- Third factor: the Hadamard block `H = (√2)⁻¹ !![1,1; 1,-1]` acting on the coordinate pair
`{0,1}`, identity on `{2,3}`. A two-level unitary. -/
noncomputable def qftFactorH01 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹, 0, 0;
     (Real.sqrt 2 : ℂ)⁻¹, -(Real.sqrt 2 : ℂ)⁻¹, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- Fourth factor: the Hadamard block `H = (√2)⁻¹ !![1,1; 1,-1]` acting on the coordinate pair
`{2,3}`, identity on `{0,1}`. A two-level unitary. -/
noncomputable def qftFactorH23 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, (Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹;
     0, 0, (Real.sqrt 2 : ℂ)⁻¹, -(Real.sqrt 2 : ℂ)⁻¹]

/-- Fifth factor: the transposition (bit-reversal swap) of the coordinate pair `{1,2}`, identity on
`{0,3}`. A two-level unitary (a permutation matrix). -/
def qftFactorSwap : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

/-- **Nielsen & Chuang, Exercise 4.37.** The 4×4 quantum Fourier transform factors as a product of
five two-level unitaries, `F = qftFactorH02 · qftFactorG13 · qftFactorH01 · qftFactorH23 ·
qftFactorSwap`. Proved by grouping the two disjoint-block layers `H02·G13 = (√2)⁻¹ • B` and
`H01·H23 = (√2)⁻¹ • C` (both Gaussian-integer matrices), so that `(√2)⁻¹ · (√2)⁻¹ = ½` supplies the
prefactor and the remaining product `B · C · Swap` is the integer matrix `!![…] = 2·F`. -/
theorem qftFour_eq_prod :
    qftFour = qftFactorH02 * qftFactorG13 * qftFactorH01 * qftFactorH23 * qftFactorSwap := by
  have hA : qftFactorH02 * qftFactorG13
      = (Real.sqrt 2 : ℂ)⁻¹ • !![1, 0, 1, 0; 0, 1, 0, Complex.I;
          1, 0, -1, 0; 0, 1, 0, -Complex.I] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [qftFactorH02, qftFactorG13, Matrix.mul_apply, Fin.sum_univ_four,
        Matrix.smul_apply] <;> ring
  have hB : qftFactorH01 * qftFactorH23
      = (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1, 0, 0; 1, -1, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [qftFactorH01, qftFactorH23, Matrix.mul_apply, Fin.sum_univ_four, Matrix.smul_apply]
  rw [mul_assoc (qftFactorH02 * qftFactorG13) qftFactorH01 qftFactorH23, hA, hB]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, invSqrtTwo_mul_self]
  rw [qftFour]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qftFactorSwap, Matrix.mul_apply, Fin.sum_univ_four]

/-- The first factor is a two-level unitary, acting only on `{0,2}`. -/
theorem qftFactorH02_isTwoLevelUnitary : IsTwoLevelUnitary qftFactorH02 := by
  refine ⟨?_, 0, 2, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply, qftFactorH02] <;>
      ring_nf <;> norm_num [Complex.I_sq, sqrtTwo_sq]
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [qftFactorH02]

/-- The second factor is a two-level unitary, acting only on `{1,3}`. -/
theorem qftFactorG13_isTwoLevelUnitary : IsTwoLevelUnitary qftFactorG13 := by
  refine ⟨?_, 1, 3, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply, qftFactorG13] <;>
      ring_nf <;> norm_num [Complex.I_sq, sqrtTwo_sq]
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [qftFactorG13]

/-- The third factor is a two-level unitary, acting only on `{0,1}`. -/
theorem qftFactorH01_isTwoLevelUnitary : IsTwoLevelUnitary qftFactorH01 := by
  refine ⟨?_, 0, 1, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply, qftFactorH01] <;>
      ring_nf <;> norm_num [Complex.I_sq, sqrtTwo_sq]
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [qftFactorH01]

/-- The fourth factor is a two-level unitary, acting only on `{2,3}`. -/
theorem qftFactorH23_isTwoLevelUnitary : IsTwoLevelUnitary qftFactorH23 := by
  refine ⟨?_, 2, 3, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply, qftFactorH23] <;>
      ring_nf <;> norm_num [Complex.I_sq, sqrtTwo_sq]
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [qftFactorH23]

/-- The fifth factor is a two-level unitary, acting only on `{1,2}` (a transposition). -/
theorem qftFactorSwap_isTwoLevelUnitary : IsTwoLevelUnitary qftFactorSwap := by
  refine ⟨?_, 1, 2, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply, qftFactorSwap]
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [qftFactorSwap]

/-- The 4×4 quantum Fourier transform is unitary: being a product of the five two-level unitaries of
`qftFour_eq_prod`, it lies in the unitary group. -/
theorem qftFour_mem_unitaryGroup : qftFour ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [qftFour_eq_prod]
  exact mul_mem (mul_mem (mul_mem (mul_mem qftFactorH02_isTwoLevelUnitary.1
    qftFactorG13_isTwoLevelUnitary.1) qftFactorH01_isTwoLevelUnitary.1)
    qftFactorH23_isTwoLevelUnitary.1) qftFactorSwap_isTwoLevelUnitary.1

end AxQM.Concrete
