/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochUnitaryRotation
import AxQM.Concrete.BlochMatrix

/-!
# The Bloch/transfer matrix of a matrix operator-sum (Kraus) family

Pure matrix algebra, on the way to the qubit converse of Nielsen & Chuang Problem 8.3.
For a finite family of `2 × 2` complex matrices `A : ι → M₂(ℂ)` (operation elements)
the operator-sum map `B ↦ ∑ₖ Aₖ B Aₖ†` acts on the **Bloch matrices**
`Concrete.blochMatrix r = ½(I + r·σ)` by a real affine-linear map of the Bloch vector `r`. When the
family is **unital** (`∑ₖ Aₖ Aₖ† = I`, so the identity term is fixed) and each image `∑ₖ Aₖ σⱼ Aₖ†`
of a Pauli is **traceless** (automatic for a trace-preserving family, `∑ₖ Aₖ† Aₖ = I`), the map is
purely linear: `r ↦ M r`, where `M` is the real `3 × 3` **Bloch matrix of the channel** whose
`j`-th column is the Pauli coordinates of `∑ₖ Aₖ σⱼ Aₖ†`.

* `Concrete.krausBlochMatrix A` — the real `3 × 3` matrix `M` (column `j` = `pauliCoords (∑ₖ Aₖ σⱼ
  Aₖ†)`).
* `Concrete.sum_conj_pauliDot_single_isHermitian` — each `∑ₖ Aₖ σⱼ Aₖ†` is Hermitian.
* `Concrete.sum_conj_blochMatrix` — the key identity `∑ₖ Aₖ (½(I+r·σ)) Aₖ† = ½(I + (M r)·σ)`, i.e.
  the operator sum carries `blochMatrix r` to `blochMatrix (M *ᵥ r)`, under the unital hypothesis
  `∑ₖ Aₖ Aₖ† = I` and tracelessness of each Pauli image.

Everything reuses the Pauli-coordinate machinery of `Concrete.BlochUnitaryRotation`
(`pauliDot`, `pauliCoords`, `pauliDot_pauliCoords_of_isHermitian_trace_zero`, `pauliDot_eq_sum`,
`pauliDot_sum3`, `mulVec_eq_sum_col`) built for Exercise 8.13. The physical statement — that a
genuine unital CPTP **channel** acts on Bloch states by such an `M` — obtains the family `A` from
the operator-sum representation theorem (N&C Theorem 8.1).
-/

open scoped Matrix

namespace AxQM.Concrete

variable {ι : Type*} [Fintype ι]

/-- The real `3 × 3` **Bloch matrix** `M` of the matrix operator-sum family `A : ι → M₂(ℂ)`: its
`j`-th column is the Pauli coordinates `(Re T₁₀, Im T₁₀, Re T₀₀)` of the Pauli image
`Tⱼ = ∑ₖ Aₖ σⱼ Aₖ†` (`σⱼ = pauliDot (eⱼ)`). On a unital trace-preserving family this is the matrix
of the induced Bloch-vector map `r ↦ M r` (`sum_conj_blochMatrix`). -/
noncomputable def krausBlochMatrix (A : ι → Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => pauliCoords (∑ k, A k * pauliDot (Pi.single j 1) * (A k)ᴴ) i

/-- The `(i, j)`-entry of `krausBlochMatrix A` is the `i`-th Pauli coordinate of the `j`-th Pauli
image `∑ₖ Aₖ σⱼ Aₖ†`. The definitional `_apply` API lemma for `krausBlochMatrix`. -/
@[simp]
theorem krausBlochMatrix_apply (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 3) :
    krausBlochMatrix A i j = pauliCoords (∑ k, A k * pauliDot (Pi.single j 1) * (A k)ᴴ) i :=
  rfl

/-- The Pauli image `∑ₖ Aₖ σⱼ Aₖ†` of a matrix operator-sum family is Hermitian: each summand
`Aₖ σⱼ Aₖ†` is Hermitian (conjugation preserves Hermiticity and `σⱼ` is Hermitian,
`Matrix.isHermitian_mul_mul_conjTranspose` + `pauliDot_isHermitian`), and a finite sum of Hermitian
matrices is Hermitian. -/
theorem sum_conj_pauliDot_single_isHermitian (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 3) :
    (∑ k, A k * pauliDot (Pi.single j 1) * (A k)ᴴ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun k _ =>
    Matrix.isHermitian_mul_mul_conjTranspose (A k) (pauliDot_isHermitian _)

/-- **Bloch action of a unital, trace-preserving matrix operator-sum family.** For a finite family
`A : ι → M₂(ℂ)` with `∑ₖ Aₖ Aₖ† = I` (unital) and each Pauli image `∑ₖ Aₖ σⱼ Aₖ†` traceless, the
operator-sum map carries the Bloch matrix `½(I + r·σ)` to `½(I + (M r)·σ)`, where
`M = krausBlochMatrix A`. This is the concrete heart of the qubit converse of N&C Problem 8.3: a
unital CPTP qubit channel acts on the Bloch ball by the linear map `r ↦ M r`. -/
theorem sum_conj_blochMatrix (A : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∑ k, A k * (A k)ᴴ = 1)
    (htl : ∀ j, (∑ k, A k * pauliDot (Pi.single j 1) * (A k)ᴴ).trace = 0)
    (r : Fin 3 → ℝ) :
    ∑ k, A k * blochMatrix r * (A k)ᴴ = blochMatrix (krausBlochMatrix A *ᵥ r) := by
  -- Column `j` of `M` recovers the Pauli image `∑ₖ Aₖ σⱼ Aₖ†` through `pauliDot`.
  have hcol : ∀ j, (∑ k, A k * pauliDot (Pi.single j 1) * (A k)ᴴ)
      = pauliDot (fun i => krausBlochMatrix A i j) := by
    intro j
    -- `krausBlochMatrix A · j` is (defeq) `pauliCoords (∑ₖ Aₖ σⱼ Aₖ†)`, so `pauliDot` of it is
    -- exactly the Pauli image, backward via `pauliDot ∘ pauliCoords = id` on Hermitian traceless.
    exact (pauliDot_pauliCoords_of_isHermitian_trace_zero
      (sum_conj_pauliDot_single_isHermitian A j) (htl j)).symm
  -- The Pauli part of the operator sum equals `(M r)·σ`.
  have hpart : ∑ k, A k * pauliDot r * (A k)ᴴ = pauliDot (krausBlochMatrix A *ᵥ r) := by
    rw [pauliDot_eq_sum r]
    have hrs : ∀ k, A k * (∑ j, (r j : ℂ) • pauliDot (Pi.single j 1)) * (A k)ᴴ
        = ∑ j, (r j : ℂ) • (A k * pauliDot (Pi.single j 1) * (A k)ᴴ) := by
      intro k
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm, smul_mul_assoc]
    simp_rw [hrs]
    rw [Finset.sum_comm]
    have hj : ∀ j, (∑ k, (r j : ℂ) • (A k * pauliDot (Pi.single j 1) * (A k)ᴴ))
        = (r j : ℂ) • pauliDot (fun i => krausBlochMatrix A i j) := by
      intro j; rw [← Finset.smul_sum, hcol j]
    simp_rw [hj]
    rw [← pauliDot_sum3 r (fun j i => krausBlochMatrix A i j), mulVec_eq_sum_col]
  -- Assemble: expand `blochMatrix`, distribute, use `hU` for the identity term and `hpart`.
  simp only [blochMatrix]
  have hterm : ∀ k, A k * ((2⁻¹ : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + pauliDot r)) * (A k)ᴴ
      = (2⁻¹ : ℂ) • (A k * (A k)ᴴ + A k * pauliDot r * (A k)ᴴ) := by
    intro k
    rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.smul_sum, Finset.sum_add_distrib, hU,
    hpart]

end AxQM.Concrete
