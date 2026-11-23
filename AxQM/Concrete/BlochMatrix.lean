/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

/-!
# Concrete: the Bloch matrix `ρ = (I + r·σ)/2`

For a real three-vector
`r` this file defines the `2 × 2` complex matrix

`blochMatrix r = ½ (I + r·σ) = ½ (I + r₀ X + r₁ Y + r₂ Z)`,

the **Bloch representation of a single-qubit density matrix** (Nielsen & Chuang, Exercise
2.72, eq. 2.175), built on the concrete combination `Concrete.pauliDot` (`r·σ`). It records the
matrix-level facts of the exercise that need no positivity/spectral analysis — the statement that
the family `½(I + r·σ)` is exactly the family of Hermitian trace-one `2 × 2` matrices:

* `blochMatrix_eq` — the collapsed explicit `2 × 2` form
  `½ !![1 + r₂, r₀ − i r₁; r₀ + i r₁, 1 − r₂]`.
* `blochMatrix_isHermitian` — `blochMatrix r` is Hermitian (`r` real).
* `blochMatrix_trace` — `tr (blochMatrix r) = 1` (the `±r₂` on the diagonal cancels).
* `blochMatrix_zero` — `blochMatrix 0 = ½ I`, the matrix underlying the maximally mixed state
  (Nielsen & Chuang, Exercise 2.72(2): the state `ρ = I/2` has Bloch vector `r⃗ = 0`).
* `blochVector` / `blochVector_blochMatrix` — the map reading the Bloch vector off a matrix's
  entries (`r₀ = 2 Re M₁₀`, `r₁ = 2 Im M₁₀`, `r₂ = 2 Re M₀₀ − 1`), a **left inverse** of
  `blochMatrix`; the citable "Bloch vector for `ρ`" the exercise names.
* `blochMatrix_injective` — `r ↦ blochMatrix r` is injective, so the Bloch vector of a matrix is
  **unique** ("the Bloch vector for `ρ`" of the exercise is well defined), immediate from the
  left inverse `blochVector`.
* `exists_blochMatrix_of_isHermitian_trace_one` — **every** Hermitian trace-one `2 × 2` matrix
  is `blochMatrix r` for some real `r` (the decomposition half of Exercise 2.72(1): the family
  `½(I + r·σ)` exhausts the Hermitian trace-one matrices).
* `blochMatrix_det` — `det (blochMatrix r) = (1 − ‖r‖²)/4`, the eigenvalue product `λ₊ λ₋` for the
  eigenvalues `(1 ± ‖r‖)/2`.
* `blochMatrix_posSemidef_iff` — the **positivity constraint** of Exercise 2.72(1): `blochMatrix r`
  is positive semidefinite iff `‖r‖² = r₀² + r₁² + r₂² ≤ 1`. Together with the Hermitian/trace-one
  facts this identifies the Bloch matrices that are genuine density matrices as exactly the closed
  unit ball `‖r‖ ≤ 1` — the **Bloch ball**.

The remaining halves of Exercise 2.72 — the purity characterization `pure ↔ ‖r‖ = 1` (part 3),
and the promotion of the `‖r‖ ≤ 1` family to states of a qubit `State qubit` (parts 1, 2, 4) —
are not treated here.

## Design notes

* The Bloch vector `r` is modelled as a bare `Fin 3 → ℝ` and `‖r‖²` as the scalar
  `r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2`, matching `Concrete.pauliDot` (and N&C's `r⃗ · σ⃗ ≡ Σᵢ rᵢ σᵢ`).
* Facts are proved by collapsing to the closed `2 × 2` form `blochMatrix_eq` and computing
  entrywise, the same idiom as `Concrete.Pauli`.
* `exists_blochMatrix_of_isHermitian_trace_one` recovers the components from the matrix entries:
  `r₀ = 2 Re M₁₀`, `r₁ = 2 Im M₁₀`, `r₂ = 2 Re M₀₀ − 1` (using that `M` is Hermitian — diagonal
  real, `M₀₁ = M₁₀*` — and has trace one — `M₁₁ = 1 − M₀₀`).
-/

namespace AxQM.Concrete

open Matrix Complex
open scoped ComplexOrder

/-- The **Bloch matrix** `½ (I + r·σ)` for a real three-vector `r`: the `2 × 2` complex matrix
representing a single-qubit density matrix with Bloch vector `r` (Nielsen & Chuang, Exercise
2.72, eq. 2.175). Built from the identity and the Pauli combination `Concrete.pauliDot r`. -/
noncomputable def blochMatrix (r : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (2⁻¹ : ℂ) • (1 + pauliDot r)

/-- The **Bloch vector** read off a `2 × 2` matrix's entries: `r₀ = 2 Re M₁₀`, `r₁ = 2 Im M₁₀`,
`r₂ = 2 Re M₀₀ − 1`. This is the left inverse of `blochMatrix` (`blochVector_blochMatrix`), so it
recovers the Bloch vector of a Bloch matrix — the extraction "the Bloch vector for `ρ`" that
Nielsen & Chuang, Exercise 2.72 names. -/
noncomputable def blochVector (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℝ :=
  ![2 * (M 1 0).re, 2 * (M 1 0).im, 2 * (M 0 0).re - 1]

/-- `blochMatrix r` as a single explicit `2 × 2` matrix
`½ !![1 + r₂, r₀ − i r₁; r₀ + i r₁, 1 − r₂]`. -/
theorem blochMatrix_eq (r : Fin 3 → ℝ) :
    blochMatrix r =
      !![(2⁻¹ : ℂ) * (1 + (r 2 : ℂ)), (2⁻¹ : ℂ) * ((r 0 : ℂ) - (r 1 : ℂ) * I);
         (2⁻¹ : ℂ) * ((r 0 : ℂ) + (r 1 : ℂ) * I), (2⁻¹ : ℂ) * (1 - (r 2 : ℂ))] := by
  rw [blochMatrix, pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.add_apply, mul_add, sub_eq_add_neg]

/-- **`blochVector (blochMatrix r) = r`**: recovering the Bloch vector off the entries inverts
`blochMatrix`. Reading `r₀ = 2 Re M₁₀` etc. back from `½(I + r·σ)`'s entries returns `r`. -/
theorem blochVector_blochMatrix (r : Fin 3 → ℝ) : blochVector (blochMatrix r) = r := by
  funext i
  rw [blochMatrix_eq]
  fin_cases i <;>
    simp [blochVector, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]

/-- `(blochMatrix r)ᴴ = blochMatrix r`: the Bloch matrix is self-adjoint (its diagonal entries are
real and its off-diagonal entries are complex conjugates). -/
theorem blochMatrix_conjTranspose (r : Fin 3 → ℝ) : (blochMatrix r)ᴴ = blochMatrix r := by
  rw [blochMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, Complex.ext_iff]

/-- `blochMatrix r` is Hermitian for any real three-vector `r` (Nielsen & Chuang, Exercise 2.72:
the density matrix `ρ = ½(I + r·σ)` is Hermitian). -/
theorem blochMatrix_isHermitian (r : Fin 3 → ℝ) : (blochMatrix r).IsHermitian :=
  blochMatrix_conjTranspose r

/-- **`tr (blochMatrix r) = 1`**: the trace of the Bloch matrix is one, since the `±r₂` on the
diagonal cancels and the two `½`'s add. This is the trace-one half of "`blochMatrix r` is a
density matrix" (Nielsen & Chuang, Exercise 2.72). -/
theorem blochMatrix_trace (r : Fin 3 → ℝ) : (blochMatrix r).trace = 1 := by
  rw [blochMatrix_eq, Matrix.trace_fin_two]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  ring

/-- **`blochMatrix 0 = ½ I`**: the Bloch matrix of the zero vector is half the identity, the
matrix underlying the maximally mixed state `I/2` (Nielsen & Chuang, Exercise 2.72(2): the state
`ρ = I/2` has Bloch vector `r⃗ = 0`). -/
theorem blochMatrix_zero :
    blochMatrix (0 : Fin 3 → ℝ) = (2⁻¹ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [blochMatrix]
  simp [pauliDot]

/-- **`r ↦ blochMatrix r` is injective**: a Bloch matrix determines its Bloch vector, so the
"Bloch vector for `ρ`" of Nielsen & Chuang, Exercise 2.72 is unique. The three real components are
recovered from the `(0,0)` and `(1,0)` entries. -/
theorem blochMatrix_injective : Function.Injective blochMatrix :=
  Function.LeftInverse.injective blochVector_blochMatrix

/-- **Bloch decomposition (Nielsen & Chuang, Exercise 2.72(1), the "form" half).** Every Hermitian
`2 × 2` matrix of trace one is a Bloch matrix: there is a real three-vector `r` with
`M = ½(I + r·σ)`. The components are read off `M`'s entries — `r₀ = 2 Re M₁₀`, `r₁ = 2 Im M₁₀`,
`r₂ = 2 Re M₀₀ − 1` — using Hermiticity (diagonal real, `M₀₁ = M₁₀*`) and trace one
(`M₁₁ = 1 − M₀₀`). Together with `blochMatrix_isHermitian`/`blochMatrix_trace` this shows the
family `½(I + r·σ)` is *exactly* the Hermitian trace-one matrices. -/
theorem exists_blochMatrix_of_isHermitian_trace_one {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M.IsHermitian) (htr : M.trace = 1) :
    ∃ r : Fin 3 → ℝ, M = blochMatrix r := by
  refine ⟨blochVector M, ?_⟩
  -- Hermiticity: diagonal entries real, and `M₀₁ = conj M₁₀`.
  have h00 : (M 0 0).im = 0 := Complex.conj_eq_iff_im.mp (hM.apply 0 0)
  have h11 : (M 1 1).im = 0 := Complex.conj_eq_iff_im.mp (hM.apply 1 1)
  have h01re : (M 0 1).re = (M 1 0).re := by
    have := hM.apply 0 1; rw [Complex.ext_iff] at this; simpa using this.1.symm
  have h01im : (M 0 1).im = -(M 1 0).im := by
    have := hM.apply 0 1; rw [Complex.ext_iff] at this; simpa using this.2.symm
  -- Trace one: `M₀₀ + M₁₁ = 1`, hence on real parts `Re M₀₀ + Re M₁₁ = 1`.
  have htrre : (M 0 0).re + (M 1 1).re = 1 := by
    rw [Matrix.trace_fin_two] at htr
    have := congrArg Complex.re htr; simpa [Complex.add_re] using this
  rw [blochMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [blochVector, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Matrix.cons_val_two, Matrix.tail_cons] <;>
    rw [Complex.ext_iff] <;>
    refine ⟨?_, ?_⟩ <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
    linarith [h00, h11, h01re, h01im, htrre]

/-- **`det (blochMatrix r) = (1 − ‖r‖²)/4`** (with `‖r‖² = r₀² + r₁² + r₂²`). Computing the
`2 × 2` determinant of `½ !![1+r₂, r₀−i r₁; r₀+i r₁, 1−r₂]`, the diagonal product contributes
`¼(1 − r₂²)` and the off-diagonal product `¼(r₀² + r₁²)`, whose difference is `¼(1 − ‖r‖²)`. This
is the product `λ₊ λ₋` of the eigenvalues `(1 ± ‖r‖)/2` of the Bloch matrix, and it drives the
positivity criterion `blochMatrix_posSemidef_iff`. -/
theorem blochMatrix_det (r : Fin 3 → ℝ) :
    (blochMatrix r).det = ((1 - (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2)) / 4 : ℝ) := by
  rw [blochMatrix_eq, Matrix.det_fin_two]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  rw [Complex.ext_iff]
  refine ⟨?_, ?_⟩ <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, -Complex.ofReal_pow, Complex.I_re,
      Complex.I_im] <;>
    ring

/-- **`tr ((blochMatrix r)²) = (1 + ‖r‖²)/2`** (with `‖r‖² = r₀² + r₁² + r₂²`). Squaring the Bloch
matrix `½(I + r·σ)` and taking the trace: the diagonal entries square to give
`¼(1+r₂)² + ¼(1−r₂)² = ½(1 + r₂²)`, and the two off-diagonal cross terms contribute
`2·¼(r₀ − i r₁)(r₀ + i r₁) = ½(r₀² + r₁²)`, summing to `½(1 + ‖r‖²)`. Equivalently
`tr ((blochMatrix r)²) = ½(1 + ‖r‖²)`, matching the eigenvalues `(1 ± ‖r‖)/2` (their squares sum to
`½(1 + ‖r‖²)`). This is the **purity** `tr ρ²` of the Bloch matrix; combined with the equivalence
`tr ρ² = 1 ↔ ρ` pure it drives the purity characterization `pure ↔ ‖r‖ = 1` (Nielsen & Chuang,
Exercise 2.72(3)). -/
theorem blochMatrix_sq_trace (r : Fin 3 → ℝ) :
    (blochMatrix r * blochMatrix r).trace
      = (((1 + (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2)) / 2 : ℝ) : ℂ) := by
  rw [blochMatrix_eq, Matrix.mul_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  rw [Complex.ext_iff]
  refine ⟨?_, ?_⟩ <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, -Complex.ofReal_pow, Complex.I_re,
      Complex.I_im] <;>
    ring

/-- **Positivity criterion for the Bloch matrix (Nielsen & Chuang, Exercise 2.72(1), positivity
half).** `blochMatrix r` is positive semidefinite iff `‖r‖² = r₀² + r₁² + r₂² ≤ 1` — equivalently
`‖r‖ ≤ 1`, since `‖r‖ ≥ 0`. Combined with `blochMatrix_isHermitian`, `blochMatrix_trace` and
`exists_blochMatrix_of_isHermitian_trace_one`, this identifies the Bloch matrices that are genuine
density matrices (Hermitian, trace one, positive semidefinite) as exactly the closed unit ball
`‖r‖ ≤ 1` — the **Bloch ball**.

*Forward* (`PosSemidef ⇒ ‖r‖² ≤ 1`): a positive semidefinite matrix has nonnegative determinant
(`Matrix.PosSemidef.det_nonneg`), and `det (blochMatrix r) = (1 − ‖r‖²)/4` (`blochMatrix_det`), so
`0 ≤ (1 − ‖r‖²)/4`.

*Reverse* (`‖r‖² ≤ 1 ⇒ PosSemidef`): writing `A := r·σ`, which is Hermitian
(`pauliDot_conjTranspose`) with `A² = ‖r‖²·I` (`pauliDot_mul_self`), one has the algebraic identity

`blochMatrix r = ¼·(I+A)ᴴ(I+A) + ¼(1 − ‖r‖²)·I`,

exhibiting `blochMatrix r` as a nonnegative combination of the positive semidefinite matrices
`(I+A)ᴴ(I+A)` (a Gram matrix, `Matrix.posSemidef_conjTranspose_mul_self`) and `I`
(`Matrix.PosSemidef.one`); the second coefficient `¼(1 − ‖r‖²)` is `≥ 0` exactly when `‖r‖² ≤ 1`.
This route sidesteps any normalisation of `r` (no `r/‖r‖`, no case split on `r = 0`). -/
theorem blochMatrix_posSemidef_iff (r : Fin 3 → ℝ) :
    (blochMatrix r).PosSemidef ↔ r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1 := by
  constructor
  · -- Forward: positive semidefinite ⇒ nonnegative determinant ⇒ ‖r‖² ≤ 1.
    intro h
    have hdet := h.det_nonneg
    rw [blochMatrix_det, Complex.zero_le_real] at hdet
    linarith
  · -- Reverse: the Gram + scaled-identity decomposition.
    intro hr
    have hAh : (1 + pauliDot r)ᴴ = 1 + pauliDot r := by
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, pauliDot_conjTranspose]
    -- (I+A)ᴴ(I+A) = I + 2A + A² = I + 2A + ‖r‖²·I.
    have hgram : (1 + pauliDot r)ᴴ * (1 + pauliDot r)
        = 1 + pauliDot r + pauliDot r
          + ((r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [hAh,
        show (1 + pauliDot r) * (1 + pauliDot r)
            = 1 + pauliDot r + pauliDot r + pauliDot r * pauliDot r from by noncomm_ring,
        pauliDot_mul_self]
    -- The scalar-level identity blochMatrix r = ¼(I+A)ᴴ(I+A) + ¼(1-‖r‖²)·I. The two coefficients
    -- are written as coerced reals so the nonnegativity goals reduce via `Complex.zero_le_real`.
    have heq : blochMatrix r
        = (((4⁻¹ : ℝ) : ℂ)) • ((1 + pauliDot r)ᴴ * (1 + pauliDot r))
          + (((1 - (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2)) / 4 : ℝ) : ℂ)
            • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [hgram, blochMatrix, pauliDot_eq]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
          Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul] <;>
        push_cast <;> ring
    rw [heq]
    refine (Matrix.posSemidef_conjTranspose_mul_self _).smul ?_ |>.add
      (Matrix.PosSemidef.one.smul ?_)
    · rw [Complex.zero_le_real]; norm_num
    · rw [Complex.zero_le_real]; linarith

/-- **The Bloch ball is closed under a `[0,1]` shrink.** If `r` lies in the closed unit ball
`r₀² + r₁² + r₂² ≤ 1` and `0 ≤ c ≤ 1`, then so does the scaled vector `c r`:
`‖c r‖² = c² ‖r‖² ≤ c² ≤ 1`. A pure `Fin 3 → ℝ` companion to `blochMatrix_posSemidef_iff`'s ball
constraint, used to certify that the shrunk Bloch state stays a genuine density matrix (e.g. under
the depolarizing channel `r ↦ (1 − p) r`, Nielsen & Chuang Exercise 9.12). -/
theorem sq_sum_smul_le_one {r : Fin 3 → ℝ} (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (c • r) 0 ^ 2 + (c • r) 1 ^ 2 + (c • r) 2 ^ 2 ≤ 1 := by
  simp only [Pi.smul_apply, smul_eq_mul]
  nlinarith [h, sq_nonneg (r 0), sq_nonneg (r 1), sq_nonneg (r 2), hc0, hc1, mul_nonneg hc0 hc0]

end AxQM.Concrete
