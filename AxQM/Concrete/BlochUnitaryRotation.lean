/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochRotation
import ToMathlib.LinearAlgebra.UnitaryGroup

/-!
# Concrete: unitary conjugation of the Bloch matrix is an SO(3) rotation (N&C Exercise 8.13)

Nielsen & Chuang, Exercise 8.13 asks to show that *unitary transformations correspond to rotations
of the Bloch sphere*. In the Bloch representation `ρ = ½(I + r·σ)` (N&C eq. 8.87, here
`Concrete.blochMatrix r`), the state conjugation `ρ ↦ U ρ U†` induced by a `2 × 2` unitary `U`
sends the Bloch vector `r` to `R r`, where `R` is a **proper rotation** `R ∈ SO(3)`. This is the
`SU(2) → SO(3)` homomorphism: the group of single-qubit unitaries (modulo the global phase, which
cancels in the conjugation) double-covers the rotation group of the Bloch ball.

This file develops the pure `2 × 2`/`3 × 3` matrix core; the statement for evolutions and states
is in `AxQM/NC/Ch8/Exercise8_13.lean`.

## What is formalized

* `blochRotationOfUnitary U` — the **induced 3D rotation matrix** `R(U) : Matrix (Fin 3) (Fin 3) ℝ`,
  whose `k`-th column is the Pauli coordinate vector of `U σₖ U†`.
* `blochRotationOfUnitary_conj_pauliDot` — the **homomorphism at the Pauli level**: for a unitary
  `U`, `U (v·σ) U† = (R(U) v)·σ`. Its heart is the reconstruction that a Hermitian traceless
  `2 × 2` matrix `M` equals `(pauliCoords M)·σ` (`pauliDot_pauliCoords_of_isHermitian_trace_zero`),
  applied to `U σₖ U†` (Hermitian since `σₖ` is, traceless since `tr(U σₖ U†) = tr σₖ = 0`).
* `blochRotationOfUnitary_mem_orthogonalGroup` — `R(U)ᵀ R(U) = I`, from the Hilbert–Schmidt
  orthonormality of the columns: `2 (wₖ · wₗ) = tr((wₖ·σ)(wₗ·σ)) = tr(U σₖ σₗ U†) = 2δₖₗ`.
* `blochRotationOfUnitary_det` — `det R(U) = 1`, from the orientation identity `X Y Z = i I`:
  `2i (w₀×w₁)·w₂ = tr((w₀·σ)(w₁·σ)(w₂·σ)) = tr(U (XYZ) U†) = tr(i I) = 2i`, and
  `det R = (w₀×w₁)·w₂` (the scalar triple product of the columns).
* `exists_mem_specialOrthogonalGroup_blochMatrix_conj_unitary` — **Exercise 8.13 (Concrete
  headline)**: for any unitary `U`, there is `R ∈ SO(3)` with `U (blochMatrix r) U† = blochMatrix
  (R r)` for every Bloch vector `r`.

The physical statement — that unitary *evolution* rotates
the Bloch *state*'s vector — is in `AxQM/NC/Ch8/Exercise8_13.lean`.

## Design notes

* The Pauli coordinates are `pauliCoords M = (Re M₁₀, Im M₁₀, Re M₀₀)`, the inverse of
  `pauliDot` on the space of Hermitian traceless matrices (compare `Concrete.blochVector`, which
  carries the affine `−1` shift for the trace-one Bloch matrices). No factor of two appears.
* The whole `SU(2) → SO(3)` construction is *uniform* in `U`: orthogonality and `det = 1` are read
  off two Pauli-trace identities (`pauliDot_trace_mul`, `pauliDot_trace_mul3`) with the unitary's
  role reduced to the cyclicity `tr(U A U†) = tr A`. In particular the axis-angle decomposition
  (`Concrete.exists_axis_angle_decomposition`) is *not* used — the proof holds for any unitary.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- `tr(v·σ) = 0`: the Pauli combination is traceless (its diagonal is `(v₂, −v₂)`). -/
theorem pauliDot_trace (v : Fin 3 → ℝ) : (pauliDot v).trace = 0 := by
  rw [pauliDot_eq, Matrix.trace_fin_two]
  simp

/-- **Hilbert–Schmidt pairing of Pauli combinations**: `tr((a·σ)(b·σ)) = 2 (a · b)`. The `(a·b) I`
part of the Pauli product rule contributes `2 (a·b)`; the `i (a×b)·σ` part is traceless. -/
theorem pauliDot_trace_mul (a b : Fin 3 → ℝ) :
    (pauliDot a * pauliDot b).trace = 2 * ((a ⬝ᵥ b : ℝ) : ℂ) := by
  rw [pauliDot_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, trace_one_fin_two,
    pauliDot_trace, smul_eq_mul, smul_eq_mul, mul_zero, add_zero, mul_comm]

/-- **Triple Pauli trace** (the orientation pairing): `tr((a·σ)(b·σ)(c·σ)) = 2i ((a×b) · c)`. From
the Pauli product rule `(a·σ)(b·σ) = (a·b) I + i (a×b)·σ` and `pauliDot_trace`/`pauliDot_trace_mul`:
the `(a·b) I` term multiplies a traceless `c·σ`, and the `i (a×b)·σ` term pairs with `c·σ` to give
`i · 2((a×b)·c)`. This is the scalar triple product that drives `det R = 1`. -/
theorem pauliDot_trace_mul3 (a b c : Fin 3 → ℝ) :
    (pauliDot a * pauliDot b * pauliDot c).trace
      = 2 * Complex.I * (((crossProduct a) b ⬝ᵥ c : ℝ) : ℂ) := by
  rw [pauliDot_mul, add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.trace_smul, Matrix.trace_smul, one_mul, pauliDot_trace, pauliDot_trace_mul,
    smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
  ring

/-- `pauliDot (Pi.single 0 1) = X`. -/
theorem pauliDot_single_zero : pauliDot (Pi.single 0 (1 : ℝ)) = pauliX := by
  rw [pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX]

/-- `pauliDot (Pi.single 1 1) = Y`. -/
theorem pauliDot_single_one : pauliDot (Pi.single 1 (1 : ℝ)) = pauliY := by
  rw [pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY]

/-- `pauliDot (Pi.single 2 1) = Z`. -/
theorem pauliDot_single_two : pauliDot (Pi.single 2 (1 : ℝ)) = pauliZ := by
  rw [pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ]

/-- The orientation identity `X Y Z = i I` (positive handedness of the Pauli vector). -/
theorem pauliX_mul_pauliY_mul_pauliZ :
    pauliX * pauliY * pauliZ = Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The **Pauli coordinates** of a `2 × 2` matrix: `(Re M₁₀, Im M₁₀, Re M₀₀)`. On the Hermitian
traceless matrices this inverts `pauliDot` (`pauliDot_pauliCoords_of_isHermitian_trace_zero`). -/
noncomputable def pauliCoords (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℝ :=
  ![(M 1 0).re, (M 1 0).im, (M 0 0).re]

/-- **Reconstruction**: a Hermitian, traceless `2 × 2` matrix `M` is `(pauliCoords M)·σ`. Reading
`(Re M₁₀, Im M₁₀, Re M₀₀)` back through `pauliDot` returns `M`, using Hermiticity (diagonal real,
`M₀₁ = M₁₀*`) and tracelessness (`M₁₁ = −M₀₀`). This is the `pauliDot`-inverse that turns each
conjugate `U σₖ U†` into a real three-vector. -/
theorem pauliDot_pauliCoords_of_isHermitian_trace_zero {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hH : M.IsHermitian) (h0 : M.trace = 0) : pauliDot (pauliCoords M) = M := by
  have h00 : (M 0 0).im = 0 := Complex.conj_eq_iff_im.mp (hH.apply 0 0)
  have h11 : (M 1 1).im = 0 := Complex.conj_eq_iff_im.mp (hH.apply 1 1)
  have h01re : (M 0 1).re = (M 1 0).re := by
    have := hH.apply 0 1; rw [Complex.ext_iff] at this; simpa using this.1.symm
  have h01im : (M 0 1).im = -(M 1 0).im := by
    have := hH.apply 0 1; rw [Complex.ext_iff] at this; simpa using this.2.symm
  have htr : (M 0 0).re + (M 1 1).re = 0 := by
    rw [Matrix.trace_fin_two] at h0
    have := congrArg Complex.re h0; simpa [Complex.add_re] using this
  rw [pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliCoords, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Matrix.cons_val_two, Matrix.tail_cons] <;>
    rw [Complex.ext_iff] <;>
    refine ⟨?_, ?_⟩ <;>
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
    linarith [h00, h11, h01re, h01im, htr]

/-- `tr(U A U†) = tr A` for a unitary `U` (`U† U = 1`): cyclicity of the trace. -/
theorem trace_conjUnitary {U : Matrix (Fin 2) (Fin 2) ℂ} (hUU' : Uᴴ * U = 1)
    (A : Matrix (Fin 2) (Fin 2) ℂ) : (U * A * Uᴴ).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, hUU', one_mul]

/-- Conjugation by a unitary is multiplicative: `(U A U†)(U B U†) = U (A B) U†` (using `U† U = 1`).
The engine of both SO(3)-membership proofs: it collapses a product of conjugates to a single
conjugate whose trace is `tr(A B)` via `trace_conjUnitary`. -/
theorem conjUnitary_mul {U : Matrix (Fin 2) (Fin 2) ℂ} (hUU' : Uᴴ * U = 1)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    U * A * Uᴴ * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
  simp only [mul_assoc]
  rw [← mul_assoc Uᴴ U, hUU', one_mul]

/-- `U A U†` is Hermitian when `A` is a Pauli combination (`(v·σ)† = v·σ`). -/
theorem conjUnitary_pauliDot_isHermitian (U : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 3 → ℝ) :
    (U * pauliDot v * Uᴴ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    pauliDot_conjTranspose, ← mul_assoc]

/-- The **induced 3D rotation matrix** `R(U)` of a `2 × 2` unitary: its `k`-th column is the Pauli
coordinate vector of `U σₖ U†`, where `σₖ = pauliDot (Pi.single k 1)` (so `σ₀ = X`, `σ₁ = Y`,
`σ₂ = Z`). By `blochRotationOfUnitary_conj_pauliDot` it satisfies `U (v·σ) U† = (R(U) v)·σ`. -/
noncomputable def blochRotationOfUnitary (U : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun j k => pauliCoords (U * pauliDot (Pi.single k 1) * Uᴴ) j

/-- Each conjugated basis Pauli reconstructs to the corresponding column of `R(U)`:
`U σₖ U† = (colₖ R(U))·σ`. Immediate from the reconstruction lemma, since `U σₖ U†` is Hermitian
and traceless and `colₖ R(U)` is by definition its Pauli coordinates. -/
theorem conjUnitary_pauliDot_eq_col {U : Matrix (Fin 2) (Fin 2) ℂ} (hUU' : Uᴴ * U = 1)
    (k : Fin 3) :
    U * pauliDot (Pi.single k 1) * Uᴴ = pauliDot (fun j => blochRotationOfUnitary U j k) := by
  rw [← pauliDot_pauliCoords_of_isHermitian_trace_zero (conjUnitary_pauliDot_isHermitian U _)
    (by rw [trace_conjUnitary hUU', pauliDot_trace])]
  rfl

/-- `pauliDot` distributes over a real-scalar `Fin 3` sum. -/
theorem pauliDot_sum3 (c : Fin 3 → ℝ) (w : Fin 3 → (Fin 3 → ℝ)) :
    pauliDot (∑ k, c k • w k) = ∑ k, (c k : ℂ) • pauliDot (w k) := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three, pauliDot_add, pauliDot_add, pauliDot_smul,
    pauliDot_smul, pauliDot_smul]

/-- The standard-basis expansion `∑ k, v k • Pi.single k 1 = v`. -/
theorem sum_smul_single (v : Fin 3 → ℝ) :
    (∑ k, v k • (Pi.single k 1 : Fin 3 → ℝ)) = v := by
  funext i
  rw [Finset.sum_apply]
  simp [Pi.single_apply, Finset.sum_ite_eq]

/-- `v·σ = ∑ k, vₖ (Pi.single k 1)·σ`: the Pauli combination as a basis sum, used to reduce the
homomorphism to its action on the basis conjugates. -/
theorem pauliDot_eq_sum (v : Fin 3 → ℝ) :
    pauliDot v = ∑ k, (v k : ℂ) • pauliDot (Pi.single k (1 : ℝ)) := by
  conv_lhs => rw [← sum_smul_single v]
  rw [pauliDot_sum3]

/-- `R.mulVec v` as the scaled sum of the columns of `R`. -/
theorem mulVec_eq_sum_col (R : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    R.mulVec v = ∑ k, v k • (fun j => R j k) := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **The `SU(2) → SO(3)` homomorphism at the Pauli level.** For a unitary `U`, conjugating the
Pauli combination `v·σ` gives that of the rotated vector: `U (v·σ) U† = (R(U) v)·σ`.
The proof expands `v·σ = ∑ vₖ σₖ`, distributes the conjugation over the sum, reconstructs each
`U σₖ U†` as `(colₖ R(U))·σ`, and reassembles `∑ vₖ colₖ = R(U) v`. -/
theorem blochRotationOfUnitary_conj_pauliDot {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hUU' : Uᴴ * U = 1) (v : Fin 3 → ℝ) :
    U * pauliDot v * Uᴴ = pauliDot ((blochRotationOfUnitary U).mulVec v) := by
  rw [pauliDot_eq_sum v, Finset.mul_sum, Finset.sum_mul]
  simp_rw [Matrix.mul_smul, Matrix.smul_mul, conjUnitary_pauliDot_eq_col hUU']
  rw [mulVec_eq_sum_col, pauliDot_sum3]

/-- **`R(U)ᵀ R(U) = I`**: `R(U)` is orthogonal. The `(k, l)` entry of `R(U)ᵀ R(U)` is
`colₖ · colₗ`, and `2 (colₖ · colₗ) = tr((colₖ·σ)(colₗ·σ)) = tr(U σₖ σₗ U†) = tr(σₖ σₗ)
= 2 (σₖ-vector · σₗ-vector) = 2 δₖₗ`, using the Pauli trace pairing and trace cyclicity. -/
theorem blochRotationOfUnitary_mem_orthogonalGroup {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    blochRotationOfUnitary U ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  have hUU' : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff' (n := Fin 2) (α := ℂ)).mp hU
  -- the columns are orthonormal: `colₚ · col_q = δₚ_q`, via the Pauli-trace pairing.
  have hcol : ∀ p q : Fin 3,
      (∑ j, blochRotationOfUnitary U j p * blochRotationOfUnitary U j q)
        = if p = q then (1 : ℝ) else 0 := by
    intro p q
    have key : (pauliDot (fun j => blochRotationOfUnitary U j p)
                * pauliDot (fun j => blochRotationOfUnitary U j q)).trace
             = (pauliDot (Pi.single p 1) * pauliDot (Pi.single q 1)).trace := by
      rw [← conjUnitary_pauliDot_eq_col hUU' p, ← conjUnitary_pauliDot_eq_col hUU' q,
        conjUnitary_mul hUU', trace_conjUnitary hUU']
    rw [pauliDot_trace_mul, pauliDot_trace_mul] at key
    have hreal : ((fun j => blochRotationOfUnitary U j p) ⬝ᵥ
          (fun j => blochRotationOfUnitary U j q)) = (Pi.single p (1 : ℝ) ⬝ᵥ Pi.single q 1) := by
      exact_mod_cast mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) key
    rw [show (∑ j, blochRotationOfUnitary U j p * blochRotationOfUnitary U j q)
          = (fun j => blochRotationOfUnitary U j p) ⬝ᵥ (fun j => blochRotationOfUnitary U j q)
          from rfl, hreal, single_dotProduct, one_mul, Pi.single_apply]
  rw [Matrix.mem_orthogonalGroup_iff']
  ext k l
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply]
  exact hcol k l

/-- **`det R(U) = 1`**: `R(U)` is a *proper* rotation. Its determinant equals the scalar triple
product `(col₀ × col₁) · col₂` of the columns, and `2i ((col₀×col₁)·col₂) = tr((col₀·σ)(col₁·σ)
(col₂·σ)) = tr(U (X Y Z) U†) = tr(i I) = 2i` (using `X Y Z = i I` and trace cyclicity), so the
triple product is `1`. -/
theorem blochRotationOfUnitary_det {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) : (blochRotationOfUnitary U).det = 1 := by
  have hUU' : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff' (n := Fin 2) (α := ℂ)).mp hU
  set c0 : Fin 3 → ℝ := fun j => blochRotationOfUnitary U j 0 with hc0
  set c1 : Fin 3 → ℝ := fun j => blochRotationOfUnitary U j 1 with hc1
  set c2 : Fin 3 → ℝ := fun j => blochRotationOfUnitary U j 2 with hc2
  -- the triple product is 1
  have htriple : (crossProduct c0) c1 ⬝ᵥ c2 = 1 := by
    have hkey : (pauliDot c0 * pauliDot c1 * pauliDot c2).trace = 2 * Complex.I := by
      rw [hc0, hc1, hc2, ← conjUnitary_pauliDot_eq_col hUU', ← conjUnitary_pauliDot_eq_col hUU',
        ← conjUnitary_pauliDot_eq_col hUU']
      rw [conjUnitary_mul hUU', conjUnitary_mul hUU', trace_conjUnitary hUU',
        pauliDot_single_zero, pauliDot_single_one, pauliDot_single_two,
        pauliX_mul_pauliY_mul_pauliZ, Matrix.trace_smul, trace_one_fin_two, smul_eq_mul]
      ring
    have heq := hkey.symm.trans (pauliDot_trace_mul3 c0 c1 c2)
    -- 2i = 2i * triple  ⟹  triple = 1
    have : (((crossProduct c0) c1 ⬝ᵥ c2 : ℝ) : ℂ) = 1 :=
      mul_left_cancel₀ (by simp [Complex.ext_iff] : (2 * Complex.I : ℂ) ≠ 0)
        (by rw [mul_one]; exact heq.symm)
    exact_mod_cast this
  -- det = scalar triple product of the columns
  rw [Matrix.det_fin_three]
  simp only [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at htriple
  simp only [hc0, hc1, hc2] at htriple
  linarith [htriple]

/-- `R(U) ∈ SO(3)`: combining orthogonality and `det = 1`. -/
theorem blochRotationOfUnitary_mem_specialOrthogonalGroup {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    blochRotationOfUnitary U ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨blochRotationOfUnitary_mem_orthogonalGroup hU, blochRotationOfUnitary_det hU⟩

/-- **`R(U)` preserves the squared Bloch-vector length**: `‖R(U) r‖² = ‖r‖²` (with `‖·‖²` the
scalar `·₀² + ·₁² + ·₂²`). Proved *algebraically* from the homomorphism identity, mirroring
`rot3D_sq_sum`: `(R(U) r)·σ = U (r·σ) U†`, so `((R(U) r)·σ)² = U (r·σ)² U† = ‖r‖² U U† = ‖r‖² I`
using `U† U = U U† = I` and `(w·σ)² = ‖w‖² I` (`pauliDot_mul_self`); comparing with
`((R(U) r)·σ)² = ‖R(U) r‖² I` gives `‖R(U) r‖² = ‖r‖²`. Since `R(U)` is an SO(3) rotation this is
just orthogonality, but the Pauli-square route needs no orthogonal-group API. It keeps the rotated
Bloch vector in the ball, so `blochState (R(U) r)` is well defined (Exercise 8.13). -/
theorem blochRotationOfUnitary_mulVec_sq_sum {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (r : Fin 3 → ℝ) :
    ((blochRotationOfUnitary U).mulVec r) 0 ^ 2 + ((blochRotationOfUnitary U).mulVec r) 1 ^ 2
        + ((blochRotationOfUnitary U).mulVec r) 2 ^ 2
      = r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 := by
  have hUU : U * Uᴴ = 1 := (Matrix.mem_unitaryGroup_iff (n := Fin 2) (α := ℂ)).mp hU
  have hUU' : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff' (n := Fin 2) (α := ℂ)).mp hU
  have key : pauliDot ((blochRotationOfUnitary U).mulVec r)
      * pauliDot ((blochRotationOfUnitary U).mulVec r)
      = ((r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 : ℝ) : ℂ) • 1 := by
    rw [← blochRotationOfUnitary_conj_pauliDot hUU']
    calc U * pauliDot r * Uᴴ * (U * pauliDot r * Uᴴ)
          = U * pauliDot r * (Uᴴ * U) * pauliDot r * Uᴴ := by noncomm_ring
      _ = U * (pauliDot r * pauliDot r) * Uᴴ := by rw [hUU']; noncomm_ring
      _ = ((r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 : ℝ) : ℂ) • 1 := by
          rw [pauliDot_mul_self, mul_smul_comm, smul_mul_assoc, mul_one, hUU]
  rw [pauliDot_mul_self] at key
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) key
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
  exact_mod_cast h00

/-- **Unitary conjugation of the Bloch matrix rotates its Bloch vector.** For a unitary `U`,
`U (blochMatrix r) U† = blochMatrix (R(U) r)`: the identity part is fixed (`U U† = I`) and the
traceless part rotates (`blochRotationOfUnitary_conj_pauliDot`). -/
theorem blochMatrix_conj_unitary {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (r : Fin 3 → ℝ) :
    U * blochMatrix r * Uᴴ = blochMatrix ((blochRotationOfUnitary U).mulVec r) := by
  have hUU : U * Uᴴ = 1 := (Matrix.mem_unitaryGroup_iff (n := Fin 2) (α := ℂ)).mp hU
  have hUU' : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff' (n := Fin 2) (α := ℂ)).mp hU
  simp only [blochMatrix, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [mul_add, mul_one, add_mul, hUU, blochRotationOfUnitary_conj_pauliDot hUU']

/-- **Nielsen & Chuang, Exercise 8.13 (Concrete headline) — unitary transformations correspond to
rotations of the Bloch sphere.** For any `2 × 2` unitary `U`, the state conjugation
`ρ ↦ U ρ U†` on the Bloch matrix `ρ = ½(I + r·σ)` acts on the Bloch vector `r` as a *proper
rotation* `R ∈ SO(3)`: there exists `R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ` with
`U (blochMatrix r) U† = blochMatrix (R r)` for every `r`. The witness is
`blochRotationOfUnitary U`, the `SU(2) → SO(3)` image of `U`. -/
theorem exists_mem_specialOrthogonalGroup_blochMatrix_conj_unitary
    {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ r : Fin 3 → ℝ, U * blochMatrix r * Uᴴ = blochMatrix (R.mulVec r) :=
  ⟨blochRotationOfUnitary U, blochRotationOfUnitary_mem_specialOrthogonalGroup hU,
    fun r => blochMatrix_conj_unitary hU r⟩

end AxQM.Concrete
