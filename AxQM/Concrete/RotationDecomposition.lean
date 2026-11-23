/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Rotation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Concrete: the Z–Y decomposition of a single-qubit unitary (Nielsen & Chuang, Theorem 4.1)

Building on the rotation matrices
`rotY`, `rotZ` of `Concrete/Rotation.lean` (N&C eqs. 4.5, 4.6), it proves the **Z–Y decomposition**
— **Nielsen & Chuang, Theorem 4.1** (eq. 4.11): every single-qubit unitary `U` factors as

`U = e^{iα} R_z(β) R_y(γ) R_z(δ)`

for some real `α, β, γ, δ`. This is the algebraic backbone of the construction of controlled
single-qubit operations (Corollary 4.2 and §4.3).

## What is formalised

* `rotZ_mul_rotY_mul_rotZ` — the closed form of the product `R_z(β) R_y(γ) R_z(δ)` as the single
  `2 × 2` matrix of N&C eq. (4.12) (up to the global phase). This is the reusable computational
  core, obtained from the explicit-matrix lemmas `rotZ_eq`/`rotY_eq` and `Matrix.mul_fin_two`.
* `exists_zy_decomposition` — **Theorem 4.1 itself**: for `U ∈ Matrix.unitaryGroup (Fin 2) ℂ`
  there exist real `α, β, γ, δ` with `U = e^{iα} • (R_z(β) R_y(γ) R_z(δ))`.
* `zyMatrixForm` — the entry-explicit matrix of N&C eq. (4.12) itself: the diagonal entries
  `e^{i(α ∓ β/2 ∓ δ/2)} cos(γ/2)` and off-diagonal `∓ e^{i(α ∓ β/2 ± δ/2)} sin(γ/2)`, with the
  global phase `e^{iα}` folded in.
* `zyMatrixForm_eq_smul_rotZ_mul_rotY_mul_rotZ` — the bridge `zyMatrixForm α β γ δ =
  e^{iα} • (R_z(β) R_y(γ) R_z(δ))`, folding the phase of `rotZ_mul_rotY_mul_rotZ` into each entry.
* `exists_zyMatrixForm` — **Nielsen & Chuang, Exercise 4.9**: every unitary
  `U ∈ Matrix.unitaryGroup (Fin 2) ℂ` can be written in the explicit form (4.12), i.e.
  `∃ α β γ δ, U = zyMatrixForm α β γ δ`. It is the entrywise restatement of Theorem 4.1, obtained by
  applying the bridge to `exists_zy_decomposition`.

## Design notes

* **`rotY`/`rotZ` are reused, not redefined.** The rotation matrices come from
  `Concrete/Rotation.lean` (where `R_n̂(θ) ≡ exp(-iθ(n·σ)/2)` and `rotY`/`rotZ` are its
  coordinate cases); here we consume their explicit-matrix forms `rotY_eq`/`rotZ_eq` and add only
  the decomposition-specific results, so there is a single source of truth for the rotations.
* **"Unitary" as `Matrix.unitaryGroup`.** A single-qubit unitary is a `2 × 2` complex matrix with
  `Uᴴ U = I`, i.e. membership in `Matrix.unitaryGroup (Fin 2) ℂ` — N&C's own definition of a
  quantum gate. No dimension or determinant is fixed, so the statement is Theorem 4.1 in full
  generality (all of `U(2)`, not just `SU(2)`).
* **Proof.** The four entries of `U` are pinned by unitarity: writing `a = U₀₀`, `c = U₁₀`, the
  columns are orthonormal so `‖a‖² + ‖c‖² = 1`, and `Uᴴ = U⁻¹ = (det U)⁻¹ · adj U` forces
  `U₁₁ = det U · conj a` and `U₀₁ = -det U · conj c` (via `adjugate_fin_two`). Choosing
  `α = arg(det U)/2`, `β = arg c - arg a`, `γ = 2 arccos ‖a‖`, `δ = arg(det U) - arg a - arg c` and
  reading each entry through the polar form `z = ‖z‖ e^{i arg z}` matches
  `e^{iα} R_z(β) R_y(γ) R_z(δ)` entrywise. The `det`-based bookkeeping computes the phases of the
  two "dependent" entries `U₁₁, U₀₁` from their closed forms rather than from `arg U₁₁`, `arg U₀₁`
  directly — avoiding the mod-`2π` ambiguity of `Complex.arg` on a product.

The statement of Theorem 4.1 is `exists_zy_decomposition`, in `AxQM/NC/Ch4/Theorem4_1.lean`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The product `R_z(β) R_y(γ) R_z(δ)` in closed form (Nielsen & Chuang eq. 4.12, without the
global phase): a single `2 × 2` matrix whose entries are `e^{∓i(β±δ)/2}` times `cos(γ/2)`
(diagonal) or `sin(γ/2)` (off-diagonal). This is the computational core of the Z–Y decomposition
(`exists_zy_decomposition`), obtained from the explicit forms `rotZ_eq`/`rotY_eq`. -/
theorem rotZ_mul_rotY_mul_rotZ (β γ δ : ℝ) :
    rotZ β * rotY γ * rotZ δ =
      !![Complex.exp ((-((β : ℂ) + δ) / 2) * I) * (Real.cos (γ / 2) : ℂ),
         -(Complex.exp ((-((β : ℂ) - δ) / 2) * I) * (Real.sin (γ / 2) : ℂ));
         Complex.exp (((β : ℂ) - δ) / 2 * I) * (Real.sin (γ / 2) : ℂ),
         Complex.exp (((β : ℂ) + δ) / 2 * I) * (Real.cos (γ / 2) : ℂ)] := by
  rw [rotZ_eq, rotY_eq, rotZ_eq]
  simp only [Matrix.mul_fin_two, mul_zero, zero_mul, add_zero, zero_add, mul_neg, neg_zero]
  rw [show (-((β : ℂ) + δ) / 2 * I) = (-(β : ℂ) / 2 * I) + (-(δ : ℂ) / 2 * I) by ring,
     show (-((β : ℂ) - δ) / 2 * I) = (-(β : ℂ) / 2 * I) + ((δ : ℂ) / 2 * I) by ring,
     show (((β : ℂ) - δ) / 2 * I) = ((β : ℂ) / 2 * I) + (-(δ : ℂ) / 2 * I) by ring,
     show (((β : ℂ) + δ) / 2 * I) = ((β : ℂ) / 2 * I) + ((δ : ℂ) / 2 * I) by ring,
     Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add]
  ring_nf

/-- **Nielsen & Chuang, Theorem 4.1 (Z–Y decomposition of a single-qubit unitary).** Every
`2 × 2` unitary `U` (a single-qubit gate, `Uᴴ U = I`) factors as
`U = e^{iα} R_z(β) R_y(γ) R_z(δ)` for some real numbers `α, β, γ, δ` (eq. 4.11). The angles are
extracted from the entries of `U`: `α = arg(det U)/2`, `β = arg U₁₀ - arg U₀₀`,
`γ = 2 arccos ‖U₀₀‖`, `δ = arg(det U) - arg U₀₀ - arg U₁₀`, and the equality is checked entrywise
against the closed form `rotZ_mul_rotY_mul_rotZ` using the polar decomposition of each entry and
the unitarity constraints `‖U₀₀‖² + ‖U₁₀‖² = 1`, `U₁₁ = det U · conj U₀₀`,
`U₀₁ = -det U · conj U₁₀`. -/
theorem exists_zy_decomposition (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ δ : ℝ, U = Complex.exp ((α : ℂ) * Complex.I) • (rotZ β * rotY γ * rotZ δ) := by
  have hUsU : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).1 hU
  have hsUU : star U * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hU
  -- `det U` is a unit, with inverse `det (star U)`.
  have hunit : IsUnit U.det :=
    IsUnit.of_mul_eq_one (star U).det (by rw [← Matrix.det_mul, hUsU, Matrix.det_one])
  have hrmul : U.det * Ring.inverse U.det = 1 := Ring.mul_inverse_cancel _ hunit
  -- `star U = U⁻¹ = (det U)⁻¹ • adj U`, and `adj` of a `2 × 2` matrix is explicit.
  have hstar : star U = Ring.inverse U.det • !![U 1 1, -U 0 1; -U 1 0, U 0 0] := by
    rw [(Matrix.inv_eq_left_inv hsUU).symm, Matrix.inv_def, Matrix.adjugate_fin_two]
  -- The two "dependent" entries in closed form.
  have hd : U 1 1 = U.det * star (U 0 0) := by
    have h := congrFun (congrFun hstar 0) 0
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one, smul_eq_mul] at h
    rw [h, ← mul_assoc, hrmul, one_mul]
  have hb : U 0 1 = -(U.det * star (U 1 0)) := by
    have h := congrFun (congrFun hstar 0) 1
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul] at h
    rw [h, ← mul_assoc, hrmul, one_mul, neg_neg]
  -- Column `0` of `U` is a unit vector.
  have hcol : ‖U 0 0‖ ^ 2 + ‖U 1 0‖ ^ 2 = 1 := by
    have h := congrFun (congrFun hsUU 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
    simp only [← starRingEnd_apply] at h
    rw [Complex.conj_mul', Complex.conj_mul'] at h
    exact_mod_cast h
  -- `|det U| = 1`.
  have hdetnorm : ‖U.det‖ = 1 := by
    have hmul : ‖U.det‖ * ‖U.det‖ = 1 := by
      have e1 : ‖U.det‖ * ‖(star U).det‖ = 1 := by
        rw [← norm_mul, ← Matrix.det_mul, hUsU, Matrix.det_one, norm_one]
      rwa [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, norm_star] at e1
    rcases mul_self_eq_one_iff.1 hmul with h | h
    · exact h
    · have := norm_nonneg U.det; linarith
  -- Magnitude/angle facts for `γ = 2 arccos ‖U₀₀‖`.
  have hna1 : ‖U 0 0‖ ≤ 1 := by nlinarith [hcol, norm_nonneg (U 0 0), sq_nonneg ‖U 1 0‖]
  have hna0 : (-1 : ℝ) ≤ ‖U 0 0‖ := le_trans (by norm_num) (norm_nonneg _)
  have hcos : Real.cos (2 * Real.arccos ‖U 0 0‖ / 2) = ‖U 0 0‖ := by
    rw [show 2 * Real.arccos ‖U 0 0‖ / 2 = Real.arccos ‖U 0 0‖ by ring, Real.cos_arccos hna0 hna1]
  have hsin : Real.sin (2 * Real.arccos ‖U 0 0‖ / 2) = ‖U 1 0‖ := by
    rw [show 2 * Real.arccos ‖U 0 0‖ / 2 = Real.arccos ‖U 0 0‖ by ring, Real.sin_arccos,
      show 1 - ‖U 0 0‖ ^ 2 = ‖U 1 0‖ ^ 2 by linarith [hcol], Real.sqrt_sq (norm_nonneg _)]
  -- Polar forms.
  have hdet : U.det = Complex.exp ((↑U.det.arg : ℂ) * I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I U.det]
    rw [hdetnorm]; simp
  have hstarEq : ∀ z : ℂ, star z = (↑‖z‖ : ℂ) * Complex.exp (-↑z.arg * I) := by
    intro z
    have h := congrArg (starRingEnd ℂ) (Complex.norm_mul_exp_arg_mul_I z)
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I, show (↑z.arg : ℂ) * -I = -↑z.arg * I by ring] at h
    exact h.symm
  have detConj : ∀ z : ℂ,
      U.det * star z = (↑‖z‖ : ℂ) * Complex.exp ((↑U.det.arg - ↑z.arg) * I) := by
    intro z
    rw [hstarEq z]
    conv_lhs => rw [hdet]
    rw [show Complex.exp ((↑U.det.arg : ℂ) * I) * (↑‖z‖ * Complex.exp (-↑z.arg * I))
        = ↑‖z‖ * (Complex.exp ((↑U.det.arg : ℂ) * I) * Complex.exp (-↑z.arg * I)) by ring,
      ← Complex.exp_add,
      show ((↑U.det.arg : ℂ) * I + -↑z.arg * I) = (↑U.det.arg - ↑z.arg) * I by ring]
  have hU11 : U 1 1 = (↑‖U 0 0‖ : ℂ) * Complex.exp ((↑U.det.arg - ↑(U 0 0).arg) * I) := by
    rw [hd]; exact detConj (U 0 0)
  have hU01 : U 0 1 = -((↑‖U 1 0‖ : ℂ) * Complex.exp ((↑U.det.arg - ↑(U 1 0).arg) * I)) := by
    rw [hb, detConj (U 1 0)]
  -- The reassembly identity: `e^{iα} · e^{iw} · ↑m = ↑m · e^{iθ}` when `α + w = θ`.
  have fin4 : ∀ (m : ℝ) (w θ : ℂ), (↑(U.det.arg / 2) : ℂ) * I + w = θ →
      (↑m : ℂ) * Complex.exp θ
        = Complex.exp ((↑(U.det.arg / 2) : ℂ) * I) * (Complex.exp w * ↑m) := by
    intro m w θ hE
    rw [show Complex.exp ((↑(U.det.arg / 2) : ℂ) * I) * (Complex.exp w * ↑m)
          = ↑m * (Complex.exp ((↑(U.det.arg / 2) : ℂ) * I) * Complex.exp w) by ring,
        ← Complex.exp_add, hE]
  refine ⟨U.det.arg / 2, (U 1 0).arg - (U 0 0).arg, 2 * Real.arccos ‖U 0 0‖,
          U.det.arg - (U 0 0).arg - (U 1 0).arg, ?_⟩
  rw [rotZ_mul_rotY_mul_rotZ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.mk_zero, Fin.mk_one, smul_eq_mul, hcos, hsin]
  · -- (0,0): `U₀₀ = ‖U₀₀‖ e^{i arg U₀₀}`
    rw [← fin4 ‖U 0 0‖ _ (↑(U 0 0).arg * I) (by push_cast; ring),
      Complex.norm_mul_exp_arg_mul_I]
  · -- (0,1): `U₀₁ = -det U · conj U₁₀`
    rw [hU01, mul_neg, ← fin4 ‖U 1 0‖ _ ((↑U.det.arg - ↑(U 1 0).arg) * I) (by push_cast; ring)]
  · -- (1,0): `U₁₀ = ‖U₁₀‖ e^{i arg U₁₀}`
    rw [← fin4 ‖U 1 0‖ _ (↑(U 1 0).arg * I) (by push_cast; ring),
      Complex.norm_mul_exp_arg_mul_I]
  · -- (1,1): `U₁₁ = det U · conj U₀₀`
    rw [hU11, ← fin4 ‖U 0 0‖ _ ((↑U.det.arg - ↑(U 0 0).arg) * I) (by push_cast; ring)]

/-- The explicit `2 × 2` matrix of Nielsen & Chuang eq. (4.12): the Z–Y decomposition
`e^{iα} R_z(β) R_y(γ) R_z(δ)` written out entrywise, with the global phase `e^{iα}` folded into each
entry. Every entry is a phase `e^{i(α ± β/2 ± δ/2)}` times `cos(γ/2)` (diagonal) or `± sin(γ/2)`
(off-diagonal). This is the target form of N&C Exercise 4.9;
`zyMatrixForm_eq_smul_rotZ_mul_rotY_mul_rotZ` identifies it with the phased rotation product of the
Z–Y decomposition (`exists_zy_decomposition`). -/
noncomputable def zyMatrixForm (α β γ δ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (((α : ℂ) - (β : ℂ) / 2 - (δ : ℂ) / 2) * I) * (Real.cos (γ / 2) : ℂ),
     -(Complex.exp (((α : ℂ) - (β : ℂ) / 2 + (δ : ℂ) / 2) * I) * (Real.sin (γ / 2) : ℂ));
     Complex.exp (((α : ℂ) + (β : ℂ) / 2 - (δ : ℂ) / 2) * I) * (Real.sin (γ / 2) : ℂ),
     Complex.exp (((α : ℂ) + (β : ℂ) / 2 + (δ : ℂ) / 2) * I) * (Real.cos (γ / 2) : ℂ)]

/-- The explicit matrix form (4.12) equals the global-phase-times-rotations product of the Z–Y
decomposition: `zyMatrixForm α β γ δ = e^{iα} • (R_z(β) R_y(γ) R_z(δ))`. Folding the phase `e^{iα}`
into each entry of the closed form `rotZ_mul_rotY_mul_rotZ` and combining the two exponentials
turns the phased product into the entrywise matrix of N&C eq. (4.12). -/
theorem zyMatrixForm_eq_smul_rotZ_mul_rotY_mul_rotZ (α β γ δ : ℝ) :
    zyMatrixForm α β γ δ = Complex.exp ((α : ℂ) * I) • (rotZ β * rotY γ * rotZ δ) := by
  have key : ∀ (t p q r : ℂ), p = q + r →
      Complex.exp p * t = Complex.exp q * (Complex.exp r * t) := fun t p q r hpqr => by
    rw [hpqr, Complex.exp_add, mul_assoc]
  rw [rotZ_mul_rotY_mul_rotZ, zyMatrixForm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_zero, Fin.mk_one,
      smul_eq_mul, mul_neg]
  · exact key _ _ _ _ (by ring)
  · rw [neg_inj]; exact key _ _ _ _ (by ring)
  · exact key _ _ _ _ (by ring)
  · exact key _ _ _ _ (by ring)

/-- **Nielsen & Chuang, Exercise 4.9.** Any single-qubit unitary `U` (a `2 × 2` complex matrix with
`Uᴴ U = I`, i.e. `U ∈ Matrix.unitaryGroup (Fin 2) ℂ`) can be written in the explicit form (4.12):
there exist real numbers `α, β, γ, δ` with `U = zyMatrixForm α β γ δ`. Because `U` is unitary its
rows and columns are orthonormal, so the Z–Y decomposition (`exists_zy_decomposition`, Theorem 4.1)
yields angles with `U = e^{iα} R_z(β) R_y(γ) R_z(δ)`; rewriting that product entrywise via
`zyMatrixForm_eq_smul_rotZ_mul_rotY_mul_rotZ` puts `U` in the matrix form (4.12). -/
theorem exists_zyMatrixForm (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ δ : ℝ, U = zyMatrixForm α β γ δ := by
  obtain ⟨α, β, γ, δ, hUeq⟩ := exists_zy_decomposition U hU
  refine ⟨α, β, γ, δ, ?_⟩
  rw [hUeq, zyMatrixForm_eq_smul_rotZ_mul_rotY_mul_rotZ]

end AxQM.Concrete
