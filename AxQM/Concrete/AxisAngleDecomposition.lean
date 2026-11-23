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
# Concrete: the axis-angle decomposition of a single-qubit unitary (Nielsen & Chuang, Ex. 4.8(1))

Building on the rotation operator `rotAxis` of `Concrete/Rotation.lean` (N&C eq. 4.8), it proves
the **axis-angle decomposition** — the first part of **Nielsen & Chuang, Exercise 4.8** (eq. 4.9):
every single-qubit unitary `U` factors as

`U = e^{iα} R_n̂(θ)`

for some real numbers `α, θ` and a real *unit* three-vector `n̂`.
This is the `SU(2) = unit quaternions` fact behind the Bloch-sphere picture: modulo an overall
phase, a single-qubit gate is a rotation of the Bloch sphere.

"Unitary" is membership in `Matrix.unitaryGroup (Fin 2) ℂ` (`Uᴴ U = I`) — N&C's own definition; no
dimension or determinant is fixed, so this is Exercise 4.8(1) in full generality (all of `U(2)`),
the axis-angle analogue of Theorem 4.1's Z-Y decomposition (`exists_zy_decomposition`).

## Proof (the quaternion route)

Pull out the phase `α = arg(det U)/2`; then `V := e^{-iα} • U` has `det V = 1` (since
`|det U| = 1`), so `V ∈ SU(2)`. Unitarity with unit determinant forces (via `adjugate_fin_two`) the
`SU(2)` shape `V₁₁ = conj V₀₀`, `V₁₀ = -conj V₀₁`; expanding into real and imaginary parts gives the
*quaternion* identity `V = a • I + i (w₀ X + w₁ Y + w₂ Z)` with `a = Re V₀₀` and
`w = (Im V₀₁, Re V₀₁, Im V₀₀)`, and row-`0` orthonormality `‖V₀₀‖² + ‖V₀₁‖² = 1` gives
`‖w‖² = 1 - a²`. Choosing `θ = 2 arccos a` (so `cos(θ/2) = a`, `sin(θ/2) = ‖w‖`) and the unit axis
`n̂ = -w/‖w‖` (or `ẑ` when `w = 0`, `V = ±I`, keeping `n̂` genuinely unit) matches the closed form
`rotAxis_eq_of_unit` `cos(θ/2) I - i sin(θ/2) (n̂·σ)`, since `sin(θ/2) (n̂·σ) = -(w·σ)`. Finally
`U = e^{iα} V`. The grounded physics reading is in
`AxQM/NC/Ch4/Exercise4_8.lean`.
-/

namespace AxQM.Concrete

open Matrix Complex

set_option maxHeartbeats 400000 in
-- A single self-contained proof carries the whole `SU(2) = unit quaternions` argument —
-- phase extraction, the `adjugate_fin_two` `SU(2)` bookkeeping, the entrywise quaternion identity,
-- and the trig/`√` axis construction — so its elaboration runs to roughly twice the default budget.
/-- **Nielsen & Chuang, Exercise 4.8(1) (axis-angle decomposition of a single-qubit unitary).**
Every `2 × 2` unitary `U` (a single-qubit gate, `Uᴴ U = I`) factors as `U = e^{iα} R_n̂(θ)`
(eq. 4.9) for some real numbers `α, θ` and a real *unit* three-vector `n̂`
(`n₀² + n₁² + n₂² = 1`). The phase is `α = arg(det U)/2`; writing `V = e^{-iα} U ∈ SU(2)` in
quaternion form `V = a·I + i(w·σ)` with `a = Re V₀₀`, `w = (Im V₀₁, Re V₀₁, Im V₀₀)`, the angle is
`θ = 2 arccos a` and the axis `n̂ = -w/‖w‖` (or `ẑ` if `w = 0`). -/
theorem exists_axis_angle_decomposition (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (α θ : ℝ) (n : Fin 3 → ℝ), (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) ∧
      U = Complex.exp ((α : ℂ) * Complex.I) • rotAxis n θ := by
  -- Unitarity as the two products.
  have hUsU : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).1 hU
  have hsUU : star U * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hU
  -- `|det U| = 1`: `det U` is a unitary of the C⋆-ring `ℂ` (`Matrix.det_of_mem_unitary`).
  have hdetnorm : ‖U.det‖ = 1 :=
    CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)
  -- The phase `α = arg(det U)/2` and the unit-modulus scalar `c = e^{-iα}`.
  set α : ℝ := U.det.arg / 2 with hα
  set c : ℂ := Complex.exp (((-α : ℝ) : ℂ) * Complex.I) with hc
  have hcnorm : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I (-α)
  -- The `SU(2)` matrix `V = c • U`.
  set V : Matrix (Fin 2) (Fin 2) ℂ := c • U with hV
  -- `V` is unitary (unit scalar times unitary).
  have hcc : star c * c = 1 := by
    rw [← starRingEnd_apply, Complex.conj_mul', hcnorm]; norm_num
  have hcc' : c * star c = 1 := by rw [mul_comm]; exact hcc
  have hVsV : star V * V = 1 := by
    rw [hV, star_smul, smul_mul_smul_comm, hsUU, hcc, one_smul]
  have hVVs : V * star V = 1 := by
    rw [hV, star_smul, smul_mul_smul_comm, hUsU, hcc', one_smul]
  -- `det V = 1`.
  have hdetV : V.det = 1 := by
    have hd : U.det = Complex.exp ((↑U.det.arg : ℂ) * Complex.I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I U.det]
      rw [hdetnorm]; simp
    rw [hV, Matrix.det_smul, Fintype.card_fin, hc, hd, ← Complex.exp_nsmul, ← Complex.exp_add]
    rw [show (2 : ℕ) • (((-α : ℝ) : ℂ) * Complex.I) + (↑U.det.arg : ℂ) * Complex.I
        = ((2 * (-α) + U.det.arg : ℝ) : ℂ) * Complex.I by rw [hα]; push_cast; ring]
    rw [show (2 * (-α) + U.det.arg : ℝ) = 0 by rw [hα]; ring]
    simp
  -- The `SU(2)` entry constraints from `star V = V⁻¹ = adjugate V` (det V = 1).
  have hstarV : star V = !![V 1 1, -(V 0 1); -(V 1 0), V 0 0] := by
    rw [(Matrix.inv_eq_left_inv hVsV).symm, Matrix.inv_def, Matrix.adjugate_fin_two, hdetV,
      Ring.inverse_one, one_smul]
  have hF1 : V 1 1 = star (V 0 0) := by
    have h := congrFun (congrFun hstarV 0) 0
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one] at h
    exact h.symm
  have hF2 : V 1 0 = -star (V 0 1) := by
    have h := congrFun (congrFun hstarV 1) 0
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] at h
    rw [h, neg_neg]
  -- Row-`0` orthonormality `‖V₀₀‖² + ‖V₀₁‖² = 1`.
  have hF3 : Complex.normSq (V 0 0) + Complex.normSq (V 0 1) = 1 := by
    have h := congrFun (congrFun hVVs 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.one_apply_eq, ← starRingEnd_apply, Complex.mul_conj] at h
    exact_mod_cast h
  -- The quaternion coefficients.
  set a : ℝ := (V 0 0).re with ha
  set w : Fin 3 → ℝ := ![(V 0 1).im, (V 0 1).re, (V 0 0).im] with hw
  set nrm : ℝ := w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 with hnrmdef
  have hnrm : nrm = 1 - a ^ 2 := by
    simp only [hnrmdef, hw, ha, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    have := hF3
    simp only [Complex.normSq_apply] at this
    nlinarith [this]
  -- `V = a • I + i (w · σ)` (the quaternion identity).
  have hVform : V = !![V 0 0, V 0 1; -star (V 0 1), star (V 0 0)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta, Fin.mk_one]
    · exact hF2
    · exact hF1
  have hquat : V = (a : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Complex.I • pauliDot w := by
    rw [hVform, pauliDot_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [hw, ha, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, mul_one, Fin.isValue, Fin.zero_eta, Fin.mk_one, ite_true] <;>
      apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im]
  -- Bounds on `a` and the trig identities for `θ = 2 arccos a`.
  have ha_sq : a ^ 2 ≤ 1 := by
    have h0 := Complex.normSq_nonneg (V 0 1)
    have h1 : a ^ 2 ≤ Complex.normSq (V 0 0) := by
      rw [ha, Complex.normSq_apply]; nlinarith [sq_nonneg (V 0 0).im]
    linarith [hF3]
  have ha1 : a ≤ 1 := by nlinarith [ha_sq]
  have ha_ge : (-1 : ℝ) ≤ a := by nlinarith [ha_sq]
  set θ : ℝ := 2 * Real.arccos a with hθ
  set s : ℝ := Real.sqrt nrm with hs
  have hcos : Real.cos (θ / 2) = a := by
    rw [show θ / 2 = Real.arccos a by rw [hθ]; ring, Real.cos_arccos ha_ge ha1]
  have hsin : Real.sin (θ / 2) = s := by
    rw [show θ / 2 = Real.arccos a by rw [hθ]; ring, Real.sin_arccos, ← hnrm, hs]
  -- The unit axis: `-w/‖w‖ = (-1/s) • w`, or `ẑ` in the degenerate case `w = 0`.
  set n : Fin 3 → ℝ := if s = 0 then ![0, 0, 1] else (-1 / s : ℝ) • w with hn_def
  have hnrm_nonneg : 0 ≤ nrm := by rw [hnrmdef]; positivity
  have hs2 : s ^ 2 = nrm := Real.sq_sqrt hnrm_nonneg
  have hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    by_cases hs0 : s = 0
    · simp [hn_def, hs0]
    · simp only [hn_def, ite_eq_right hs0, Pi.smul_apply, smul_eq_mul]
      have hsne : s ≠ 0 := hs0
      have hs2' : s ^ 2 = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by rw [hs2, hnrmdef]
      field_simp
      nlinarith [hs2']
  -- `(s : ℂ) • (w · σ)` collapses to `-(w · σ)` on the chosen axis `n`.
  have hstep : (s : ℂ) • pauliDot n = -pauliDot w := by
    by_cases hs0 : s = 0
    · have hnrm0 : nrm = 0 := by
        have : s ^ 2 = 0 := by rw [hs0]; ring
        rw [hs2] at this; exact this
      have hw0 : w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 := by
        rw [hnrmdef] at hnrm0
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
      rw [hs0, Complex.ofReal_zero, zero_smul, eq_comm, neg_eq_zero, pauliDot, hw0.1, hw0.2.1,
        hw0.2.2]
      simp
    · have hsne : s ≠ 0 := hs0
      have hn_eq : n = (-1 / s : ℝ) • w := by rw [hn_def, ite_eq_right hs0]
      rw [hn_eq, pauliDot_smul, smul_smul]
      rw [show (s : ℂ) * ((-1 / s : ℝ) : ℂ) = ((s * (-1 / s) : ℝ) : ℂ) by push_cast; ring,
        show s * (-1 / s) = -1 by field_simp]
      simp
  -- `rotAxis n θ = V`.
  have hgoalV : rotAxis n θ = V := by
    have hpw : pauliDot w = -((s : ℂ) • pauliDot n) := by rw [hstep]; exact (neg_neg _).symm
    rw [rotAxis_eq_of_unit hn θ, hcos, hsin, hquat, hpw]
    module
  -- Reassemble `U = e^{iα} • rotAxis n θ`.
  refine ⟨α, θ, n, hn, ?_⟩
  have hac : Complex.exp ((α : ℂ) * Complex.I) * c = 1 := by
    rw [hc, ← Complex.exp_add,
      show (α : ℂ) * Complex.I + ((-α : ℝ) : ℂ) * Complex.I = 0 by push_cast; ring,
      Complex.exp_zero]
  rw [hgoalV, hV, smul_smul, hac, one_smul]

end AxQM.Concrete
