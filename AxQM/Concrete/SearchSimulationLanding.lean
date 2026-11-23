/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SearchSimulationStep

/-!
# Concrete: exact-landing geometry of the search-simulation step (Nielsen & Chuang, Exercise 6.10)

Nielsen & Chuang, Exercise 6.10 asks to choose the simulation time-step `Δt` so that the
continuous-time (Hamiltonian-simulation) quantum search lands **exactly** on the solution `|x⟩`
(probability `1`) in `O(√N)` queries, improving on the small-probability `Δt = π` special case.

The step operator (Exercise 6.9, `searchStep_eq`) is, up to a global phase `e^{−iΔt}`, the single
Bloch rotation `searchStepReduced Δt a b = R_r̂(θ)` about `r̂ = rotComposeUnitAxis` through
`θ = rotComposeAngle` (`searchStepReduced_eq_rotAxis`, Exercise 6.10). Both `⃗ψ = a` and
`ẑ = b = (0,0,1)` lie on the same circle of revolution about `r̂`, at azimuthal separation
`Φ = π − θ/2` (N&C's remark `⃗ψ·⃗r = ẑ·⃗r`). Hence `j` steps rotate `⃗ψ` to `ẑ` exactly when
`jθ = Φ`, i.e. `(2j+1)θ = 2π`.

This file proves that **geometric landing**:

* `rot3D_smul_invSqrt_eq` — a general Rodrigues identity: rotating `a` about the *unit-normalised*
  vector `v̂ = ‖v‖⁻¹ v` through `π − arccos C`, where `‖v‖² = 1 − C²`, equals
  `−C·a + (v×a) + (1+C)(v·a)‖v‖⁻² · v` — the `‖v‖`-normalisation cancelling cleanly.
* `searchStep_rot3D_land` — the landing itself: for a unit `⃗ψ = a`, with `b = ẑ`,
  `rot3D r̂ (π − θ/2) a = ẑ`. The `(1+C)(v·a)‖v‖⁻²·v` term collapses to
  `2 cos(Δt/2) · searchStepAxis` and the whole expression to `(0,0,1)` by `sin²+cos² = 1` and
  `‖⃗ψ‖ = 1`.
* `searchStepReduced_pow_conj_blochMatrix_land` — the **matrix conjugation form** (the statement of
  Exercise 6.10): when `(2j+1)θ = 2π`, the `j`-th power of the reduced search step
  conjugates the Bloch matrix of `⃗ψ` to that of `ẑ`, `U^j |ψ⟩⟨ψ| (U^j)† = |x⟩⟨x|`. Route:
  `rotAxis_pow` gives `U^j = R_r̂(jθ)`, `blochMatrix_conj_rotAxis` turns conjugation into
  `rot3D r̂ (jθ)`, and `jθ = π − θ/2` (from `(2j+1)θ = 2π`) with `searchStep_rot3D_land` lands it on
  `ẑ`. The global phase of `U(Δt)` is irrelevant here since it cancels in the conjugation
  (`searchStepReduced` is already phase-free).

The physical statement (final state `= |x⟩`, probability `1`) for `PureState`/`State` is in
`AxQM/NC/Ch6/Exercise6_10.lean`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- **Rodrigues rotation about a unit-normalised axis, at angle `π − arccos C`.** For a vector `v`
with `‖v‖² = 1 − C²` (and `‖v‖ > 0`), rotating `a` about the unit axis `v̂ = ‖v‖⁻¹ v` through the
angle `π − arccos C` is
`rot3D v̂ (π − arccos C) a = −C·a + (v×a) + (1+C)(v·a)‖v‖⁻² · v`.
The half-angle data are `cos(π − arccos C) = −C` and `sin(π − arccos C) = √(1−C²) = ‖v‖`; the two
`‖v‖⁻¹` factors of `v̂` combine with `sin = ‖v‖` so the `(v×a)` term loses its normalisation and the
`(v·a)v̂` term picks up `‖v‖⁻²`. Isolates the axis-normalisation algebra of the Exercise 6.10
landing `searchStep_rot3D_land`. -/
theorem rot3D_smul_invSqrt_eq (v a : Fin 3 → ℝ) (C : ℝ)
    (hSpos : 0 < v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)
    (hSC : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 - C ^ 2) :
    rot3D ((Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2))⁻¹ • v) (Real.pi - Real.arccos C) a
      = (-C) • a + crossProduct v a
        + ((1 + C) * (v ⬝ᵥ a) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)⁻¹) • v := by
  have hClt : C ^ 2 < 1 := by rw [hSC] at hSpos; linarith
  have hC1 : (-1 : ℝ) ≤ C := by nlinarith [hClt, sq_nonneg (C + 1)]
  have hC2 : C ≤ 1 := by nlinarith [hClt, sq_nonneg (C - 1)]
  set σ := Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) with hσ_def
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hSpos
  have hσne : σ ≠ 0 := hσpos.ne'
  have hσsq : σ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := Real.sq_sqrt hSpos.le
  have hcosφ : Real.cos (Real.pi - Real.arccos C) = -C := by
    rw [Real.cos_pi_sub, Real.cos_arccos hC1 hC2]
  have hsinφ : Real.sin (Real.pi - Real.arccos C) = σ := by
    rw [Real.sin_pi_sub, Real.sin_arccos, hσ_def, ← hSC]
  have hcross : crossProduct (σ⁻¹ • v) a = σ⁻¹ • crossProduct v a := by
    rw [map_smul, LinearMap.smul_apply]
  have hσinv : σ⁻¹ * σ⁻¹ = (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)⁻¹ := by
    rw [← mul_inv, ← pow_two, hσsq]
  rw [rot3D, hcosφ, hsinφ, hcross, smul_smul, mul_inv_cancel₀ hσne, one_smul,
    smul_dotProduct, smul_eq_mul, smul_smul]
  congr 2
  rw [← hσinv]; ring

/-- **Exercise 6.10 exact landing (Bloch-vector level).** For a unit Bloch vector `⃗ψ = a` and
`b = ẑ = (0,0,1)`, with a nonzero step half-angle (`sin(Δt/2) ≠ 0`) and nonzero composed axis
(`searchStepAxis ≠ 0`), rotating `⃗ψ` about the composed axis `r̂ = rotComposeUnitAxis` through the
half-turn-minus-half-angle `π − θ/2` (`θ = rotComposeAngle`) lands exactly on `ẑ`:
`rot3D r̂ (π − θ/2) ⃗ψ = ẑ`.
This is the geometric heart of N&C Exercise 6.10: `⃗ψ` and `ẑ` sit on the same circle of revolution
about `r̂` at azimuthal separation `π − θ/2`. Proof: `rot3D_smul_invSqrt_eq` reduces the normalised
rotation to `−C·⃗ψ + (v×⃗ψ) + (1+C)(v·⃗ψ)‖v‖⁻²·v` (`v = rotComposeVec`,
`C = rotComposeCos = c²−s²ψ_z`); `v = 2s·searchStepAxis` and `(1+C)(v·⃗ψ)·2s = 2c·‖v‖²` collapse the
last term to `2c·searchStepAxis`, after which each component is `sin²+cos² = 1` and `‖⃗ψ‖ = 1`. -/
theorem searchStep_rot3D_land {a : Fin 3 → ℝ}
    (ha : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) (Δt : ℝ)
    (hs : Real.sin (Δt / 2) ≠ 0)
    (hax : (searchStepAxis Δt a ![0, 0, 1]) 0 ^ 2 + (searchStepAxis Δt a ![0, 0, 1]) 1 ^ 2
        + (searchStepAxis Δt a ![0, 0, 1]) 2 ^ 2 ≠ 0) :
    rot3D (rotComposeUnitAxis Δt ![0, 0, 1] Δt a)
        (Real.pi - rotComposeAngle Δt ![0, 0, 1] Δt a / 2) a = ![0, 0, 1] := by
  have hb : (![0, 0, 1] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, 1] : Fin 3 → ℝ) 1 ^ 2
      + (![0, 0, 1] : Fin 3 → ℝ) 2 ^ 2 = 1 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]; norm_num
  have hcs : Real.cos (Δt / 2) ^ 2 + Real.sin (Δt / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have hvsw : rotComposeVec Δt ![0, 0, 1] Δt a
      = (2 * Real.sin (Δt / 2)) • searchStepAxis Δt a ![0, 0, 1] :=
    rotComposeVec_eq_smul_searchStepAxis Δt a ![0, 0, 1]
  have hSpos : 0 < (rotComposeVec Δt ![0, 0, 1] Δt a) 0 ^ 2
      + (rotComposeVec Δt ![0, 0, 1] Δt a) 1 ^ 2 + (rotComposeVec Δt ![0, 0, 1] Δt a) 2 ^ 2 :=
    rotComposeVec_normSq_pos (a := a) (b := ![0, 0, 1]) Δt hs hax
  have hSC : (rotComposeVec Δt ![0, 0, 1] Δt a) 0 ^ 2 + (rotComposeVec Δt ![0, 0, 1] Δt a) 1 ^ 2
      + (rotComposeVec Δt ![0, 0, 1] Δt a) 2 ^ 2 = 1 - (rotComposeCos Δt ![0, 0, 1] Δt a) ^ 2 :=
    rotComposeVec_normSq hb ha Δt Δt
  rw [rotComposeAngle_div_two, rotComposeUnitAxis, rot3D_smul_invSqrt_eq _ a _ hSpos hSC]
  set C := rotComposeCos Δt ![0, 0, 1] Δt a with hC_def
  set S := (rotComposeVec Δt ![0, 0, 1] Δt a) 0 ^ 2 + (rotComposeVec Δt ![0, 0, 1] Δt a) 1 ^ 2
      + (rotComposeVec Δt ![0, 0, 1] Δt a) 2 ^ 2 with hS_def
  have hC : C = Real.cos (Δt / 2) ^ 2 - Real.sin (Δt / 2) ^ 2 * a 2 := by
    rw [hC_def, rotComposeCos]
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hva : rotComposeVec Δt ![0, 0, 1] Δt a ⬝ᵥ a
      = Real.sin (Δt / 2) * Real.cos (Δt / 2) * (1 + a 2) := by
    rw [hvsw, smul_dotProduct, smul_eq_mul, searchStepAxis]
    simp only [cross_apply, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    linear_combination (Real.sin (Δt / 2) * Real.cos (Δt / 2)) * ha
  have hSne : S ≠ 0 := hSpos.ne'
  have hcoef : (1 + C) * (Real.sin (Δt / 2) * Real.cos (Δt / 2) * (1 + a 2))
        * (2 * Real.sin (Δt / 2))
      = 2 * Real.cos (Δt / 2) * S := by
    rw [hSC, hC]
    linear_combination
      (2 * Real.cos (Δt / 2) * (Real.cos (Δt / 2) ^ 2 + 1 - Real.sin (Δt / 2) ^ 2 * a 2)) * hcs
  have hterm3 : ((1 + C) * (rotComposeVec Δt ![0, 0, 1] Δt a ⬝ᵥ a) * S⁻¹)
        • rotComposeVec Δt ![0, 0, 1] Δt a
      = (2 * Real.cos (Δt / 2)) • searchStepAxis Δt a ![0, 0, 1] := by
    rw [hva, hvsw, smul_smul]
    congr 1
    field_simp
    linear_combination hcoef / 2
  rw [hterm3]
  have hcrossv : crossProduct (rotComposeVec Δt ![0, 0, 1] Δt a) a
      = (2 * Real.sin (Δt / 2)) • crossProduct (searchStepAxis Δt a ![0, 0, 1]) a := by
    rw [hvsw, map_smul, LinearMap.smul_apply]
  rw [hcrossv, hC]
  -- Freeze `cos(Δt/2)`, `sin(Δt/2)` as opaque `c, s` so the componentwise `simp` cannot rewrite the
  -- angle `Δt/2` into a variant form; the remaining identity is `sin²+cos² = 1` and `‖⃗ψ‖ = 1`.
  simp only [searchStepAxis]
  generalize hgc : Real.cos (Δt / 2) = c
  generalize hgs : Real.sin (Δt / 2) = s
  have hcs' : c ^ 2 + s ^ 2 = 1 := by rw [← hgc, ← hgs]; exact hcs
  funext i
  fin_cases i <;> simp [cross_apply, Matrix.vecHead, Matrix.vecTail]
  · ring
  · ring
  · linear_combination s ^ 2 * ha + hcs'

/-- **Exercise 6.10 exact landing (Bloch-matrix conjugation form).** For a unit Bloch vector
`⃗ψ = a` and `b = ẑ = (0,0,1)`, with `sin(Δt/2) ≠ 0`, nonzero composed axis, and step count `j`
tuned so that `(2j+1)·θ = 2π` (`θ = rotComposeAngle`, the exact-landing condition
`jθ = π − θ/2`), the `j`-th power of the reduced search step conjugates the Bloch matrix of `⃗ψ` to
that of `ẑ`:
`(searchStepReduced Δt a ẑ)^j · blochMatrix a · ((searchStepReduced Δt a ẑ)^j)† = blochMatrix ẑ`,
i.e. `U(Δt)^j |ψ⟩⟨ψ| (U(Δt)^j)† = |x⟩⟨x|` (the global phase of `U(Δt)` cancels in the conjugation).
Proof: `searchStepReduced_eq_rotAxis` presents the step as one `rotAxis r̂ θ`; `rotAxis_pow` gives
`(rotAxis r̂ θ)^j = rotAxis r̂ (jθ)`; `blochMatrix_conj_rotAxis` turns the conjugation into
`blochMatrix (rot3D r̂ (jθ) a)`; and `jθ = π − θ/2` (from `(2j+1)θ = 2π`) with
`searchStep_rot3D_land` gives `rot3D r̂ (jθ) a = ẑ`. -/
theorem searchStepReduced_pow_conj_blochMatrix_land {a : Fin 3 → ℝ}
    (ha : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) (Δt : ℝ)
    (hs : Real.sin (Δt / 2) ≠ 0)
    (hax : (searchStepAxis Δt a ![0, 0, 1]) 0 ^ 2 + (searchStepAxis Δt a ![0, 0, 1]) 1 ^ 2
        + (searchStepAxis Δt a ![0, 0, 1]) 2 ^ 2 ≠ 0)
    (j : ℕ)
    (hj : (2 * (j : ℝ) + 1) * rotComposeAngle Δt ![0, 0, 1] Δt a = 2 * Real.pi) :
    (searchStepReduced Δt a ![0, 0, 1]) ^ j * blochMatrix a
        * ((searchStepReduced Δt a ![0, 0, 1]) ^ j)ᴴ = blochMatrix ![0, 0, 1] := by
  have hb : (![0, 0, 1] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, 1] : Fin 3 → ℝ) 1 ^ 2
      + (![0, 0, 1] : Fin 3 → ℝ) 2 ^ 2 = 1 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]; norm_num
  have hVne : (rotComposeVec Δt ![0, 0, 1] Δt a) 0 ^ 2 + (rotComposeVec Δt ![0, 0, 1] Δt a) 1 ^ 2
      + (rotComposeVec Δt ![0, 0, 1] Δt a) 2 ^ 2 ≠ 0 :=
    (rotComposeVec_normSq_pos (a := a) (b := ![0, 0, 1]) Δt hs hax).ne'
  have hrunit : (rotComposeUnitAxis Δt ![0, 0, 1] Δt a) 0 ^ 2
      + (rotComposeUnitAxis Δt ![0, 0, 1] Δt a) 1 ^ 2
      + (rotComposeUnitAxis Δt ![0, 0, 1] Δt a) 2 ^ 2 = 1 :=
    rotComposeUnitAxis_normSq Δt Δt hVne
  rw [searchStepReduced_eq_rotAxis ha hb Δt hs hax, rotAxis_pow, blochMatrix_conj_rotAxis hrunit]
  congr 1
  have hangle : (j : ℝ) * rotComposeAngle Δt ![0, 0, 1] Δt a
      = Real.pi - rotComposeAngle Δt ![0, 0, 1] Δt a / 2 := by
    have hexp : (2 * (j : ℝ) + 1) * rotComposeAngle Δt ![0, 0, 1] Δt a
        = 2 * ((j : ℝ) * rotComposeAngle Δt ![0, 0, 1] Δt a)
          + rotComposeAngle Δt ![0, 0, 1] Δt a := by ring
    linarith [hj, hexp]
  rw [hangle]
  exact searchStep_rot3D_land ha Δt hs hax

end AxQM.Concrete
