/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.GroverRotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Order.Round

/-!
# Concrete: iterating the Grover search, and its success guarantee (Nielsen & Chuang, Exercise 6.4)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §6.1.3–6.1.4 (pp. 252–254) analyse
the quantum search algorithm. Exercise 6.4 asks to give the explicit steps of that algorithm for the
**multiple-solution** case `1 < M < N/2` (the boxed `M = 1` "Algorithm: Quantum search" on p. 254
being the special case). The only substance distinguishing the general `M` case from `M = 1` is the
number of Grover iterations `R` and the guarantee that after them a measurement returns a solution
with probability at least `1/2`. This file supplies that analytic substance, over the
two-dimensional `|α⟩, |β⟩` plane in which the whole geometric picture lives (Exercise 6.3 already
established that the Grover iteration is a rotation there; see
`AxQM/Concrete/GroverRotation.lean`).

## Setting

Everything here is mathematics over `ℂ²` (`Fin 2 → ℂ`) and real trigonometry. The physical part of
Exercise 6.4 — that measuring the final state in the computational basis yields a solution with
probability `≥ 1/2` (the Born rule) — is grounded separately, consuming the results proved here.

## Contents

* `planeState φ` — the unit vector `cos φ |α⟩ + sin φ |β⟩` at angle `φ` from `|α⟩` in the plane
  `span{|α⟩, |β⟩}` (with `|α⟩ = stdVec 0`, `|β⟩ = stdVec 1`); `groverState θ = planeState (θ/2)`
  (`groverState_eq_planeState`).
* `groverRotation_mulVec_planeState` — the rotation acts on a plane state by adding to its angle:
  `G · (cos φ |α⟩ + sin φ |β⟩) = cos(φ+θ) |α⟩ + sin(φ+θ) |β⟩`.
* `groverIteration_pow_mulVec_groverState` — **N&C Eq. 6.12**: `k` Grover iterations rotate the
  starting state `|ψ⟩` (at `θ/2`) to `cos((2k+1)θ/2) |α⟩ + sin((2k+1)θ/2) |β⟩`.
* `sin_sq_ge_half_of_abs_sub_pi_div_two_le` — the success bound: `sin² x ≥ 1/2` whenever `x` is
  within `π/4` of `π/2` (i.e. the state is within `π/4` of the all-solutions vector `|β⟩`).
* `grover_multipleSolutions_success` — **the Exercise 6.4 guarantee (N&C Eqs. 6.15–6.17)**: for the
  Grover angle `θ` with `sin(θ/2) = √(M/N)` and `M ≤ N/2` (`0 < θ ≤ π/2`), there is a number of
  iterations `R` with `sin²((2R+1)θ/2) ≥ 1/2` (a solution is found with probability `≥ 1/2`) and
  `R ≤ (π/4)·√(N/M)` (`O(√(N/M))` oracle calls — the quadratic speedup).
-/

namespace AxQM.Concrete

open Matrix

/-- **The plane state at angle `φ`**: the unit vector `cos φ |α⟩ + sin φ |β⟩` of `ℂ²`, at angle `φ`
from `|α⟩` in the plane `span{|α⟩, |β⟩}` (with `|α⟩ = stdVec 0`, `|β⟩ = stdVec 1`). The generic
point of N&C's geometric picture (§6.1.3): the Grover iteration rotates it, and the starting state
and the all-solutions vector are `planeState (θ/2)` and `planeState (π/2) = |β⟩`. -/
noncomputable def planeState (φ : ℝ) : Fin 2 → ℂ :=
  (Real.cos φ : ℂ) • stdVec 0 + (Real.sin φ : ℂ) • stdVec 1

@[simp] theorem planeState_apply_zero (φ : ℝ) : planeState φ 0 = (Real.cos φ : ℂ) := by
  simp [planeState, stdVec]

@[simp] theorem planeState_apply_one (φ : ℝ) : planeState φ 1 = (Real.sin φ : ℂ) := by
  simp [planeState, stdVec]

/-- The Grover starting state `|ψ⟩` is the plane state at angle `θ/2` (N&C Eq. 6.10). -/
theorem groverState_eq_planeState (θ : ℝ) : groverState θ = planeState (θ / 2) := rfl

/-- **The rotation acts on a plane state by adding its angle** (N&C §6.1.3): the Grover rotation
matrix sends `cos φ |α⟩ + sin φ |β⟩` to `cos(φ+θ) |α⟩ + sin(φ+θ) |β⟩`. The one-step engine behind
Eq. 6.12 — the cosine/sine angle-addition formulas read off the `[[cosθ,−sinθ],[sinθ,cosθ]]`
matrix-vector product. -/
theorem groverRotation_mulVec_planeState (θ φ : ℝ) :
    groverRotation θ *ᵥ planeState φ = planeState (φ + θ) := by
  have hc : (Real.cos (φ + θ) : ℂ)
      = (Real.cos θ : ℂ) * (Real.cos φ : ℂ) - (Real.sin θ : ℂ) * (Real.sin φ : ℂ) := by
    rw [Real.cos_add]; push_cast; ring
  have hs : (Real.sin (φ + θ) : ℂ)
      = (Real.sin θ : ℂ) * (Real.cos φ : ℂ) + (Real.cos θ : ℂ) * (Real.sin φ : ℂ) := by
    rw [Real.sin_add]; push_cast; ring
  funext i
  fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, groverRotation, planeState_apply_zero,
      planeState_apply_one, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
      Fin.zero_eta, Fin.mk_one] <;>
    first
      | linear_combination -hc
      | linear_combination -hs

/-- **Iterating the rotation** `k` times rotates a plane state by `k·θ`:
`Gᵏ · (cos φ |α⟩ + sin φ |β⟩) = cos(φ + kθ) |α⟩ + sin(φ + kθ) |β⟩`. Induction on `k` from the
one-step `groverRotation_mulVec_planeState`. -/
theorem groverRotation_pow_mulVec_planeState (θ φ : ℝ) (k : ℕ) :
    (groverRotation θ) ^ k *ᵥ planeState φ = planeState (φ + k * θ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, groverRotation_mulVec_planeState]
    congr 1
    push_cast
    ring

/-- **Nielsen & Chuang, Eq. 6.12.** After `k` Grover iterations the starting state `|ψ⟩` (at angle
`θ/2` from `|α⟩`) has been rotated to `cos((2k+1)θ/2) |α⟩ + sin((2k+1)θ/2) |β⟩` — it sits at angle
`(2k+1)θ/2`, rotating by `θ` per iteration towards the all-solutions vector `|β⟩` (at `π/2`). -/
theorem groverIteration_pow_mulVec_groverState (θ : ℝ) (k : ℕ) :
    (groverIteration θ) ^ k *ᵥ groverState θ = planeState ((2 * k + 1) * θ / 2) := by
  rw [groverState_eq_planeState, groverIteration_eq_rotation, groverRotation_pow_mulVec_planeState]
  congr 1
  ring

/-- **The success bound.** If the final angle `x` is within `π/4` of `π/2` (the state is within
`π/4` of the all-solutions vector `|β⟩`), then `sin² x ≥ 1/2`: measuring the plane state
`cos x |α⟩ + sin x |β⟩` in the `|α⟩, |β⟩` basis returns the `|β⟩` (solution) outcome with
probability `sin² x ≥ 1/2`. Proof: `sin² x = 1/2 − cos(2x)/2`, and `2x ∈ [π/2, 3π/2]` gives
`cos(2x) ≤ 0`. -/
theorem sin_sq_ge_half_of_abs_sub_pi_div_two_le {x : ℝ} (h : |x - Real.pi / 2| ≤ Real.pi / 4) :
    (1 : ℝ) / 2 ≤ Real.sin x ^ 2 := by
  rw [abs_le] at h
  have h1 : Real.pi / 2 ≤ 2 * x := by linarith [h.1]
  have h2 : 2 * x ≤ Real.pi + Real.pi / 2 := by linarith [h.2]
  have hcos : Real.cos (2 * x) ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
  have hsin : Real.sin x ^ 2 = 1 / 2 - Real.cos (2 * x) / 2 := by
    rw [Real.sin_sq, Real.cos_sq]; ring
  linarith

/-- **Nielsen & Chuang, Exercise 6.4 — the multiple-solution search succeeds in `O(√(N/M))` steps.**
Let `θ` be the Grover rotation angle of an `M`-solution problem, `sin(θ/2) = √(M/N)` (N&C Eq. 6.10),
with `1 ≤ M ≤ N/2` (encoded as `0 < M`, `2M ≤ N`, and `0 < θ ≤ π/2`). Then there is a number of
Grover iterations `R : ℕ` such that

* `sin²((2R+1)θ/2) ≥ 1/2` — after `R` iterations, measuring the state in the computational basis
  returns a solution with probability at least one half (N&C Eq. 6.15's `θ/2 ≤ π/4` closeness); and
* `R ≤ (π/4)·√(N/M)` — only `O(√(N/M))` iterations (hence oracle calls) are needed (N&C Eq. 6.17),
  a quadratic speedup over the `O(N/M)` classical cost.

`R` is the integer closest to `(π/2 − θ/2)/θ = arccos√(M/N)/θ` (N&C Eq. 6.15): rounding lands the
final angle `(2R+1)θ/2` within `θ/2 ≤ π/4` of `|β⟩`; the count bound uses `θ/2 ≥ sin(θ/2) = √(M/N)`
(N&C Eq. 6.16). -/
theorem grover_multipleSolutions_success
    (N M θ : ℝ) (hM : 0 < M) (hMN : 2 * M ≤ N)
    (hθ0 : 0 < θ) (hθ2 : θ ≤ Real.pi / 2)
    (hsin : Real.sin (θ / 2) = Real.sqrt (M / N)) :
    ∃ R : ℕ, (1 : ℝ) / 2 ≤ Real.sin ((2 * (R : ℝ) + 1) * θ / 2) ^ 2
      ∧ (R : ℝ) ≤ Real.pi / 4 * Real.sqrt (N / M) := by
  have hπ := Real.pi_pos
  have hN : 0 < N := by linarith
  -- `y` = the ideal (real) number of iterations `(π/2 − θ/2)/θ`; `R₀ = round y`.
  set y : ℝ := (Real.pi / 2 - θ / 2) / θ with hy
  have hy_ge : (1 : ℝ) / 2 ≤ y := by
    rw [hy, le_div_iff₀ hθ0]; nlinarith
  have hround := abs_sub_round y
  rw [abs_le] at hround
  have hR0_nonneg : 0 ≤ round y := by
    have : (0 : ℝ) ≤ (round y : ℝ) := by linarith [hround.2]
    exact_mod_cast this
  have hRcast : ((round y).toNat : ℝ) = (round y : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hR0_nonneg
  refine ⟨(round y).toNat, ?_, ?_⟩
  · -- Success: the final angle is within `θ/2 ≤ π/4` of `π/2`, so `sin² ≥ 1/2`.
    rw [hRcast]
    apply sin_sq_ge_half_of_abs_sub_pi_div_two_le
    have heq : (2 * (round y : ℝ) + 1) * θ / 2 - Real.pi / 2 = ((round y : ℝ) - y) * θ := by
      rw [hy]; field_simp; ring
    rw [heq, abs_mul, abs_of_pos hθ0]
    have hlt : |(round y : ℝ) - y| ≤ 1 / 2 := by rw [abs_sub_comm, abs_le]; exact hround
    calc |(round y : ℝ) - y| * θ ≤ (1 / 2) * θ := mul_le_mul_of_nonneg_right hlt hθ0.le
      _ ≤ Real.pi / 4 := by linarith
  · -- Count: `R ≤ π/(2θ)` and `θ/2 ≥ √(M/N)`, giving `R ≤ (π/4)·√(N/M)`.
    rw [hRcast]
    have hsmn : Real.sqrt (M / N) ≤ θ / 2 := by
      rw [← hsin]; exact (Real.sin_lt (by linarith)).le
    have hsmn_nonneg : 0 ≤ Real.sqrt (M / N) := Real.sqrt_nonneg _
    -- `R ≤ π/(2θ)`.
    have hRy : (round y : ℝ) ≤ Real.pi / (2 * θ) := by
      have hle : (round y : ℝ) ≤ y + 1 / 2 := by linarith [hround.1]
      have hval : y + 1 / 2 = Real.pi / (2 * θ) := by rw [hy]; field_simp; ring
      rw [hval] at hle; exact hle
    -- `R·√(M/N) ≤ π/(2θ)·√(M/N) ≤ π/(2θ)·(θ/2) = π/4`.
    have hprod : (round y : ℝ) * Real.sqrt (M / N) ≤ Real.pi / 4 := by
      have h1 : (round y : ℝ) * Real.sqrt (M / N) ≤ Real.pi / (2 * θ) * Real.sqrt (M / N) :=
        mul_le_mul_of_nonneg_right hRy hsmn_nonneg
      have h2 : Real.pi / (2 * θ) * Real.sqrt (M / N) ≤ Real.pi / (2 * θ) * (θ / 2) :=
        mul_le_mul_of_nonneg_left hsmn (by positivity)
      have h3 : Real.pi / (2 * θ) * (θ / 2) = Real.pi / 4 := by field_simp; ring
      linarith
    -- Convert `R·√(M/N) ≤ π/4` to `R ≤ (π/4)·√(N/M)` using `√(M/N)·√(N/M) = 1`.
    have hprod1 : Real.sqrt (M / N) * Real.sqrt (N / M) = 1 := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [show M / N * (N / M) = 1 by field_simp]
      exact Real.sqrt_one
    have hmul := mul_le_mul_of_nonneg_right hprod (Real.sqrt_nonneg (N / M))
    calc (round y : ℝ)
        = (round y : ℝ) * (Real.sqrt (M / N) * Real.sqrt (N / M)) := by rw [hprod1, mul_one]
      _ = (round y : ℝ) * Real.sqrt (M / N) * Real.sqrt (N / M) := by ring
      _ ≤ Real.pi / 4 * Real.sqrt (N / M) := hmul

end AxQM.Concrete
