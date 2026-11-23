/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SpecialOrthogonalFixedAxis
import AxQM.Concrete.BlochRotation
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Concrete: the axis–angle decomposition of a proper rotation of `ℝ³`

This file supplies the pure linear-algebra content behind the **axis–angle decomposition** of a
proper rotation, the second ingredient (after the axis-existence theorem
`Concrete.exists_unit_mulVec_self_of_mem_specialOrthogonalGroup`, Euler's theorem) of the qubit
converse of **Nielsen & Chuang, Problem 8.3** (p. 396):

> **Axis–angle decomposition.** For every `O ∈ SO(3)` there is a *unit* axis `n̂` and an angle `θ`
> with `O v = rot3D n̂ θ v` for all `v`: `O` is the Rodrigues rotation by `θ` about `n̂`.

## Context in N&C

Problem 8.3's qubit direction realises a unital single-qubit channel's Bloch matrix `M` as
`M = O₁ · diagonal d · O₂` (`Concrete.exists_specialOrthogonalGroup_diagonal_factor`), then must
realise the proper rotations `O₁, O₂ ∈ SO(3)` as *unitary conjugations* on the Bloch sphere (the
`SU(2) → SO(3)` cover, forward direction `Concrete.blochRotationOfUnitary`). The surjectivity of
that cover reduces to this axis–angle decomposition: once `O = rot3D n̂ θ`, the qubit rotation gate
`rotAxis n̂ θ` realises it (`Concrete.pauliDot_conj_rotAxis`, N&C Ex. 4.6), closing the converse.

## The proof (the orthonormal-frame argument)

Euler's theorem gives a unit axis `n` fixed by `O` (`O n = n`). Complete `n` to a right-handed
orthonormal frame `{n, u, w}` with `w = n × u` (`exists_unit_dotProduct_zero` for the perpendicular
`u`; `frame_expansion` for the resulting basis). Because `O` is orthogonal it preserves the dot
product (`mulVec_dotProduct_mulVec_of_mem_orthogonalGroup`), so `O u` lies in the `n`-orthogonal
plane: `O u = c • u + s • w` with `c² + s² = 1`; pick `θ` with `cos θ = c`, `sin θ = s`. Then
`O u = rot3D n θ u`. Because `O ∈ SO(3)` it also preserves the cross product
(`mulVec_crossProduct_of_mem_specialOrthogonalGroup`), so
`O w = O (n × u) = (O n) × (O u) = n × (c • u + s • w) = -s • u + c • w = rot3D n θ w`. The two maps
agree on `n` (both fix it), `u`, and `w`; since `{n, u, w}` spans `ℝ³` and both maps are `ℝ`-linear,
they agree on every `v`.

Compare the companion files `AxQM/Concrete/SpecialOrthogonalFixedAxis.lean` and
`AxQM/Concrete/BlochRotation.lean`.
-/

namespace AxQM.Concrete

open Matrix

/-- **`rot3D` is additive** in its vector argument: `rot3D n θ (a + b) = rot3D n θ a + rot3D n θ b`.
Each Rodrigues term (`cos θ • v`, `sin θ • (n × v)`, `(1 − cos θ)(n·v) • n`) is linear in `v`. -/
theorem rot3D_add (n : Fin 3 → ℝ) (θ : ℝ) (a b : Fin 3 → ℝ) :
    rot3D n θ (a + b) = rot3D n θ a + rot3D n θ b := by
  simp only [rot3D, map_add, dotProduct_add]
  module

/-- **`rot3D` is homogeneous** in its vector argument: `rot3D n θ (c • a) = c • rot3D n θ a`.
Each Rodrigues term is linear in `v`. -/
theorem rot3D_smul (n : Fin 3 → ℝ) (θ : ℝ) (c : ℝ) (a : Fin 3 → ℝ) :
    rot3D n θ (c • a) = c • rot3D n θ a := by
  simp only [rot3D, map_smul, dotProduct_smul, smul_eq_mul]
  module

/-- **The Binet/Lagrange cross-product identity under a matrix.** For any `3 × 3` matrix `O`,
`Oᵀ ((O u) × (O v)) = det O • (u × v)`. A polynomial identity in the entries of `O` and the
components of `u, v`, proved by `ring` after expanding the matrix operations. It is the algebraic
core of `mulVec_crossProduct_of_mem_specialOrthogonalGroup`. -/
theorem transpose_mulVec_crossProduct_mulVec (O : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
    Oᵀ.mulVec (crossProduct (O.mulVec u) (O.mulVec v)) = O.det • crossProduct u v := by
  funext i
  fin_cases i <;>
    simp only [Fin.isValue, Fin.reduceFinMk, Matrix.mulVec, Matrix.transpose_apply,
      dotProduct, cross_apply, Fin.sum_univ_three, Matrix.det_fin_three, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] <;>
    ring

/-- **`SO(3)` preserves the cross product.** For `O ∈ SO(3)`,
`O (u × v) = (O u) × (O v)`. From the Binet identity `Oᵀ ((O u) × (O v)) = det O • (u × v) = u × v`
(det `O = 1`), left-multiplied by `O` (using `O Oᵀ = 1`). -/
theorem mulVec_crossProduct_of_mem_specialOrthogonalGroup
    {O : Matrix (Fin 3) (Fin 3) ℝ} (hO : O ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (u v : Fin 3 → ℝ) :
    O.mulVec (crossProduct u v) = crossProduct (O.mulVec u) (O.mulVec v) := by
  obtain ⟨hOorth, hdet⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hO
  have hOtO : Oᵀ * O = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hOorth
  have hOOt : O * Oᵀ = 1 := mul_eq_one_comm.mp hOtO
  have key := transpose_mulVec_crossProduct_mulVec O u v
  rw [hdet, one_smul] at key
  calc O.mulVec (crossProduct u v)
      = O.mulVec (Oᵀ.mulVec (crossProduct (O.mulVec u) (O.mulVec v))) := by rw [key]
    _ = (O * Oᵀ).mulVec (crossProduct (O.mulVec u) (O.mulVec v)) := by rw [Matrix.mulVec_mulVec]
    _ = crossProduct (O.mulVec u) (O.mulVec v) := by rw [hOOt, Matrix.one_mulVec]

/-- **An orthogonal matrix preserves the dot product.** For `O` in the orthogonal group over any
finite index type, `(O x) ⬝ᵥ (O y) = x ⬝ᵥ y`. From `Oᵀ O = 1`; nothing three-dimensional is used. -/
theorem mulVec_dotProduct_mulVec_of_mem_orthogonalGroup {m : Type*} [Fintype m] [DecidableEq m]
    {O : Matrix m m ℝ} (hO : O ∈ Matrix.orthogonalGroup m ℝ)
    (x y : m → ℝ) :
    (O.mulVec x) ⬝ᵥ (O.mulVec y) = x ⬝ᵥ y := by
  have hOtO : Oᵀ * O = 1 := (Matrix.mem_orthogonalGroup_iff' m ℝ).mp hO
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hOtO,
    Matrix.one_mulVec]

/-- **An orthogonal transformation preserves the Bloch-ball length.** For `O ∈ O(3)` the squared
length `r₀² + r₁² + r₂²` is invariant under `r ↦ O r`, so an orthogonal map (in particular a proper
`SO(3)` rotation) sends the closed unit ball to itself. Only **orthogonality** is used — the
determinant plays no role — so the hypothesis is `orthogonalGroup`, not `specialOrthogonalGroup`.
Immediate from `mulVec_dotProduct_mulVec_of_mem_orthogonalGroup` (orthogonality preserves the dot
product): `∑ (O r)ᵢ² = (O r) ⬝ᵥ (O r) = r ⬝ᵥ r = ∑ rᵢ²`. The `Fin 3` sum-of-squares *form* is kept
(not generalised) because it is exactly the ball hypothesis of `blochState`: the membership fact
needed to feed an `O r` back into `blochState` when assembling the qubit converse of Nielsen &
Chuang, Problem 8.3 (realising the singular-value rotations of a unital channel's Bloch matrix as
unitary conjugations requires the rotated Bloch vectors to stay in the ball). -/
theorem mem_orthogonalGroup_mulVec_sq_sum {O : Matrix (Fin 3) (Fin 3) ℝ}
    (hO : O ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (r : Fin 3 → ℝ) :
    (O.mulVec r) 0 ^ 2 + (O.mulVec r) 1 ^ 2 + (O.mulVec r) 2 ^ 2
      = r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 := by
  have key := mulVec_dotProduct_mulVec_of_mem_orthogonalGroup hO r r
  simp only [dotProduct, Fin.sum_univ_three] at key
  nlinarith [key]

/-- **The special orthogonal group is closed under transpose.** If `O ∈ SO(n)` over a commutative
ring `R`, then `Oᵀ ∈ SO(n)`: `Oᵀ` is orthogonal because `(Oᵀ)ᵀ · Oᵀ = O · Oᵀ = 1` (orthogonality
of `O`), and `det Oᵀ = det O = 1`. Nothing about the index type `n` or the base ring `R` is used, so
this is stated in full generality. Applied at `n = Fin 3`, `R = ℝ` to realise the *inverse*
singular-value rotations `O₁ᵀ, O₂ᵀ` of a unital qubit channel's Bloch matrix as unitary conjugations
(via the `SU(2) → SO(3)` cover) when diagonalising the channel — the geometric assembly of Nielsen &
Chuang, Problem 8.3's qubit converse. -/
theorem mem_specialOrthogonalGroup_transpose {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] {O : Matrix n n R}
    (hO : O ∈ Matrix.specialOrthogonalGroup n R) :
    Oᵀ ∈ Matrix.specialOrthogonalGroup n R := by
  obtain ⟨hOo, hdet⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hO
  have hOtO : Oᵀ * O = 1 := (Matrix.mem_orthogonalGroup_iff' n R).mp hOo
  have hOOt : O * Oᵀ = 1 := mul_eq_one_comm.mp hOtO
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨by rw [Matrix.mem_orthogonalGroup_iff' n R, Matrix.transpose_transpose]; exact hOOt,
    by rw [Matrix.det_transpose]; exact hdet⟩

/-- **`n × u` is a unit vector for an orthonormal pair.** If `n ⬝ᵥ n = 1`, `u ⬝ᵥ u = 1` and
`n ⬝ᵥ u = 0`, then `(n × u) ⬝ᵥ (n × u) = 1`. Immediate from Lagrange's identity
`Matrix.cross_dot_cross`. -/
theorem crossProduct_dotProduct_self_of_orthonormal {n u : Fin 3 → ℝ}
    (hn : n ⬝ᵥ n = 1) (hu : u ⬝ᵥ u = 1) (hnu : n ⬝ᵥ u = 0) :
    (crossProduct n u) ⬝ᵥ (crossProduct n u) = 1 := by
  rw [cross_dot_cross, hn, hu, hnu]; ring

/-- **Orthonormal-frame expansion.** If `{n, u, n × u}` is a right-handed orthonormal frame
(`n ⬝ᵥ n = 1`, `u ⬝ᵥ u = 1`, `n ⬝ᵥ u = 0`), every vector `x` is the sum of its projections onto the
frame: `x = (n·x) • n + (u·x) • u + ((n×u)·x) • (n×u)`. Proved from the cross-product identities
`(n×u) × x = (n·x) • u − (u·x) • n` and `(n×u) × ((n×u) × x) = (n×u·x) • (n×u) − x`. -/
theorem frame_expansion {n u : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) (hu : u ⬝ᵥ u = 1) (hnu : n ⬝ᵥ u = 0)
    (x : Fin 3 → ℝ) :
    x = (n ⬝ᵥ x) • n + (u ⬝ᵥ x) • u + ((crossProduct n u) ⬝ᵥ x) • (crossProduct n u) := by
  set w := crossProduct n u with hw
  have hww : w ⬝ᵥ w = 1 := by
    rw [hw]; exact crossProduct_dotProduct_self_of_orthonormal hn hu hnu
  have hwu : crossProduct w u = -n := by
    rw [hw, cross_cross_eq_smul_sub_smul, hnu, hu, zero_smul, one_smul, zero_sub]
  have hwn : crossProduct w n = u := by
    rw [hw, cross_cross_eq_smul_sub_smul, hn, one_smul, dotProduct_comm u n, hnu, zero_smul,
      sub_zero]
  have hwx : crossProduct w x = (n ⬝ᵥ x) • u - (u ⬝ᵥ x) • n := by
    rw [hw, cross_cross_eq_smul_sub_smul]
  have hwwx1 : crossProduct w (crossProduct w x) = -((n ⬝ᵥ x) • n) - (u ⬝ᵥ x) • u := by
    rw [hwx, map_sub, map_smul, map_smul, hwu, hwn, smul_neg]
  have hwwx2 : crossProduct w (crossProduct w x) = (w ⬝ᵥ x) • w - x := by
    rw [cross_cross_eq_smul_sub_smul', hww, one_smul]
  have key := hwwx1.symm.trans hwwx2
  rw [eq_sub_iff_add_eq] at key
  linear_combination (norm := module) key

/-- **Every unit vector of `ℝ³` has a unit vector orthogonal to it.** Given `n ⬝ᵥ n = 1`, there is a
`u` with `u ⬝ᵥ u = 1` and `n ⬝ᵥ u = 0`. Take `(−n₁, n₀, 0)` normalised (or `(1, 0, 0)` when `n` is
along `ẑ`). -/
theorem exists_unit_dotProduct_zero {n : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) :
    ∃ u : Fin 3 → ℝ, u ⬝ᵥ u = 1 ∧ n ⬝ᵥ u = 0 := by
  have hn' : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    simpa only [dotProduct, Fin.sum_univ_three, ← pow_two] using hn
  by_cases h : n 0 = 0 ∧ n 1 = 0
  · refine ⟨![1, 0, 0], ?_, ?_⟩
    · simp [dotProduct, Fin.sum_univ_three]
    · simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, mul_one, mul_zero, add_zero]
      exact h.1
  · -- `p = (−n₁, n₀, 0)` is nonzero and orthogonal to `n`.
    set s : ℝ := n 0 ^ 2 + n 1 ^ 2 with hs
    have hs_pos : 0 < s := by
      rcases not_and_or.mp h with h0 | h1
      · have : 0 < n 0 ^ 2 := by positivity
        nlinarith [sq_nonneg (n 1)]
      · have : 0 < n 1 ^ 2 := by positivity
        nlinarith [sq_nonneg (n 0)]
    refine ⟨(Real.sqrt s)⁻¹ • ![-n 1, n 0, 0], ?_, ?_⟩
    · have hpp : (![-n 1, n 0, 0] : Fin 3 → ℝ) ⬝ᵥ ![-n 1, n 0, 0] = s := by
        simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
        rw [hs]; ring
      rw [smul_dotProduct, dotProduct_smul, hpp, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        ← mul_inv, Real.mul_self_sqrt hs_pos.le, inv_mul_cancel₀ hs_pos.ne']
    · have hnp : n ⬝ᵥ (![-n 1, n 0, 0] : Fin 3 → ℝ) = 0 := by
        simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
        ring
      rw [dotProduct_smul, hnp, smul_zero]

/-- **A point on the unit circle is `(cos θ, sin θ)` for some `θ`.** If `c² + s² = 1` there is a
real `θ` with `cos θ = c` and `sin θ = s`; take `θ = arg (c + s i)`. -/
theorem exists_cos_sin_of_sq_add_sq {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = c ∧ Real.sin θ = s := by
  have hne : (⟨c, s⟩ : ℂ) ≠ 0 := by
    intro hz
    rw [Complex.ext_iff] at hz
    simp only [Complex.zero_re, Complex.zero_im] at hz
    nlinarith [hz.1, hz.2]
  have hnorm : c * c + s * s = 1 := by nlinarith [h]
  refine ⟨(⟨c, s⟩ : ℂ).arg, ?_, ?_⟩
  · rw [Complex.cos_arg hne]
    simp only [Complex.norm_def, Complex.normSq_mk]
    rw [hnorm]; simp
  · rw [Complex.sin_arg]
    simp only [Complex.norm_def, Complex.normSq_mk]
    rw [hnorm]; simp

/-- **Axis–angle decomposition of a proper rotation (Euler's theorem, full form).** Every
`O ∈ SO(3)` is a Rodrigues rotation: there is a unit axis `n` (`n₀² + n₁² + n₂² = 1`) and an angle
`θ` with `O v = rot3D n θ v` for every `v : Fin 3 → ℝ`.

`n` is the fixed axis of `O` (Euler,
`exists_unit_mulVec_self_of_mem_specialOrthogonalGroup`); completing `n` to a right-handed
orthonormal frame `{n, u, w = n × u}`, orthogonality gives `O u = cos θ • u + sin θ • w` and (via
`SO(3)`-cross-product preservation) `O w = -sin θ • u + cos θ • w`, so `O` and `rot3D n θ` agree on
the frame, hence everywhere. This is the axis–angle ingredient of the qubit converse of Nielsen &
Chuang, Problem 8.3. -/
theorem exists_rot3D_eq_mulVec_of_mem_specialOrthogonalGroup
    {O : Matrix (Fin 3) (Fin 3) ℝ} (hO : O ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ (n : Fin 3 → ℝ) (θ : ℝ), (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) ∧
      ∀ v, O.mulVec v = rot3D n θ v := by
  obtain ⟨hOorth, hdet⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hO
  -- Euler axis `n`, fixed by `O`.
  obtain ⟨n, hnsq, hOn⟩ := exists_unit_mulVec_self_of_mem_specialOrthogonalGroup hO
  have hnn : n ⬝ᵥ n = 1 := by simpa only [dotProduct, Fin.sum_univ_three, ← pow_two] using hnsq
  -- A unit vector `u ⟂ n`, and the completing `w = n × u`.
  obtain ⟨u, huu, hnu⟩ := exists_unit_dotProduct_zero hnn
  set w := crossProduct n u with hw
  have hnw : n ⬝ᵥ w = 0 := by rw [hw]; exact dot_self_cross n u
  have huw : u ⬝ᵥ w = 0 := by rw [hw]; exact dot_cross_self n u
  have hwu : w ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact huw
  -- `O` preserves dot & cross products.
  have hdotpres := mulVec_dotProduct_mulVec_of_mem_orthogonalGroup hOorth
  have hcrosspres := mulVec_crossProduct_of_mem_specialOrthogonalGroup hO
  -- `O u` lies in the `n`-orthogonal plane.
  have hnOu : n ⬝ᵥ (O.mulVec u) = 0 := by
    conv_lhs => rw [← hOn]
    rw [hdotpres]; exact hnu
  set c : ℝ := u ⬝ᵥ (O.mulVec u) with hc
  set s : ℝ := w ⬝ᵥ (O.mulVec u) with hs
  have hOu : O.mulVec u = c • u + s • w := by
    have := frame_expansion hnn huu hnu (O.mulVec u)
    rw [hnOu, zero_smul, zero_add, ← hw, ← hc, ← hs] at this
    exact this
  -- `c² + s² = 1`.
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have expand : (O.mulVec u) ⬝ᵥ (O.mulVec u)
        = c ^ 2 * (u ⬝ᵥ u) + c * s * (u ⬝ᵥ w) + s * c * (w ⬝ᵥ u) + s ^ 2 * (w ⬝ᵥ w) := by
      conv_lhs => rw [hOu]
      simp only [dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [hdotpres, huu, huw, hwu] at expand
    have hww : w ⬝ᵥ w = 1 := by
      rw [hw]; exact crossProduct_dotProduct_self_of_orthonormal hnn huu hnu
    rw [hww] at expand
    nlinarith [expand, huu]
  -- The angle.
  obtain ⟨θ, hcos, hsin⟩ := exists_cos_sin_of_sq_add_sq hcs
  refine ⟨n, θ, hnsq, fun v => ?_⟩
  -- `n × w = -u`.
  have hnw' : crossProduct n w = -u := by
    rw [hw, cross_cross_eq_smul_sub_smul', hnu, hnn, zero_smul, one_smul, zero_sub]
  -- Agreement on the three frame vectors.
  have hOn_eq : O.mulVec n = rot3D n θ n := by rw [hOn, rot3D_self hnsq]
  have hru : rot3D n θ u = c • u + s • w := by
    rw [rot3D, hnu, mul_zero, zero_smul, add_zero, hcos, hsin, ← hw]
  have hOu_eq : O.mulVec u = rot3D n θ u := by rw [hOu, hru]
  have hOw : O.mulVec w = -(s • u) + c • w := by
    rw [hw, hcrosspres, hOn, ← hw, hOu, map_add, map_smul, map_smul, ← hw, hnw']
    module
  have hrw : rot3D n θ w = -(s • u) + c • w := by
    rw [rot3D, hnw, mul_zero, zero_smul, add_zero, hcos, hsin, hnw']
    module
  have hOw_eq : O.mulVec w = rot3D n θ w := by rw [hOw, hrw]
  -- Extend to all `v` by frame expansion and linearity.
  have hv := frame_expansion hnn huu hnu v
  rw [← hw] at hv
  calc O.mulVec v
      = O.mulVec ((n ⬝ᵥ v) • n + (u ⬝ᵥ v) • u + (w ⬝ᵥ v) • w) := by rw [← hv]
    _ = (n ⬝ᵥ v) • O.mulVec n + (u ⬝ᵥ v) • O.mulVec u + (w ⬝ᵥ v) • O.mulVec w := by
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
    _ = (n ⬝ᵥ v) • rot3D n θ n + (u ⬝ᵥ v) • rot3D n θ u + (w ⬝ᵥ v) • rot3D n θ w := by
        rw [hOn_eq, hOu_eq, hOw_eq]
    _ = rot3D n θ ((n ⬝ᵥ v) • n + (u ⬝ᵥ v) • u + (w ⬝ᵥ v) • w) := by
        rw [rot3D_add, rot3D_add, rot3D_smul, rot3D_smul, rot3D_smul]
    _ = rot3D n θ v := by rw [← hv]

end AxQM.Concrete
