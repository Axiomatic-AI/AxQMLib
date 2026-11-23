/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochRotation
import AxQM.Concrete.RotationConjugation

/-!
# Concrete: the generalized Euler decomposition is *false* for non-parallel axes (N&C Exercise 4.11)

Nielsen & Chuang, Exercise 4.11 claims: for **non-parallel** real unit vectors `m̂, n̂`, an
arbitrary single-qubit unitary `U` may be written

`U = e^{iα} R_n̂(β) R_m̂(γ) R_n̂(δ)`  (eq. 4.13)

for appropriate real `α, β, γ, δ`. **This is false as stated.** The correct hypothesis is that the
middle axis be *perpendicular* to the (repeated) outer axis, `m̂ ⊥ n̂` — this is exactly Davenport's
theorem on three-rotation decompositions (the classical Euler `ZYZ`/`ZXZ` decompositions all use
perpendicular axes). Mere non-parallelism does **not** suffice.

## Why it fails — the conjugation invariant

Conjugation by `R_â(θ)` acts on the Pauli combination `v·σ` as the spatial rotation of `v` about
`â` by `θ` (`Concrete.pauliDot_conj_rotAxis`, the heart of Exercise 4.6). For a product
`U = e^{iα} R_n̂(β) R_m̂(γ) R_n̂(δ)` the global phase cancels in `U (n̂·σ) U†`, and the two outer
`R_n̂` factors fix the axis `n̂` (`rot3D_self`), so

`U (n̂·σ) U† = (R(n̂))·σ`,   where   `n̂ · R(n̂) = (m̂·n̂)² + (1 − (m̂·n̂)²) cos γ ≥ 2(m̂·n̂)² − 1`.

Thus the coefficient `n̂·R(n̂)` is bounded **below by `2(m̂·n̂)² − 1`**. When `m̂` is not
perpendicular to `n̂` (`m̂·n̂ ≠ 0`) this bound is strictly greater than `−1`, so any unitary `U`
whose induced rotation sends `n̂ ↦ −n̂` (i.e. `n̂·R(n̂) = −1`) is **not** of the form (4.13). The
Pauli `X` is such a unitary: `X (ẑ·σ) X = −(ẑ·σ)` (`pauliX_mul_pauliZ_mul_pauliX`).

## What is formalized

This file holds the exercise-specific content. The three general facts it builds on live in their
canonical `Concrete/` modules and are reused, not restated: `rot3D_self` (a rotation fixes its own
axis) and `rot3D_axisZ_apply_two` (rotation about `ẑ` preserves the `z`-component) in
`Concrete/BlochRotation.lean` (alongside `rot3D`), and `pauliDot_axisZ` (`ẑ·σ = Z`) in
`Concrete/Pauli.lean` (alongside `pauliDot_eq`).

* `pauliDot_conj_rotAxis_triple` — the **conjugation invariant**: for unit `n̂, m̂`,
  `(e^{iα} • R_n̂(β) R_m̂(γ) R_n̂(δ)) · (n̂·σ) · (…)ᴴ = (rot3D n̂ β (rot3D m̂ γ n̂))·σ`. The phase
  cancels and the inner `R_n̂(δ)` drops (it fixes `n̂`), leaving the axis rotated by `R_m̂(γ)` then
  `R_n̂(β)`.
* `rot3D_counterexampleAxis_axisZ_apply_two` — the `z`-component of `ẑ` rotated about the specific
  counterexample axis `m̂ = (3/5, 0, 4/5)`, equal to `cos γ + (1 − cos γ)·(16/25) ∈ [7/25, 1]`.
* `pauliX_ne_smul_rotAxis_mul_rotAxis_mul_rotAxis` — the **counterexample**: with the non-parallel,
  non-perpendicular unit pair `n̂ = ẑ`, `m̂ = (3/5, 0, 4/5)` (so `m̂·n̂ = 4/5 ≠ 0`), the unitary
  `X` is not `e^{iα} R_ẑ(β) R_m̂(γ) R_ẑ(δ)` for any `α, β, γ, δ`. Reading off the `(0,0)` entry of
  the conjugation invariant forces `16/25 + (9/25) cos γ = −1`, i.e. `cos γ = −41/9 < −1`, absurd.
* `not_forall_unit_nonParallel_exists_smul_rotAxis_triple` — the **negation of Exercise 4.11**
  itself: there is no proof that every unitary decomposes as (4.13) over every non-parallel unit
  pair. Instantiating the (claimed) universal statement at `X, ẑ, m̂` contradicts the
  counterexample.

Everything is stated for matrices and scalars (`rotAxis`, `pauliDot`, `pauliX`, `pauliZ`,
`rot3D`). The statement of Exercise 4.11 is in `AxQM/NC/Ch4/Exercise4_11.lean`.

## Design notes

* **Faithful refutation, not a silent repair.** N&C states (4.13) for all non-parallel `m̂, n̂`;
  rather than quietly strengthening the hypothesis to `m̂ ⊥ n̂` and proving the (true) corrected
  statement, we prove the negation of the theorem *as written*, exhibiting an explicit non-parallel
  pair and unitary for which the decomposition provably does not exist. The corrected perpendicular
  version (obtained by conjugating Theorem 4.1) is proved separately in
  `Concrete/EulerDecompositionOrthogonal.lean` (`exists_smul_rotAxis_triple_of_perp`).
* **The `(0,0)`-entry reads off the invariant.** With the outer axis fixed to `n̂ = ẑ`, both outer
  `R_ẑ` conjugations preserve the `z`-component of the rotated vector (`rot3D_axisZ_apply_two`),
  and `(pauliDot w)₀₀ = ↑(w₂)` (from `pauliDot_eq`), so the single scalar `n̂·R(n̂)` is extracted
  without any trace machinery.
* **Choice of the counterexample pair.** `m̂ = (3/5, 0, 4/5)` is a rational unit vector with
  `m̂·ẑ = 4/5`, giving the clean lower bound `2(4/5)² − 1 = 7/25 > −1`; any non-perpendicular
  rational unit vector would do.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The outer axis `n̂ = ẑ = (0, 0, 1)` of the counterexample is a unit vector. -/
theorem axisZ_normSq_eq_one :
    (![0, 0, 1] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, 1] : Fin 3 → ℝ) 1 ^ 2
      + (![0, 0, 1] : Fin 3 → ℝ) 2 ^ 2 = 1 := by
  norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- The middle axis `m̂ = (3/5, 0, 4/5)` of the counterexample is a unit vector. It is non-parallel
to `ẑ` (nonzero first component) and non-perpendicular (`m̂·ẑ = 4/5 ≠ 0`). -/
theorem counterexampleAxis_normSq_eq_one :
    (![3 / 5, 0, 4 / 5] : Fin 3 → ℝ) 0 ^ 2 + (![3 / 5, 0, 4 / 5] : Fin 3 → ℝ) 1 ^ 2
      + (![3 / 5, 0, 4 / 5] : Fin 3 → ℝ) 2 ^ 2 = 1 := by
  norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- **The conjugation invariant of a three-rotation `R_n̂ R_m̂ R_n̂` product.** For unit axes
`n̂, m̂` and any phase `α` and angles `β, γ, δ`, conjugating the axis observable `n̂·σ` by
`U = e^{iα} R_n̂(β) R_m̂(γ) R_n̂(δ)` rotates the axis vector `n̂` along the composite Rodrigues
rotation `rot3D n̂ β ∘ rot3D m̂ γ`:

`U · (n̂·σ) · Uᴴ = (rot3D n̂ β (rot3D m̂ γ n̂))·σ`.

The global phase cancels (`e^{iα}` against `star e^{iα} = e^{-iα}`), the innermost `R_n̂(δ)` fixes
`n̂` (`rot3D_self`), and the two remaining conjugations apply `pauliDot_conj_rotAxis`
(Exercise 4.6). This is the obstruction behind the falsity of Exercise 4.11: the `n̂`-coefficient
of the right-hand vector is `(m̂·n̂)² + (1 − (m̂·n̂)²) cos γ`, bounded below by `2(m̂·n̂)² − 1`. -/
theorem pauliDot_conj_rotAxis_triple {n m : Fin 3 → ℝ}
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (hm : m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 = 1)
    (α β γ δ : ℝ) :
    (Complex.exp ((α : ℂ) * I) • (rotAxis n β * rotAxis m γ * rotAxis n δ))
        * pauliDot n
        * (Complex.exp ((α : ℂ) * I) • (rotAxis n β * rotAxis m γ * rotAxis n δ))ᴴ
      = pauliDot (rot3D n β (rot3D m γ n)) := by
  -- The global phase `e^{iα}` cancels against its conjugate `e^{-iα}`.
  have hc : star (Complex.exp ((α : ℂ) * I)) * Complex.exp ((α : ℂ) * I) = 1 := by
    simp [← Complex.exp_conj, ← Complex.exp_add, Complex.conj_ofReal]
  -- Peel the three conjugations from the inside out.
  have h1 : rotAxis n δ * pauliDot n * (rotAxis n δ)ᴴ = pauliDot n := by
    rw [pauliDot_conj_rotAxis hn δ n, rot3D_self hn]
  have h2 : rotAxis m γ * pauliDot n * (rotAxis m γ)ᴴ = pauliDot (rot3D m γ n) :=
    pauliDot_conj_rotAxis hm γ n
  have h3 : rotAxis n β * pauliDot (rot3D m γ n) * (rotAxis n β)ᴴ
      = pauliDot (rot3D n β (rot3D m γ n)) := pauliDot_conj_rotAxis hn β _
  simp only [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hc, one_smul]
  calc rotAxis n β * rotAxis m γ * rotAxis n δ * pauliDot n
          * (rotAxis n β * rotAxis m γ * rotAxis n δ)ᴴ
      = rotAxis n β * (rotAxis m γ * (rotAxis n δ * pauliDot n * (rotAxis n δ)ᴴ)
          * (rotAxis m γ)ᴴ) * (rotAxis n β)ᴴ := by
        rw [conjTranspose_mul, conjTranspose_mul]; noncomm_ring
    _ = rotAxis n β * (rotAxis m γ * pauliDot n * (rotAxis m γ)ᴴ) * (rotAxis n β)ᴴ := by rw [h1]
    _ = rotAxis n β * pauliDot (rot3D m γ n) * (rotAxis n β)ᴴ := by rw [h2]
    _ = pauliDot (rot3D n β (rot3D m γ n)) := h3

/-- The `z`-component of `ẑ` rotated about the counterexample axis `m̂ = (3/5, 0, 4/5)`:
`(rot3D m̂ γ ẑ)₂ = cos γ + (1 − cos γ)·(16/25)`. Here `m̂·ẑ = 4/5`, so `(m̂·ẑ)² = 16/25` and the
value is `16/25 + (9/25) cos γ ∈ [7/25, 1]` — bounded strictly above `−1`. -/
theorem rot3D_counterexampleAxis_axisZ_apply_two (γ : ℝ) :
    (rot3D ![3 / 5, 0, 4 / 5] γ ![0, 0, 1]) 2 = Real.cos γ + (1 - Real.cos γ) * (16 / 25) := by
  simp only [rot3D, Pi.add_apply, Pi.smul_apply, smul_eq_mul, cross_apply, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **Counterexample to Nielsen & Chuang, Exercise 4.11.** For the non-parallel, non-perpendicular
unit axes `n̂ = ẑ = (0,0,1)` and `m̂ = (3/5, 0, 4/5)` (which have `m̂·n̂ = 4/5 ≠ 0`), the Pauli `X`
gate is **not** expressible as `e^{iα} R_n̂(β) R_m̂(γ) R_n̂(δ)` for any real `α, β, γ, δ`.

Conjugating `ẑ·σ = Z` by such a product would, by `pauliDot_conj_rotAxis_triple`, give
`(rot3D ẑ β (rot3D m̂ γ ẑ))·σ`; but `X Z X = −Z`, so its `z`-coefficient must be `−1`. Reading off
the `(0,0)` entry forces `cos γ + (1 − cos γ)(16/25) = −1`, i.e. `cos γ = −41/9 < −1`, contradicting
`−1 ≤ cos γ`. -/
theorem pauliX_ne_smul_rotAxis_mul_rotAxis_mul_rotAxis (α β γ δ : ℝ) :
    pauliX ≠ Complex.exp ((α : ℂ) * I) •
      (rotAxis ![0, 0, 1] β * rotAxis ![3 / 5, 0, 4 / 5] γ * rotAxis ![0, 0, 1] δ) := by
  intro h
  have hxh : pauliXᴴ = pauliX := pauliX_isHermitian
  -- Conjugate `Z = ẑ·σ` by the claimed product; the invariant gives the rotated axis vector.
  have key := pauliDot_conj_rotAxis_triple axisZ_normSq_eq_one counterexampleAxis_normSq_eq_one
    α β γ δ
  rw [← h, pauliDot_axisZ, hxh, pauliX_mul_pauliZ_mul_pauliX] at key
  -- `key : -Z = (rot3D ẑ β (rot3D m̂ γ ẑ))·σ`; the `(0,0)` entry reads off the `z`-coefficient.
  have hentry := congrFun (congrFun key 0) 0
  rw [pauliDot_eq] at hentry
  simp only [pauliZ, Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hentry
  have hw2 : (rot3D ![0, 0, 1] β (rot3D ![3 / 5, 0, 4 / 5] γ ![0, 0, 1])) 2 = -1 := by
    exact_mod_cast hentry.symm
  rw [rot3D_axisZ_apply_two, rot3D_counterexampleAxis_axisZ_apply_two] at hw2
  -- `16/25 + (9/25) cos γ = -1` contradicts `-1 ≤ cos γ`.
  nlinarith [Real.neg_one_le_cos γ, hw2]

/-- **Nielsen & Chuang, Exercise 4.11 is false as stated.** There is no proof that *every*
single-qubit unitary decomposes as `e^{iα} R_n̂(β) R_m̂(γ) R_n̂(δ)` for *every* pair of non-parallel
unit vectors `m̂, n̂`. (Here non-parallelism of the unit vectors is expressed as "`m̂` is not a
scalar multiple of `n̂`"; the correct sufficient hypothesis is `m̂ ⊥ n̂`.) The witnessing failure is
the non-parallel pair `n̂ = ẑ`, `m̂ = (3/5, 0, 4/5)` together with the unitary `X`
(`pauliX_ne_smul_rotAxis_mul_rotAxis_mul_rotAxis`). -/
theorem not_forall_unit_nonParallel_exists_smul_rotAxis_triple :
    ¬ ∀ (m n : Fin 3 → ℝ), m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 = 1 →
        n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 → (∀ c : ℝ, m ≠ c • n) →
      ∀ U : Matrix (Fin 2) (Fin 2) ℂ, U ∈ Matrix.unitaryGroup (Fin 2) ℂ →
        ∃ α β γ δ : ℝ,
          U = Complex.exp ((α : ℂ) * I) • (rotAxis n β * rotAxis m γ * rotAxis n δ) := by
  intro H
  -- `m̂ = (3/5,0,4/5)` is not a scalar multiple of `ẑ`: its first component is `3/5 ≠ 0 = c·0`.
  have hnonpar : ∀ c : ℝ, (![3 / 5, 0, 4 / 5] : Fin 3 → ℝ) ≠ c • ![0, 0, 1] := by
    intro c hc
    have h0 := congrFun hc 0
    simp only [Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, mul_zero] at h0
    norm_num at h0
  obtain ⟨α, β, γ, δ, hU⟩ := H ![3 / 5, 0, 4 / 5] ![0, 0, 1] counterexampleAxis_normSq_eq_one
    axisZ_normSq_eq_one hnonpar pauliX pauliX_mem_unitaryGroup
  exact pauliX_ne_smul_rotAxis_mul_rotAxis_mul_rotAxis α β γ δ hU

end AxQM.Concrete
