/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Algebra.Star.CHSH

/-!
# The noncommutative CHSH squaring identity

Extends `Mathlib.Algebra.Star.CHSH` with `CHSH_sq`, the noncommutative counterpart of `CHSH_id`
underlying Tsirelson's bound.
-/

public section

variable {R : Type*}

/-- **The CHSH squaring identity.** If `A₀ A₁ B₀ B₁` are involutions (`Aᵢ ^ 2 = Bⱼ ^ 2 = 1`)
with each `Aᵢ` commuting with each `Bⱼ`, then the square of the CHSH operator
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁` is `4 - ⁅A₀, A₁⁆ * ⁅B₀, B₁⁆`, where
`⁅x, y⁆ = x * y - y * x` is the ring commutator.

This is the noncommutative counterpart of `CHSH_id`, and like it is stated over a bare `Ring`
taking the involution and commuting relations as hypotheses (self-adjointness plays no role in
the identity). In a *commutative* ring both commutators vanish, so the CHSH operator squares to
the scalar `4`; in general the extra term `⁅A₀, A₁⁆ * ⁅B₀, B₁⁆` measures the failure of
commutativity, and this identity underlies Tsirelson's bound — bounding that term shows the
square is at most `8`, whence the CHSH operator is at most `2√2` (see `tsirelson_inequality`).

This is equation (2.233) of Nielsen and Chuang, *Quantum Computation and Quantum Information*,
under the dictionary `A₀ = R`, `A₁ = Q`, `B₀ = S`, `B₁ = T` (their commutator term
`⁅Q, R⁆ ⊗ ⁅S, T⁆` equals `-⁅A₀, A₁⁆ * ⁅B₀, B₁⁆` in the ambient ring). -/
theorem CHSH_sq [Ring R] {A₀ A₁ B₀ B₁ : R}
    (A₀_inv : A₀ ^ 2 = 1) (A₁_inv : A₁ ^ 2 = 1) (B₀_inv : B₀ ^ 2 = 1) (B₁_inv : B₁ ^ 2 = 1)
    (A₀B₀_commutes : A₀ * B₀ = B₀ * A₀) (A₀B₁_commutes : A₀ * B₁ = B₁ * A₀)
    (A₁B₀_commutes : A₁ * B₀ = B₀ * A₁) (A₁B₁_commutes : A₁ * B₁ = B₁ * A₁) :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) ^ 2 = 4 - ⁅A₀, A₁⁆ * ⁅B₀, B₁⁆ := by
  have hA₀ : A₀ * A₀ = 1 := by rwa [sq] at A₀_inv
  have hA₁ : A₁ * A₁ = 1 := by rwa [sq] at A₁_inv
  have hB₀ : B₀ * B₀ = 1 := by rwa [sq] at B₀_inv
  have hB₁ : B₁ * B₁ = 1 := by rwa [sq] at B₁_inv
  -- Each `Aᵢ` commutes with `Bⱼ`, hence with `B₀ ± B₁`.
  have cP0 : Commute (B₀ + B₁) A₀ := (Commute.add_right A₀B₀_commutes A₀B₁_commutes).symm
  have cP1 : Commute (B₀ + B₁) A₁ := (Commute.add_right A₁B₀_commutes A₁B₁_commutes).symm
  have cQ0 : Commute (B₀ - B₁) A₀ := (Commute.sub_right A₀B₀_commutes A₀B₁_commutes).symm
  have cQ1 : Commute (B₀ - B₁) A₁ := (Commute.sub_right A₁B₀_commutes A₁B₁_commutes).symm
  -- Regroup the CHSH operator as `A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)` and square it, moving the
  -- `Aᵢ` past the `B₀ ± B₁` factors so the `Aᵢ` collapse via `Aᵢ ^ 2 = 1`.
  have hregroup : A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁
      = A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁) := by rw [mul_add, mul_sub]; abel
  rw [hregroup, sq]
  set P := B₀ + B₁ with hP
  set Q := B₀ - B₁ with hQ
  clear_value P Q
  rw [add_mul, mul_add, mul_add,
    cP0.mul_mul_mul_comm A₀ P, cP1.mul_mul_mul_comm A₀ Q,
    cQ0.mul_mul_mul_comm A₁ P, cQ1.mul_mul_mul_comm A₁ Q,
    hA₀, hA₁, one_mul, one_mul, hP, hQ]
  -- What remains is an identity of `B`-monomials once `Bⱼ ^ 2 = 1` is applied.
  simp only [Ring.lie_def, mul_add, add_mul, mul_sub, sub_mul, hB₀, hB₁, mul_one]
  rw [show (4 : R) = 4 • (1 : R) by norm_num]
  abel

/-- The CHSH squaring identity (2.233) packaged for a bundled `IsCHSHTuple`: a convenience
wrapper around `CHSH_sq`. The `StarMul` instance here is required only to *state* `IsCHSHTuple`;
the identity itself (`CHSH_sq`) needs neither it nor the self-adjointness fields. -/
theorem IsCHSHTuple.sq_chsh [Ring R] [StarMul R] {A₀ A₁ B₀ B₁ : R}
    (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) ^ 2 = 4 - ⁅A₀, A₁⁆ * ⁅B₀, B₁⁆ :=
  CHSH_sq T.A₀_inv T.A₁_inv T.B₀_inv T.B₁_inv
    T.A₀B₀_commutes T.A₀B₁_commutes T.A₁B₀_commutes T.A₁B₁_commutes
