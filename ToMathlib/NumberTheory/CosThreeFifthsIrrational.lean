/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.NumberTheory.Niven

/-! # An angle with cosine `3/5` is an irrational multiple of `2π`

If `cos θ = 3/5` then `θ / (2π)` is irrational — equivalently, `θ` is not a rational multiple
of `2π`. This is the mathematical content of Nielsen & Chuang's *Quantum Computation and Quantum
Information*, Exercise 4.42 ("Irrationality of `θ`"), which underlies the Solovay–Kitaev-style
observation that repeated application of a `cos θ = 3/5` rotation densely fills the circle.

N&C suggest an elementary proof via `(3 + 4i)^m ≡ 3 + 4i (mod 5)` in the Gaussian integers. Here we
instead read it off **Niven's theorem** (`niven`): the only rational values taken by `cos` at
rational multiples of `π` are `{-1, -1/2, 0, 1/2, 1}`. Since `3/5` is rational and not among those
five values, `θ` cannot be a rational multiple of `π`, hence not of `2π`. Niven's theorem is a
faithful strengthening of the exercise's specific `(3+4i)`-argument, so this is a valid — indeed
more general — route to the same conclusion.
-/

@[expose] public section

open Real

/-- **Nielsen & Chuang, Exercise 4.42 (Irrationality of `θ`).** If `cos θ = 3/5` then `θ` is an
irrational multiple of `2π`: the coefficient `θ / (2π)` is an irrational number.

Proved as a corollary of Niven's theorem (`niven`): were `θ / (2π)` rational, `θ` would be a
rational multiple of `π` with `cos θ = 3/5` rational, forcing `3/5 ∈ {-1, -1/2, 0, 1/2, 1}` — which
is false. -/
theorem irrational_div_two_pi_of_cos_eq_three_div_five {θ : ℝ}
    (hθ : Real.cos θ = 3 / 5) : Irrational (θ / (2 * π)) := by
  rintro ⟨q, hq⟩
  -- `hq : (q : ℝ) = θ / (2π)`, so `θ = (2q) · π` is a rational multiple of `π`.
  have h2π : (2 : ℝ) * π ≠ 0 := by positivity
  have hθπ : θ = ((2 * q : ℚ) : ℝ) * π := by
    have hθq : θ = (q : ℝ) * (2 * π) := (div_eq_iff h2π).mp hq.symm
    rw [hθq]; push_cast; ring
  -- Niven's theorem then pins `cos θ = 3/5` to one of the five allowed rational cosines.
  have hmem := niven ⟨2 * q, hθπ⟩ ⟨3 / 5, by rw [hθ]; norm_num⟩
  rw [hθ] at hmem
  norm_num [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
