/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Algebra.Field.GeomSum

/-!
# Geometric sum of a root of unity

For an `n`-th root of unity `ζ` in a division ring (`ζ ^ n = 1`), the geometric sum
`∑_{i < n} ζ ^ i` collapses to `n` when `ζ = 1` and to `0` otherwise — the discrete
orthogonality relation underlying the discrete Fourier transform.
-/

@[expose] public section

open Finset

variable {K : Type*} [DivisionRing K] [DecidableEq K]

/-- **Root-of-unity geometric-sum orthogonality.** If `ζ` is an `n`-th root of unity (`ζ ^ n = 1`),
then `∑_{i < n} ζ ^ i` is `n` when `ζ = 1` and `0` otherwise: for `ζ = 1` the sum is `n` termwise;
for `ζ ≠ 1` it is `(ζ ^ n − 1)/(ζ − 1) = 0` by `geom_sum_eq`. This is the finite-support discrete
orthogonality relation `∑_k ζ^k = n · [ζ = 1]` behind the discrete/quantum Fourier transform. -/
theorem geom_sum_eq_ite_of_pow_eq_one {n : ℕ} {ζ : K} (hζ : ζ ^ n = 1) :
    ∑ i ∈ range n, ζ ^ i = if ζ = 1 then (n : K) else 0 := by
  by_cases h : ζ = 1
  · rw [ite_eq_left h, h]; simp
  · rw [ite_eq_right h, geom_sum_eq h n, hζ, sub_self, zero_div]
