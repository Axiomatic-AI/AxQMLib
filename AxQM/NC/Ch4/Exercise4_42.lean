/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.NumberTheory.CosThreeFifthsIrrational

/-!
# Nielsen & Chuang, Exercise 4.42 (Irrationality of `θ`)

Prove that if cos theta=3/5 then theta is an irrational multiple of 2 pi.

The proposition is a purely number-theoretic statement about the real cosine —
`cos θ = 3/5 → θ/(2π)` irrational — with no physical content.

## The formalisation

The formalisation is in
`ToMathlib/NumberTheory/CosThreeFifthsIrrational.lean`:

* `irrational_div_two_pi_of_cos_eq_three_div_five` — **the exercise**: for `θ : ℝ` with
  `Real.cos θ = 3/5`, `Irrational (θ / (2 * Real.pi))`, i.e. `θ` is an irrational multiple of `2π`.

## Fidelity and proof route

* **"Irrational multiple of `2π`"** is `Irrational (θ / (2π))`: the unique coefficient `c` with
  `θ = c · 2π` is `c = θ / (2π)`, and the claim is exactly that this `c` is irrational
  (equivalently, `θ` is not a rational multiple of `2π`). This is the strongest faithful reading,
  stated for *every* `θ` with `cos θ = 3/5` (both signs of `sin θ`), not a single chosen branch.
* **Proof.** N&C outline an elementary `(3 + 4i)^m ≡ 3 + 4i (mod 5)` Gaussian-integer argument. The
  proof instead invokes **Niven's theorem** (`niven`, `Mathlib/NumberTheory/Niven.lean`): the
  only rational cosines of rational multiples of `π` are `{-1, -1/2, 0, 1/2, 1}`. As `3/5` is
  rational and not among them, `θ` is not a rational multiple of `π` — a fortiori not of `2π`. Niven
  is a strictly more general fact than the exercise's specific congruence, so this is a faithful
  (indeed stronger) route to the stated conclusion, never a weakening of it. The theorem proved is
  precisely the one the exercise asserts.
-/
