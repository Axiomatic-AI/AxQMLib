/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ClassicalFidelity

/-!
# Nielsen & Chuang, Exercise 9.3 (Compute the classical fidelity)

Compute fidelity of given probability distributions (1,0) vs (1/2,1/2) etc.

The classical fidelity is `F(pₓ, qₓ) ≡ ∑ₓ √(pₓ qₓ)` (N&C `(9.2)`, the
Bhattacharyya coefficient / inner product of the vectors `(√pₓ)` and `(√qₓ)`).
The two answers are `√2 / 2 = 1/√2 ≈ 0.7071` and
`(4√6 + √3) / 12 ≈ 0.9608`.

The formalisation is in `AxQM/Concrete/ClassicalFidelity.lean`:

* `AxQM.Concrete.classicalFidelity` — the fidelity `∑ₓ √(pₓ qₓ)` between
  two distributions `p q : ι → ℝ` (N&C `(9.2)`), the reusable classical quantity
  that N&C's quantum fidelity generalizes (see `matrixFidelity_diagonal`).
* `AxQM.Concrete.classicalFidelity_deterministic_uniform` — **part 1**:
  `F((1, 0), (1/2, 1/2)) = √2 / 2`.
* `AxQM.Concrete.classicalFidelity_ternary_example` — **part 2**:
  `F((1/2, 1/3, 1/6), (3/4, 1/8, 1/8)) = (4√6 + √3) / 12`.
* `AxQM.Concrete.classicalFidelity_comm`,
  `AxQM.Concrete.classicalFidelity_nonneg`,
  `AxQM.Concrete.classicalFidelity_self`,
  `AxQM.Concrete.classicalFidelity_self_eq_one` — the basic properties
  (`F(p, q) = F(q, p)`, `0 ≤ F(p, q)`, and `F(p, p) = ∑ₓ pₓ = 1` for a normalized
  distribution — the fidelity is maximized, not zeroed, by coincident
  distributions, so unlike the trace distance it is not a metric).
-/
