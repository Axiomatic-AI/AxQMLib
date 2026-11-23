/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ClassicalTraceDistance

/-!
# Nielsen & Chuang, Exercise 9.1 (Compute the classical trace distance)

Compute trace distance between given probability distributions (1,0) vs (1/2,1/2) etc.

The classical trace distance is `D(pₓ, qₓ) ≡ ½ ∑ₓ |pₓ − qₓ|` (N&C `(9.1)`, the
`L¹`/Kolmogorov distance). The two answers are `1/2` and `1/4`.

The formalisation is in `AxQM/Concrete/ClassicalTraceDistance.lean`:

* `AxQM.Concrete.classicalTraceDist` — the trace distance
  `½ ∑ₓ |pₓ − qₓ|` between two distributions `p q : ι → ℝ` (N&C `(9.1)`), the
  reusable classical quantity generalized by the quantum trace distance.
* `AxQM.Concrete.classicalTraceDist_deterministic_uniform` — **part 1**:
  `D((1, 0), (1/2, 1/2)) = 1/2`.
* `AxQM.Concrete.classicalTraceDist_ternary_example` — **part 2**:
  `D((1/2, 1/3, 1/6), (3/4, 1/8, 1/8)) = 1/4`.
* `AxQM.Concrete.classicalTraceDist_self`,
  `AxQM.Concrete.classicalTraceDist_comm`,
  `AxQM.Concrete.classicalTraceDist_nonneg` — the basic "distance"
  properties (`D(x, x) = 0`, symmetry, nonnegativity) that justify N&C's use of
  the term *distance*.
-/
