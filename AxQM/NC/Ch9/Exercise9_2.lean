/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ClassicalTraceDistance

/-!
# Nielsen & Chuang, Exercise 9.2 (Trace distance of two-outcome distributions)

Show trace distance between (p,1-p) and (q,1-q) is |p-q|.

The classical trace distance is `D(pₓ, qₓ) ≡ ½ ∑ₓ |pₓ − qₓ|` (N&C `(9.1)`, the
`L¹`/Kolmogorov distance). For the two-outcome distributions `(p, 1 − p)` and
`(q, 1 − q)` the two coordinates' deviations are equal and opposite,
`(1 − p) − (1 − q) = −(p − q)`, so the sum is `|p − q| + |p − q| = 2|p − q|` and
the answer is `|p − q|`.

The formalisation is in `AxQM/Concrete/ClassicalTraceDistance.lean`:

* `AxQM.Concrete.classicalTraceDist` — the trace distance
  `½ ∑ₓ |pₓ − qₓ|` between two distributions `p q : ι → ℝ` (N&C `(9.1)`), the
  reusable classical quantity generalized by the quantum trace distance.
* `AxQM.Concrete.classicalTraceDist_binary` — **Exercise 9.2**:
  `D((p, 1 − p), (q, 1 − q)) = |p − q|` for arbitrary real parameters `p q : ℝ`.
-/
