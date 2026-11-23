/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ClassicalTraceDistance

/-!
# Nielsen & Chuang, Exercise 9.5 (Removing the absolute value from the trace distance)

Show absolute value may be removed: D(p,q)=max_S (p(S)-q(S)).

Exercise 9.4 (N&C `(9.3)`) established `D(p, q) = max_S |p(S) − q(S)|`, the maximum
over events `S` of the *absolute* probability gap. This exercise strengthens the
interpretation: the maximum is unchanged when the absolute value is dropped, so the
optimal distinguishing event already assigns strictly more probability under `p`
than under `q`.

The reason is exactly the attainment fact from Exercise 9.4: the maximum of
`|p(S) − q(S)|` is achieved at the event `S⁺ = {x | pₓ ≥ qₓ}`, whose *signed* gap
`p(S⁺) − q(S⁺)` is already the nonnegative value `D(p, q)`. Since every signed gap
`p(S) − q(S)` is bounded above by `|p(S) − q(S)| ≤ D(p, q)`, removing the absolute
value cannot raise the supremum, and the same event still attains it — the two
maxima coincide.

The formalisation is in `AxQM/Concrete/ClassicalTraceDistance.lean`:

* `AxQM.Concrete.classicalTraceDist_isGreatest_sub` — **Exercise 9.5**, N&C
  `(9.4)`: for `p, q` of equal total mass, `D(p, q)` is the greatest value of the
  *signed* gap `p(S) − q(S)` over all events `S` (absolute value removed). It reuses
  `sum_sub_sum_le_classicalTraceDist` (the signed gap is an upper bound) and
  `exists_finset_sum_sub_eq_classicalTraceDist` (the event `{x | pₓ ≥ qₓ}` attains
  it) — both from Exercise 9.4.
* `AxQM.Concrete.classicalTraceDist_isGreatest_sub_of_sum_eq_one` — its
  corollary for genuine probability distributions (`∑ₓ pₓ = ∑ₓ qₓ = 1`).
-/
