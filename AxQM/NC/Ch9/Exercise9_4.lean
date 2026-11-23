/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ClassicalTraceDistance

/-!
# Nielsen & Chuang, Exercise 9.4 (Trace distance as a maximum over events)

Prove D(p,q)=max_S |p(S)-q(S)| over subsets S.

The classical trace distance is `D(pₓ, qₓ) ≡ ½ ∑ₓ |pₓ − qₓ|` (N&C `(9.1)`). N&C
`(9.3)` reinterprets it operationally: `S` is an *event*, `p(S) = ∑_{x∈S} pₓ` is
the probability it occurs under `{pₓ}`, and the trace distance is the largest gap
`|p(S) − q(S)|` any event can exhibit — the optimal event for distinguishing the
two distributions.

The proof rests on the identity `D(p, q) = ∑ₓ (pₓ − qₓ)⁺` (valid whenever `p`
and `q` have equal total mass, in particular for probability distributions): the
positive parts collect exactly the indices where `p` exceeds `q`, so the event
`S⁺ = {x | pₓ ≥ qₓ}` attains the maximum, while any other event's gap is squeezed
between `±∑ₓ (pₓ − qₓ)⁺`. The absolute value costs nothing extra: `p(S⁺) − q(S⁺)`
is already nonnegative and equal to `D(p, q)` (which is the content of the
companion Exercise 9.5).

The formalisation is in `AxQM/Concrete/ClassicalTraceDistance.lean`:

* `AxQM.Concrete.classicalTraceDist_eq_sum_posPart` — the algebraic core:
  `D(p, q) = ∑ₓ (pₓ − qₓ)⁺` for equal-total-mass `p, q`.
* `AxQM.Concrete.sum_sub_sum_le_classicalTraceDist` and
  `AxQM.Concrete.abs_sum_sub_sum_le_classicalTraceDist` — every event's
  gap `p(S) − q(S)` (resp. `|p(S) − q(S)|`) is at most `D(p, q)`.
* `AxQM.Concrete.exists_finset_sum_sub_eq_classicalTraceDist` — the event
  `{x | pₓ ≥ qₓ}` attains `p(S) − q(S) = D(p, q)`.
* `AxQM.Concrete.classicalTraceDist_isGreatest` — **Exercise 9.4**, N&C
  `(9.3)`: `D(p, q)` is the greatest value of `|p(S) − q(S)|` over all events `S`,
  for `p, q` of equal total mass. Its corollary
  `AxQM.Concrete.classicalTraceDist_isGreatest_of_sum_eq_one` states it
  for genuine probability distributions (`∑ₓ pₓ = ∑ₓ qₓ = 1`).
-/
