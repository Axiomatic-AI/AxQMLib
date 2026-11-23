/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ClassicalCountingQueryLowerBound

/-!
# Nielsen & Chuang, Exercise 6.14

Prove any classical counting algorithm at accuracy c*sqrt(M) with prob >=3/4 needs Omega(N) oracle
calls.

This is a classical query-complexity lower bound; no quantum object appears. It sits in §6.3
(counting), immediately after Exercise 6.13. Where 6.13 studies the *specific* uniform-independent
sampling estimator, 6.14 asks the same `Ω(N)` conclusion against **any classical counting
algorithm** making oracle calls — the general adaptive query model, not the restricted sampling
model. The statement speaks only of a probability distribution over decision trees over a Boolean
oracle.

## Formalisation

The model and the lower bound are in `AxQM/Concrete/`, namespace `AxQM.Concrete`,
built in three pieces:

* `AxQM/Concrete/ClassicalQueryModel.lean` — the adaptive decision-tree query model:
  `QueryTree N` (`leaf`/`node`), its output `eval`, query set `queried`, and `depth`; the locality
  lemmas `eval_eq_of_agree` / `queried_eq_of_agree` (behaviour depends only on the oracle's values
  at queried points) and `card_queried_le_depth`.
* `AxQM/Concrete/ClassicalCountingIntervals.lean` — the hard family: `numSolutions`, the
  length-`m` interval oracles `intervalOracle m s` (`numSolutions_intervalOracle`), and the union
  bound `card_hitStarts_le` / `card_missStarts_ge` (a query set of size `|Q|` meets at most `m·|Q|`
  of the intervals, so at least `(N−m+1)−m·|Q|` avoid it).
* `AxQM/Concrete/ClassicalCountingQueryLowerBound.lean` — the assembly:

  * `AxQM.Concrete.RandomizedCountingAlgorithm` — the faithful model of *any* classical
    counting algorithm: a probability space `(Ω, μ)` with a measurable family of trees of
    `depth ≤ budget`.
  * `AxQM.Concrete.counting_query_lower_bound` — with `m := ⌈c²⌉₊ + 1`, success probability
    `≥ 3/4` on every oracle forces `2 (N − m + 1) ≤ 3 m · budget`, a linear lower bound on the query
    budget.
  * `AxQM.Concrete.counting_query_needs_linear_oracle_calls` — the `Ω(N)` repackaging: for
    each `c ≥ 0` there is `a > 0` with `a · N ≤ budget` for all `N` large enough for the hard
    instances to exist. This is the exercise's claim.

## Proof strategy

The hard instances are the all-`false` oracle (`M = 0`, whose accuracy `c √0 = 0` forces the
estimate to be exactly `0`) versus the `N − m + 1` length-`m` interval oracles (`M = m`, where
`c √m < m` forces a nonzero estimate). By **locality** an algorithm correct on all-`false` returns
the same `0` on every interval that avoids its (small) query set, so it is wrong there; the
**union bound** counts at least `(N − m + 1) − m · budget` such intervals; **averaging** the
resulting pointwise count over
`μ`, with the two per-oracle success bounds, yields `2 (N − m + 1) ≤ 3 m · budget = Ω(N)`.
-/
