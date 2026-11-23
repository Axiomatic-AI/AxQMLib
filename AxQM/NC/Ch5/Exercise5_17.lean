/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.NumberTheory.PerfectPower

/-!
# Nielsen & Chuang, Exercise 5.17 (Testing whether `N = aᵇ`)

Give an O(L^3) classical algorithm to determine whether N = a^b for integers a>=1, b>=2.
*(N&C p. 234, §5.3.2.)*

This "perfect-power" test is **Step 2 of the classical reduction of factoring to order-finding**
(N&C p. 233): before invoking the (quantum) order-finding subroutine, the factoring algorithm first
strips off the easy cases — evenness (Step 1), and `N = aᵇ` a perfect power (Step 2, *"uses the
classical algorithm of Exercise 5.17"*). The exponent range `a ≥ 1, b ≥ 2` is exactly the set of
representations Step 2 must rule out. The very same predicate is what the worked Chapter 5 items
`Exercise5_18` (factoring `91`) and `Exercise5_19` (`15` is the smallest number needing
order-finding) consume, via `Nat.IsPerfectPower`.

The formalisation is in `ToMathlib/NumberTheory/PerfectPower.lean` (namespace `Nat`). Compare
the other Chapter 5 number-theoretic exercises 5.1, 5.3 and 5.15.

## What is formalised, and where

The exercise's four parts map onto declarations in `ToMathlib.NumberTheory.PerfectPower` as follows.

* `Nat.IsPerfectPower n` — the predicate `∃ a b, 1 ≤ a ∧ 2 ≤ b ∧ a ^ b = n`, a verbatim
  transcription of "`N = a ^ b` for integers `a ≥ 1` and `b ≥ 2`". (Edge cases match the literal
  reading: `IsPerfectPower 0` is `False` because `a ≥ 1` forbids the base `0`, while
  `IsPerfectPower 1` is `True` via `1 = 1 ^ 2`.)
* **Part (1)** — `Nat.exponent_lt_size`: if `a ^ b = n` with a nontrivial base `2 ≤ a`, then
  `b < n.size`, where `n.size = L` is the bit length of `n`. This is proved in the slightly stronger
  strict form `b < L` (N&C states `b ≤ L`); it is the finiteness fact that bounds the exponent
  search. The trivial base `a = 1` (which represents only `n = 1`) is excluded, as it evades the
  bound.
* **Correctness of the search** — `Nat.isPerfectPower_iff`: `n.IsPerfectPower` iff `n = 1`, or
  `n = a ^ b` for some base `a` and some exponent `b ∈ Finset.Ico 2 n.size`. Part (1) turns the
  unbounded double existential of the definition into this bounded, finite one.
* **Parts (2)–(3)** — the per-exponent test. For a fixed `b`, whether `∃ a, a ^ b = n` is decided by
  Mathlib's `Nat.exists_pow_eq_iff'`, which reduces it to `(Nat.nthRoot b n) ^ b = n`: compute the
  integer `b`-th root of `N` (the nearest integer to `2 ^ ((log₂ N) / b)`, i.e. N&C's `u₁`/`u₂`
  candidate base) and test its `b`-th power against `N`. This is precisely the root-plus-power check
  parts (2)–(3) describe.
* **Part (4)** — `Nat.instDecidableIsPerfectPower`: the decision procedure, assembled from the
  finite search over `b` (with `Nat.exists_pow_eq_iff'` deciding each inner test). It is a genuine
  computable algorithm — e.g. `by decide` proves `Nat.IsPerfectPower 8` and
  `¬ Nat.IsPerfectPower 6` — and depends on no axioms beyond
  `propext`/`Classical.choice`/`Quot.sound`.

## Scope

Exercise 5.17 asks for an *efficient* (`O(L³)`) algorithm. What is captured formally is the
**algorithm's existence and correctness** — the finite exponent bound (part 1), the exhaustiveness
of the bounded search, the integer-`b`-th-root test (parts 2–3), and the resulting decision
procedure (part 4), all proved and computable. The `O(L²)` / `O(L³)` **operation counts** in parts
(2)–(4) are computational-complexity claims about a cost model in which "operations" are counted;
as with Exercises 5.1, 5.3 and 5.15 the library has no such cost model, so the running-time bound —
and it alone — is deliberately out of scope.
-/
