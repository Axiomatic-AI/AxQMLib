/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.NumberTheory.PerfectPower
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# Concrete: `15` is the smallest modulus requiring the order-finding subroutine

Nielsen & Chuang, Exercise 5.19 (§5.3.2, p. 234): *show that `N = 15` is the smallest number for
which the order-finding subroutine is required, that is, it is the smallest composite number that is
not even or a power of some smaller integer.*

In N&C's reduction of factoring to order-finding (Box 5.3, p. 233), the two classical pre-steps
dispose of the easy inputs: step 1 factors out `2` when `N` is **even**, and step 2 uses the
perfect-power test of Exercise 5.17 to factor `N` when it is **a power of some smaller integer**
`N = a ^ b` (`b ≥ 2`). Order-finding is genuinely required exactly for the remaining inputs: `N`
**composite**, **odd**, and **not a perfect power**. We formalise this class as the predicate
`NeedsOrderFinding` and prove `15` is its least element.

## Faithfulness note: perfect power, not merely prime power

N&C's phrase is *"a power of some smaller integer"*, i.e. `N = a ^ b` for `a < N` and `b ≥ 2` — a
**perfect power** (`Nat.IsPerfectPower`, the very predicate Exercise 5.17 decides), *not* the
narrower *prime power* `p ^ k`. The distinction is real and physically correct: `225 = 15²` is a
perfect power that is **not** a prime power, and step 2's `a ^ b` test already factors it (returning
`15`), so it too avoids order-finding. Formalising the class with `¬ IsPerfectPower` therefore
matches both the textbook wording and the actual reach of the classical pre-steps. For the minimal
element the two readings agree: the only odd composite below `15` is `9 = 3²`, a prime power *and* a
perfect power, so `15` is least either way.
-/

namespace AxQM.Concrete

/-- **The order-finding class (Nielsen & Chuang, §5.3.2).** A modulus `n` genuinely requires the
quantum order-finding subroutine — it survives both classical pre-steps of the factoring reduction —
precisely when it is composite (`1 < n` and not prime), **odd** (`¬ Even n`, escaping step 1's
factor of `2`), and **not a perfect power** (`¬ n.IsPerfectPower`, escaping step 2's `a ^ b` test of
Exercise 5.17). Exercise 5.19 asks for the least such `n`. -/
def NeedsOrderFinding (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ¬ Even n ∧ ¬ n.IsPerfectPower

instance : DecidablePred NeedsOrderFinding := fun n =>
  inferInstanceAs (Decidable (1 < n ∧ ¬ n.Prime ∧ ¬ Even n ∧ ¬ n.IsPerfectPower))

/-- `15` is not a perfect power: `15 = 3 · 5` has two distinct prime factors, so it is not any
`a ^ b` with `b ≥ 2`. (Decided directly, as the sibling `ninetyOne_not_isPerfectPower` of Exercise
5.18 does for `91`.) -/
theorem not_isPerfectPower_fifteen : ¬ (15 : ℕ).IsPerfectPower := by decide

/-- `15` requires the order-finding subroutine: it is composite (`15 = 3 · 5`), odd, and not a
perfect power. -/
theorem needsOrderFinding_fifteen : NeedsOrderFinding 15 := by decide

/-- **Minimality below `15`.** No `n < 15` requires order-finding: every composite `n < 15` is
either even or the perfect power `9 = 3²`, so a classical pre-step of the factoring reduction
handles it. -/
theorem not_needsOrderFinding_of_lt {n : ℕ} (hn : n < 15) : ¬ NeedsOrderFinding n := by
  interval_cases n <;> decide

/-- **Nielsen & Chuang, Exercise 5.19.** `15` is the smallest number requiring the order-finding
subroutine — the least composite that is odd and not a perfect power. -/
theorem isLeast_needsOrderFinding : IsLeast {n | NeedsOrderFinding n} 15 := by
  refine ⟨needsOrderFinding_fifteen, fun n hn => ?_⟩
  by_contra h
  exact not_needsOrderFinding_of_lt (not_le.mp h) hn

end AxQM.Concrete
