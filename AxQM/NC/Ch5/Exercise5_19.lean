/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SmallestOrderFindingModulus

/-!
# Nielsen & Chuang, Exercise 5.19

Show N=15 is the smallest composite not even and not a prime power (smallest needing order-finding).

The factoring-to-order-finding reduction (N&C Box 5.3) uses classical
pre-steps to dispose of even `N` and of perfect powers `N = aᵇ` (`b ≥ 2`, the test of Exercise
5.17); order-finding is required exactly for the composite, odd, non-perfect-power moduli. Exercise
5.19 asks for the least such modulus, `15`, an explicit arithmetic fact.

The formalisation is in `AxQM/Concrete/SmallestOrderFindingModulus.lean`:

* `AxQM.Concrete.NeedsOrderFinding` — the order-finding class: `n` is composite, odd, and
  not a perfect power (`Nat.IsPerfectPower`, faithfully rendering N&C's "power of some smaller
  integer" rather than the narrower "prime power").
* `AxQM.Concrete.needsOrderFinding_fifteen` — `15` is in the class.
* `AxQM.Concrete.not_needsOrderFinding_of_lt` — no `n < 15` is in the class.
* `AxQM.Concrete.isLeast_needsOrderFinding` — `IsLeast {n | NeedsOrderFinding n} 15`, the
  statement that `15` is the smallest modulus requiring order-finding.
-/
