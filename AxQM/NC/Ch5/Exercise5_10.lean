/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.OrderFiveModTwentyOne

/-!
# Nielsen & Chuang, Exercise 5.10

Show that the order of x = 5 modulo N = 21 is 6.

The order of `x` modulo `N` is the least positive integer `r` with `x^r ≡ 1 (mod N)`, i.e. the
multiplicative order of the residue `x` in `ZMod N`. Exercise 5.10 asks for the concrete value
`r = 6` at `x = 5`, `N = 21`.

The formalisation is in `AxQM/Concrete/OrderFiveModTwentyOne.lean`:

* `AxQM.Concrete.orderOf_five_zmod_twentyOne` — `orderOf (5 : ZMod 21) = 6`, the statement
  that `6` is the least positive integer `r` with `5^r ≡ 1 (mod 21)`.
-/
