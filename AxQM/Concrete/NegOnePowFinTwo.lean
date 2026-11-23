/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Concrete: the sign `(-1)^{x+y}` of two `Fin 2` bits

A one-line combinatorial fact about the `±1` parity of a pair of `Fin 2` bits, extracted so the
detection branches of `AxQM/NC/Ch10/Exercise10_69.lean` (Nielsen & Chuang, Exercise 10.69)
cite it once instead of re-deriving it.
-/

namespace AxQM.Concrete

/-- **Distinct `Fin 2` bits have odd parity:** if `x ≠ y` in `Fin 2` then `(−1)^{x+y} = −1`. Since
`x` and `y` are distinct elements of `{0, 1}`, exactly one is `1`, so `x + y = 1` and the sign is
`−1`. The parity behind "a domain wall flips the syndrome": an adjacent-pair `ZᵢZⱼ` parity check
reads `−1` on a bit-flip residue whose two qubits disagree. -/
theorem neg_one_pow_add_fin_two_of_ne {x y : Fin 2} (h : x ≠ y) :
    (-1 : ℝ) ^ ((x : ℕ) + (y : ℕ)) = -1 := by
  fin_cases x <;> fin_cases y <;> simp_all

end AxQM.Concrete
