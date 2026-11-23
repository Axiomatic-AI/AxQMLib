/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Concrete: the modular-addition permutation of a two-register basis (N&C Exercise 4.36)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.36 (p. 189) asks for a
circuit performing `|x, y⟩ → |x, x + y mod n⟩` (with `n = 4` for two-bit numbers). Writing the
two `n`-level registers' computational-basis labels as a pair `(x, y) : Fin n × Fin n`, the induced
permutation of the *joint* basis indices is

```
(x, y) ↦ (x, x + y)
```

with `x + y` computed in `Fin n` — i.e. **modulo `n`**. This is a genuine permutation: its inverse
is `(x, z) ↦ (x, z - x)`.

The physics claim — that a reversible quantum circuit realises this permutation of basis
*indices* on the two `qudit n` registers — is in `AxQM/NC/Ch4/Exercise4_36.lean`, which uses this
definition (via the `quditPairPerm` gate of `AxQM/Postulates/API/QuditPairPermGate.lean`).
-/

namespace AxQM.Concrete

/-- **The modular-addition permutation** of the two-register computational basis
`Fin n × Fin n` (Nielsen & Chuang Exercise 4.36): the map `(x, y) ↦ (x, x + y)` that leaves the
first register fixed and replaces the second by the sum `x + y` computed in `Fin n`, i.e. **modulo
`n`**. It is a bijection with inverse `(x, z) ↦ (x, z - x)` (using `x + y - x = y` and
`x + (z - x) = z` in the additive group `Fin n`). For `n = 4` this is the two-bit modular adder of
the exercise. -/
def modAddPerm (n : ℕ) [NeZero n] : Equiv.Perm (Fin n × Fin n) where
  toFun p := (p.1, p.1 + p.2)
  invFun p := (p.1, p.2 - p.1)
  left_inv := by rintro ⟨x, y⟩; simp [add_sub_cancel_left]
  right_inv := by rintro ⟨x, z⟩; simp [add_sub_cancel]

@[simp]
theorem modAddPerm_apply {n : ℕ} [NeZero n] (p : Fin n × Fin n) :
    modAddPerm n p = (p.1, p.1 + p.2) := rfl

@[simp]
theorem modAddPerm_symm_apply {n : ℕ} [NeZero n] (p : Fin n × Fin n) :
    (modAddPerm n).symm p = (p.1, p.2 - p.1) := rfl

/-! ### Two-bit binary digits and ripple-carry correctness

To realise the modular adder as an *elementary-gate* circuit one works with the binary digits of a
two-bit number `x : Fin 4`, `x = lowBit x + 2 · highBit x`. The following combinatorics record that
a two-bit ripple-carry adder — add the low bits, propagate the carry `x₀ ∧ y₀` into the high bit,
add the high bits, discard the carry-out — computes exactly the sum `x + y` in `Fin 4`, i.e. modulo
`4`. These are the bit-level obligations discharged by `AxQM/NC/Ch4/Exercise4_36.lean`'s
`modFourAdderCircuit`. -/

/-- **The low (`2⁰`) binary digit** of a two-bit number `x : Fin 4`: `x % 2 ∈ {0, 1}`, the value
carried on the least-significant qubit when `x` is written in binary as `x = lowBit x + 2 · highBit
x`. -/
def lowBit (x : Fin 4) : Fin 2 := ⟨x.val % 2, by omega⟩

/-- **The high (`2¹`) binary digit** of a two-bit number `x : Fin 4`: `x / 2 ∈ {0, 1}`, the value
carried on the most-significant qubit when `x` is written in binary as `x = lowBit x + 2 · highBit
x`. -/
def highBit (x : Fin 4) : Fin 2 := ⟨x.val / 2, by have := x.isLt; omega⟩

/-- **Low-bit correctness of the two-bit ripple-carry adder** (Nielsen & Chuang Exercise 4.36): the
least-significant bit of the modular sum `x + y` in `Fin 4` is the XOR `lowBit y + lowBit x` of the
two low input bits — the sum bit produced with no incoming carry. -/
theorem lowBit_add (x y : Fin 4) : lowBit (x + y) = lowBit y + lowBit x := by
  fin_cases x <;> fin_cases y <;> decide

/-- **High-bit correctness of the two-bit ripple-carry adder** (Nielsen & Chuang Exercise 4.36): the
most-significant bit of the modular sum `x + y` in `Fin 4` is `highBit y + lowBit x · lowBit y +
highBit x` — the two high input bits XORed with the carry `lowBit x · lowBit y = x₀ ∧ y₀` from the
low bits. The carry *out* of the high bit is dropped: that is precisely the reduction modulo `4`. -/
theorem highBit_add (x y : Fin 4) :
    highBit (x + y) = highBit y + lowBit x * lowBit y + highBit x := by
  fin_cases x <;> fin_cases y <;> decide

end AxQM.Concrete
