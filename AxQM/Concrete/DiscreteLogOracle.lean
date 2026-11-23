/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Concrete: the discrete-logarithm oracle permutation (N&C Exercise 5.25)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 5.25 (p. 240) asks for a
quantum circuit realising the black box `U` of the quantum discrete-logarithm algorithm (§5.4.2),
which takes the base `a` and target `b = aˢ` as parameters and performs

```
|x₁⟩|x₂⟩|y⟩ → |x₁⟩|x₂⟩|y ⊕ b^{x₁} a^{x₂}⟩,
```

writing the value `f(x₁,x₂) = b^{x₁} a^{x₂} (mod N)` of the discrete-log function into the target
register. This file provides the pure `ZMod`/`Fin` combinatorics: the value index and the induced
permutation of the *joint* three-register computational basis `Fin d₁ × Fin d₂ × Fin N`.

## The value and the permutation

For units `a, b : (ZMod N)ˣ` and natural exponents `i, j`, the register index of `b^i a^j (mod N)`
is `dlogValueIndex a b i j : Fin N` (its residue's `ZMod.val`, exactly as `orbitIndex` does for the
single power `xᵏ`). The black box then permutes the joint basis by

```
(x₁, x₂, y) ↦ (x₁, x₂, y + b^{x₁} a^{x₂})
```

leaving the two exponent registers fixed and shifting the value register by the discrete-log value.

**Modelling of `⊕`.** As with the modular adder of Exercise 4.36 (`Concrete.modAddPerm`, whose
circuit `modFourAdder` writes `|x, y⟩ ↦ |x, x + y⟩`), the reversible operation `⊕` on the value
register `X` is taken to be the register's own additive group `Fin N ≅ ZMod N` — the "`⊕` an
appropriately chosen binary operation on `X`" of N&C §5.4.3. On a single bit this is exactly XOR
(addition in `Fin 2`), as used by the library's Deutsch and marking oracles; here it generalises to
the whole value register. This is the natural choice for a `Fin N` register: the literal "bitwise
addition modulo 2" of §5.4.2 is not even closed on `Fin N` unless `N` is a power of two, so a
bitwise-XOR model would have to enlarge the register to `Fin 2ᴸ` and carry the bound `N ≤ 2ᴸ` (an
added hypothesis), whereas `+ mod N` is closed and hypothesis-free. The one physically-operative
case — the algorithm always supplies the target register in `|0⟩` — is insensitive to the choice:
`0 + v = 0 ⊕ v = v`, so either convention writes exactly `|b^{x₁} a^{x₂}⟩`. The shift is a genuine
permutation with inverse the shift by `-v`.

The permutation of basis *indices* is pure combinatorics; the physics claim — that a reversible
quantum circuit realises it on the three registers `qudit d₁ ⊗ qudit d₂ ⊗ qudit N` — is
`AxQM/NC/Ch5/Exercise5_25.lean`, which imports this definition (via the `quditTriplePerm` gate of
`AxQM/Postulates/API/QuditTriplePermGate.lean`).
-/

namespace AxQM.Concrete

/-- **The discrete-logarithm value index** `b^i · a^j mod N : Fin N` (Nielsen & Chuang §5.4.2): the
computational-basis index of the value `f(x₁,x₂) = b^{x₁} a^{x₂}` of the discrete-log function, for
units `a, b : (ZMod N)ˣ` and exponents `i = x₁`, `j = x₂`. It is the `ZMod.val` of the residue
`b^i a^j`, exactly as `orbitIndex` is the index of the single power `xᵏ mod N`. -/
def dlogValueIndex {N : ℕ} [NeZero N] (a b : (ZMod N)ˣ) (i j : ℕ) : Fin N :=
  ⟨((b ^ i * a ^ j : (ZMod N)ˣ) : ZMod N).val, ZMod.val_lt _⟩

/-- **The discrete-logarithm oracle permutation** of the three-register computational basis
`Fin d₁ × Fin d₂ × Fin N` (Nielsen & Chuang Exercise 5.25): the map
`(x₁, x₂, y) ↦ (x₁, x₂, y + b^{x₁} a^{x₂})` that leaves the two exponent registers fixed and shifts
the value register by the discrete-log value `dlogValueIndex a b x₁ x₂`, the addition taken in the
additive group `Fin N` (N&C's `⊕`; see the module docstring). It is a bijection, its inverse
the shift `(x₁, x₂, z) ↦ (x₁, x₂, z - b^{x₁} a^{x₂})` (by `z + v - v = z` and `z - v + v = z`). -/
def dlogOraclePerm {N : ℕ} [NeZero N] (a b : (ZMod N)ˣ) (d₁ d₂ : ℕ) :
    Equiv.Perm (Fin d₁ × Fin d₂ × Fin N) where
  toFun p := (p.1, p.2.1, p.2.2 + dlogValueIndex a b p.1.val p.2.1.val)
  invFun p := (p.1, p.2.1, p.2.2 - dlogValueIndex a b p.1.val p.2.1.val)
  left_inv := by rintro ⟨x₁, x₂, y⟩; simp
  right_inv := by rintro ⟨x₁, x₂, z⟩; simp

/-- **Truth table of `dlogOraclePerm`**: on the joint basis label `(x₁, x₂, y)` it fixes the two
exponent registers and shifts the value register by `dlogValueIndex a b x₁ x₂` (= `b^{x₁} a^{x₂}`),
`(x₁, x₂, y) ↦ (x₁, x₂, y + b^{x₁} a^{x₂})`. -/
@[simp]
theorem dlogOraclePerm_apply {N : ℕ} [NeZero N] (a b : (ZMod N)ˣ) (d₁ d₂ : ℕ)
    (x₁ : Fin d₁) (x₂ : Fin d₂) (y : Fin N) :
    dlogOraclePerm a b d₁ d₂ (x₁, x₂, y)
      = (x₁, x₂, y + dlogValueIndex a b x₁.val x₂.val) := rfl

end AxQM.Concrete
