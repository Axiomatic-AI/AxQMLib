/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Concrete: the combinatorics of the three-qubit bit-flip code (Nielsen & Chuang, §10.1.1)

The three-qubit bit-flip code encodes `|0⟩ ↦ |000⟩`, `|1⟩ ↦ |111⟩`; error-correction against
single bit-flip errors is a *majority vote* on the three physical qubits. This file develops the
underlying **combinatorics** on the eight computational-basis labels, identified with the finite
type `Fin 8` under the big-endian convention

`x = 4·b₁ + 2·b₂ + b₃`  (qubit `1` the most significant bit),

so `0 = 000, 1 = 001, …, 7 = 111`. Everything here is a computation on `Fin 8` / `Fin 4`; the eight
computational-basis projectors and the recovery `ProjectiveUnitaryRecovery` are built on top of it
in `AxQM/NC/Ch10/Exercise10_4.lean`.

## Contents

* `xorPerm m` — the permutation `x ↦ x ⊕ m` of `Fin 8` (bitwise XOR by the mask `m : Fin 8`). A
  bit-flip error on a *subset* of the qubits is `xorPerm m` for the subset's bitmask `m`; the three
  single-qubit flips are `xorPerm 4`, `xorPerm 2`, `xorPerm 1`. It is an involution
  (`xorPerm_xorPerm`), so every error is its own inverse — the reason a bit flip is undone by
  re-applying it.
* `errorMask j` — the bitmask of the single-qubit error diagnosed by syndrome `j : Fin 4`:
  `0 ↦ 0` (no error), `1 ↦ 4`, `2 ↦ 2`, `3 ↦ 1` (flip qubit `j`).
* `syndrome x` — the error syndrome read off a computational-basis outcome `x`: `0` for the
  codewords `000, 111`, and the position `j ∈ {1,2,3}` of the *minority* qubit otherwise
  (majority-vote decoding). `syndrome_xorPerm_errorMask` records that it correctly diagnoses a
  single-qubit error on either codeword.
* `recoveryTarget x` — the codeword (`0` or `7`) that `x` is corrected to, i.e. the majority value
  broadcast to all three qubits; `recovery_xorPerm_errorMask` records that undoing the diagnosed
  error returns a corrupted codeword to its original.
-/

namespace AxQM.Concrete

/-- **The bitwise-XOR permutation** `xorPerm m : Equiv.Perm (Fin 8)`, `x ↦ x ⊕ m`. A bit-flip
error on the subset of the three qubits picked out by the bitmask `m` acts on the computational
basis by this permutation; the single-qubit flips are `xorPerm 4`, `xorPerm 2`, `xorPerm 1` (masks
`100, 010, 001`). Its own inverse (XOR by `m` is an involution), which is exactly why a bit-flip
error is corrected by re-applying it. -/
def xorPerm (m : Fin 8) : Equiv.Perm (Fin 8) where
  toFun x := ⟨x.1 ^^^ m.1, Nat.xor_lt_two_pow (n := 3) x.2 m.2⟩
  invFun x := ⟨x.1 ^^^ m.1, Nat.xor_lt_two_pow (n := 3) x.2 m.2⟩
  left_inv x := by ext; simp [Nat.xor_assoc]
  right_inv x := by ext; simp [Nat.xor_assoc]

@[simp] theorem xorPerm_apply (m x : Fin 8) : (xorPerm m x).1 = x.1 ^^^ m.1 := rfl

/-- `xorPerm` by the zero mask is the identity: no qubits are flipped. -/
@[simp] theorem xorPerm_zero : xorPerm 0 = 1 := by
  ext x; simp

/-- **`xorPerm m` is an involution**: applying a bit-flip error twice undoes it,
`xorPerm m (xorPerm m x) = x`. XOR by `m` twice cancels (`Nat.xor_assoc`, `Nat.xor_self`). -/
@[simp] theorem xorPerm_xorPerm (m x : Fin 8) : xorPerm m (xorPerm m x) = x := by
  ext; simp [Nat.xor_assoc]

/-- `xorPerm m` is its own inverse. -/
@[simp] theorem xorPerm_symm (m : Fin 8) : (xorPerm m).symm = xorPerm m :=
  Equiv.ext fun _ => rfl

/-- The **single-qubit error masks** indexed by syndrome value `j : Fin 4`: syndrome `0` is no
error (`mask 0`), and syndrome `j ∈ {1,2,3}` is the flip of qubit `j`, with masks `4, 2, 1`
(big-endian). -/
def errorMask : Fin 4 → Fin 8 := ![0, 4, 2, 1]

/-- **The error syndrome of a computational-basis outcome** `x : Fin 8`. It is `0` on the two
codewords `000` (`0`) and `111` (`7`), and otherwise the position `j ∈ {1,2,3}` of the single
minority qubit — the majority-vote diagnosis "bit `j` flipped". Explicitly
`[0, 3, 2, 1, 1, 2, 3, 0]` on `0, …, 7`. -/
def syndrome : Fin 8 → Fin 4 := ![0, 3, 2, 1, 1, 2, 3, 0]

/-- **The codeword an outcome is corrected to**: `recoveryTarget x` is `0 = 000` when the majority
of `x`'s bits is `0` and `7 = 111` when it is `1`. Explicitly `[0,0,0,7,0,7,7,7]`. -/
def recoveryTarget : Fin 8 → Fin 8 := ![0, 0, 0, 7, 0, 7, 7, 7]

/-- **The syndrome correctly diagnoses a single-qubit error on either codeword.** For every
syndrome value `j : Fin 4` and either codeword `c ∈ {0, 7}`, applying the corresponding single-qubit
error `xorPerm (errorMask j)` to `c` produces an outcome whose syndrome is exactly `j`. This is the
formal content of "the measurement result can be used to diagnose the error syndrome: no bit
flipped (`j = 0`) or bit number `j` flipped". -/
theorem syndrome_xorPerm_errorMask (j : Fin 4) (c : Fin 8) (hc : c = 0 ∨ c = 7) :
    syndrome (xorPerm (errorMask j) c) = j := by
  fin_cases j <;> rcases hc with rfl | rfl <;> decide

/-- **Undoing the diagnosed error returns a corrupted codeword to its original.** Applying the
error `xorPerm (errorMask j)` to a codeword `c ∈ {0,7}` and then the recovery flip
`xorPerm (errorMask (syndrome …))` — which re-applies the *diagnosed* error — recovers `c` exactly.
Since the diagnosis is correct (`syndrome_xorPerm_errorMask`) and `xorPerm` is an involution, the
recovery flip is the same flip and cancels the error. -/
theorem recovery_xorPerm_errorMask (j : Fin 4) (c : Fin 8) (hc : c = 0 ∨ c = 7) :
    xorPerm (errorMask (syndrome (xorPerm (errorMask j) c))) (xorPerm (errorMask j) c) = c := by
  fin_cases j <;> rcases hc with rfl | rfl <;> decide

/-- **The recovery flip sends every outcome to its corrected codeword**: applying
`xorPerm (errorMask (syndrome x))` to `x` yields `recoveryTarget x ∈ {0,7}`, the majority codeword.
This is majority-vote decoding as a single permutation applied conditionally on the outcome. -/
theorem xorPerm_errorMask_syndrome (x : Fin 8) :
    xorPerm (errorMask (syndrome x)) x = recoveryTarget x := by
  fin_cases x <;> decide

/-- `recoveryTarget` lands on a codeword: `recoveryTarget x = 0` or `= 7`. -/
theorem recoveryTarget_eq (x : Fin 8) : recoveryTarget x = 0 ∨ recoveryTarget x = 7 := by
  fin_cases x <;> decide

end AxQM.Concrete
