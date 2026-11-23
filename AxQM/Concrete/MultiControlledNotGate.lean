/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PermutationGate
import AxQM.Concrete.ControlledSingleQubit
import AxQM.Concrete.MultiControlledNot
import AxQM.Concrete.Pauli

/-!
# Concrete: the matrix multiply-controlled `NOT` is the permutation gate of the classical `mcNot`

The §4.3 reduction of a controlled single-qubit gate to `H, S, CNOT, Toffoli`
(`Concrete/ControlledSingleQubitABCReduction.lean`) writes an all-`1`-controlled single-qubit gate
in terms of a **multiply-controlled `NOT`** `N = ctrlSingleQubit enc j 1 pauliX` (the matrix that
flips the target bit `j` of `|enc x⟩` exactly when every other bit of `x` is `1`). That gate is a
*classical reversible* gate — a permutation of the computational basis — and this file identifies it
with the `Concrete/MultiControlledNot.lean` combinatorial multiply-controlled `NOT`
`mcNot (univ \ {j}) j` (controls = all wires but `j`, target `j`), lifted to a matrix by the
permutation gate `permGate`:

* `AxQM.Concrete.ctrlSingleQubit_one_pauliX_eq_permGate` — **the bridge**:
  `ctrlSingleQubit enc j 1 pauliX = permGate enc (mcNotPerm (univ \ {j}) j)`. The two objects agree
  entrywise: the controlled-`X` gate's action on `|enc x⟩` — flip bit `j` iff all other bits are `1`
  — *is* the classical `mcNot (univ \ {j}) j` truth table `x ↦ update x j (x j + ctrlBit x)`
  (`ctrlBit` is `1` exactly on the all-`1`-elsewhere condition), transported through the encoding.

This is the link that lets the whole reversible-circuit development of
`Concrete/MultiControlledNot*` (the `O(n²)` no-work-qubit `Cⁿ(X)` circuit and the Gray-code/Barenco
machinery, all phrased on bit-string permutations) be transported to the matrix multiply-controlled
`NOT` the §4.3 reduction produces, via `permGate`'s `*`-homomorphism algebra.

Everything is stated for raw complex matrices, the encoding equivalence, the concrete gate
`ctrlSingleQubit`, `pauliX`, and the classical `mcNot`/`ctrlBit`.
-/

open Matrix

namespace AxQM.Concrete

variable {m d : ℕ}

/-- **The `pauliX` block reads off bit inequality.** For `a, b : Fin 2`,
`pauliX a b = 1` when `a = b + 1` (`a ≠ b`, i.e. `X` flips the bit) and `0` otherwise. -/
theorem pauliX_apply_eq (a b : Fin 2) : pauliX a b = if a = b + 1 then (1 : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;> rfl

/-- **The entrywise heart of the identification**, on bare bit-strings `x`, `y`, for an arbitrary
control set `S` (with `j ∉ S`): the `S`-controlled `X` gate's `(x, y)` entry — apply `pauliX` to
bit `j` when every control wire in `S` is `1`, else act as the identity — equals `1` exactly when
`x` is the classical `mcNot`-image of `y` (controls `S`, target `j`), and `0` otherwise. The
all-`1`-controlled special case is `ctrlOne_pauliX_entry` below (`S = univ \ {j}`); the subset form
is what the multiply-controlled-gate bridge `mcCtrlSingleQubit_pauliX_eq_permGate`
(`Concrete/MultiControlledSingleQubit.lean`) consumes. -/
theorem ctrlSet_pauliX_entry (S : Finset (Fin m)) {j : Fin m} (hj : j ∉ S) (x y : Fin m → Fin 2) :
    (if ∀ k, k ≠ j → x k = y k then
        (if ∀ k ∈ S, x k = 1 then pauliX (x j) (y j) else if x j = y j then 1 else 0)
      else 0)
      = if x = mcNot S j y then (1 : ℂ) else 0 := by
  by_cases hoff : ∀ k, k ≠ j → x k = y k
  · rw [ite_eq_left hoff]
    have hupd : (x = mcNot S j y) ↔ (x j = y j + ctrlBit S y) := by
      rw [mcNot, Function.eq_update_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, fun k hk => hoff k hk⟩⟩
    simp only [hupd]
    by_cases hctrl : ∀ k ∈ S, x k = 1
    · rw [ite_eq_left hctrl]
      have hcb : ctrlBit S y = 1 := by
        rw [ctrlBit, ite_eq_left]
        intro k hk
        rw [← hoff k (fun h => hj (h ▸ hk)), hctrl k hk]
      simp only [hcb]
      exact pauliX_apply_eq (x j) (y j)
    · rw [ite_eq_right hctrl]
      have hcb : ctrlBit S y = 0 := by
        rw [ctrlBit, ite_eq_right]
        intro hall
        exact hctrl fun k hk => (hoff k (fun h => hj (h ▸ hk))).trans (hall k hk)
      simp only [hcb, add_zero]
  · rw [ite_eq_right hoff, eq_comm, ite_eq_right]
    intro heq
    exact hoff fun k hk => by rw [heq, mcNot_apply_of_ne _ _ _ hk]

/-- **The all-`1`-controlled special case of `ctrlSet_pauliX_entry`** (`S = univ \ {j}`): the
all-`1`-controlled `X` gate's `(x, y)` entry equals `1` exactly when `x = mcNot (univ \ {j}) j y`.
A one-line corollary — the control condition `∀ k, k ≠ j → x k = 1` is the `S = univ \ {j}` form of
`∀ k ∈ S, x k = 1`. -/
theorem ctrlOne_pauliX_entry (j : Fin m) (x y : Fin m → Fin 2) :
    (if ∀ k, k ≠ j → x k = y k then
        (if ∀ k, k ≠ j → x k = 1 then pauliX (x j) (y j) else if x j = y j then 1 else 0)
      else 0)
      = if x = mcNot (Finset.univ \ {j}) j y then (1 : ℂ) else 0 := by
  have hiff : (∀ k, k ≠ j → x k = 1) ↔ (∀ k ∈ Finset.univ \ {j}, x k = 1) := by
    constructor
    · intro h k hk; rw [Finset.mem_sdiff, Finset.mem_singleton] at hk; exact h k hk.2
    · intro h k hk; exact h k (by simp [hk])
  simp only [hiff]
  exact ctrlSet_pauliX_entry (Finset.univ \ {j}) (by simp) x y

/-- **The matrix multiply-controlled `NOT` is the permutation gate of the classical `mcNot`.**
`ctrlSingleQubit enc j 1 pauliX = permGate enc (mcNotPerm (univ \ {j}) j)`: the all-`1`-controlled
`X` gate (flip target wire `j` of `|enc x⟩` iff every other wire is `1`) realises, through the
encoding `enc`, the bit-string permutation `mcNot (univ \ {j}) j`. This is the bridge that carries
the combinatorial `Cⁿ(X)` circuit development (`Concrete/MultiControlledNot*`) over to the matrix
gate. -/
theorem ctrlSingleQubit_one_pauliX_eq_permGate (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m) :
    ctrlSingleQubit enc j 1 pauliX
      = permGate enc (mcNotPerm (Finset.univ \ {j}) (show j ∉ Finset.univ \ {j} by simp)) := by
  ext i i'
  have hcond : (i = enc (mcNot (Finset.univ \ {j}) j (enc.symm i')))
      ↔ (enc.symm i = mcNot (Finset.univ \ {j}) j (enc.symm i')) := by rw [Equiv.symm_apply_eq]
  simp only [ctrlSingleQubit, Matrix.of_apply, permGate_apply, mcNotPerm_apply, Pi.one_apply, hcond]
  exact ctrlOne_pauliX_entry j (enc.symm i) (enc.symm i')

end AxQM.Concrete
