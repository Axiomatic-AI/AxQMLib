/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledNot

/-!
# Concrete: the back-pair wire-gather permutation

Pure `Fin`/`Equiv` combinatorics for **addressing a two-qubit gate to an arbitrary ordered wire
pair**.  To place a gate whose canonical form acts on the *last two* wires `(n, n+1)` of an
`(n+2)`-wire register onto a chosen ordered pair `(i, j)`, one relabels the wires by a permutation
`σ` with `σ (wire n) = i` (the control) and `σ (wire n+1) = j` (the target); the remaining `n` wires
map onto `{i, j}ᶜ` in some order (their identity is immaterial).

`cnotPairGatherPerm n i j` is such a permutation, built as a product of two transpositions.  It
is the wire-addressing gadget used for placing gates on chosen wires (e.g. Nielsen & Chuang,
Problem 4.6, where the gate-teleportation `CNOT` gadget is routed onto arbitrary wires by
conjugating with `qubit.tensorPowCongr` of this permutation).
-/

namespace AxQM.Concrete

/-- **The back-pair wire-gather permutation** of `Fin (n+2)` sending the last-two-wire positions
`(Fin.natAdd n 0, Fin.natAdd n 1)` — wires `n` and `n+1` — to a designated ordered pair `(i, j)`:
`(Equiv.swap n i).trans (Equiv.swap ((Equiv.swap n i) (n+1)) j)`.  The first transposition carries
`n ↦ i`; the second carries the image of `n+1` to `j` while fixing `i` (when `i ≠ j`).  So
`σ (wire n) = i` (`cnotPairGatherPerm_apply_control`, for `i ≠ j`) and `σ (wire n+1) = j`
(`cnotPairGatherPerm_apply_target`); the other `n` wires map onto `{i, j}ᶜ`. -/
def cnotPairGatherPerm (n : ℕ) (i j : Fin (n + 2)) : Equiv.Perm (Fin (n + 2)) :=
  (Equiv.swap (Fin.natAdd n 0) i).trans
    (Equiv.swap ((Equiv.swap (Fin.natAdd n 0) i) (Fin.natAdd n 1)) j)

/-- **`cnotPairGatherPerm` sends the control position `n` to `i`** (for `i ≠ j`): the first swap
carries `n ↦ i`, and the second swap fixes `i` because `i ≠ (swap n i)(n+1)` (that would force
`n+1 = n`) and `i ≠ j`. -/
theorem cnotPairGatherPerm_apply_control (n : ℕ) (i j : Fin (n + 2)) (hij : i ≠ j) :
    cnotPairGatherPerm n i j (Fin.natAdd n 0) = i := by
  have hab : (Fin.natAdd n 0 : Fin (n + 2)) ≠ Fin.natAdd n 1 := by
    apply Fin.ne_of_val_ne; simp only [Fin.val_natAdd]; omega
  unfold cnotPairGatherPerm
  simp only [Equiv.trans_apply, Equiv.swap_apply_left]
  have hbi : (Equiv.swap (Fin.natAdd n 0) i) (Fin.natAdd n 1) ≠ i := fun h =>
    hab ((Equiv.swap (Fin.natAdd n 0) i).injective
      ((Equiv.swap_apply_left (Fin.natAdd n 0) i).trans h.symm))
  rw [Equiv.swap_apply_of_ne_of_ne hbi.symm hij]

/-- **`cnotPairGatherPerm` sends the target position `n+1` to `j`**: the second swap carries
`(swap n i)(n+1) ↦ j`, and the first swap has already produced `(swap n i)(n+1)` as the argument, so
the composite lands on `j` unconditionally. -/
theorem cnotPairGatherPerm_apply_target (n : ℕ) (i j : Fin (n + 2)) :
    cnotPairGatherPerm n i j (Fin.natAdd n 1) = j := by
  unfold cnotPairGatherPerm
  simp only [Equiv.trans_apply, Equiv.swap_apply_left]

end AxQM.Concrete
