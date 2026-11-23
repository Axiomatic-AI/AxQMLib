/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QftRegisterBridge
import AxQM.Core.MultiControlledNotBasis

/-!
# Digit-form basis action of the measured-QFT register bridge (N&C Problem 5.2)

The register bridge `quditPowTower n : qudit (2ⁿ⁺¹) ≃ₛ qtower n qubit` identifies the
single `2ⁿ⁺¹`-level register — where the quantum Fourier transform `qftEvolution (2ⁿ⁺¹)` lives —
with the right-nested `(n+1)`-qubit control tower. Its action on the computational basis is given
there only in the *recursive peel* form `quditPowTower_congr_quditBasis_succ` (split off one leading
qubit per step). This file closes that recursion into the **global binary-expansion dictionary**:
the bridge sends the register ket `|j⟩` to the tower product state `towerKet n b` whose wire bits
`b` are the binary digits of `j`.

## The endianness, and why `Fin.rev`

Two conventions meet here and they run in *opposite* directions:

* the **bridge** peels the leading qubit *big-endian* — `quditPowTower` iterates `quditProdIso 2 _`,
  whose split `finProdFinEquiv (x, y) = y + 2ⁿ⁺¹ · x` puts the leading tower wire `0` at the *most
  significant* bit (coefficient `2ⁿ`);
* the **matrix gates** of the Figure 5.1 circuit (`Concrete.singleQubitOnWire` /
  `Concrete.mcCtrlSingleQubit`) address wires through `enc = finFunctionFinEquiv`, which is
  *little-endian* — wire `c` carries the coefficient of `2ᶜ` (`finFunctionFinEquiv_symm_apply_val`).

So tower wire `i` is register bit `n − i`, i.e. `finFunctionFinEquiv.symm j i.rev`, and the
dictionary carries the reversal `Fin.rev` that reconciles the two orderings. This is the
convention-alignment the wire-addressed gate re-expressions rewrite through.

## What is formalised

* `quditPowTower_congr_quditBasis` — the dictionary: `Φₙ |j⟩ = towerKet n (i ↦ (bits j) i.rev)`
  with `bits j = finFunctionFinEquiv.symm j` the little-endian binary digits and `Φₙ =
  quditPowTower n`. Proved by induction on `n`, closing the recursive peel
  `quditPowTower_congr_quditBasis_succ` with the tower recursion `towerKet_succ`.
* `quditPowTower_congr_quditBasis_apply` — the **encode** form the matrix gates consume: for a
  wire bit-string `k : Fin (n+1) → Fin 2`, the register ket at the little-endian index
  `finFunctionFinEquiv k` maps to the tower state `towerKet n (k ∘ Fin.rev)`. (Every register index
  is such a `finFunctionFinEquiv k`, so this is equivalent to the dictionary; it is the form in
  which a Figure 5.1 gate — which acts on `quditBasis (finFunctionFinEquiv k)` — meets the tower.)

This extends the bridge of `AxQM/Core/QftRegisterBridge.lean` and lands in the tower basis of
`AxQM/Core/MultiControlledNotBasis.lean`. The two `private` lemmas are local base-2 digit arithmetic
(pure `Nat` facts).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- The most-significant base-2 digit of `j : Fin (2ᵐ⁺¹)` is the quotient `j / 2ᵐ`: since
`j < 2ᵐ⁺¹ = 2ᵐ · 2`, the reduction mod `2` in `finFunctionFinEquiv.symm` is vacuous. A local
digit-arithmetic helper for the bridge dictionary. -/
private theorem finFunctionFinEquiv_symm_last_eq_div (m : ℕ) (j : Fin (2 ^ (m + 1))) :
    (finFunctionFinEquiv.symm j (Fin.last m) : ℕ) = (j : ℕ) / 2 ^ m := by
  rw [finFunctionFinEquiv_symm_apply_val]
  simp only [Fin.val_last]
  have hj : (j : ℕ) < 2 ^ m * 2 := by rw [← pow_succ]; exact j.isLt
  exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hj)

/-- A base-2 digit below the cut is untouched by reducing mod `2ᵐ⁺¹`: for `c ≤ m`, the `c`-th bit of
`a` equals the `c`-th bit of `a % 2ᵐ⁺¹`, because `2ᶜ⁺¹ ∣ 2ᵐ⁺¹`. A local digit-arithmetic helper for
the bridge dictionary. -/
private theorem bit_eq_bit_mod_two_pow (m a c : ℕ) (hc : c < m + 1) :
    a / 2 ^ c % 2 = a % 2 ^ (m + 1) / 2 ^ c % 2 := by
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  calc 2 ^ c * 2 = 2 ^ (c + 1) := by rw [pow_succ]
    _ ∣ 2 ^ (m + 1) := pow_dvd_pow 2 (by omega)

/-- **The register bridge as a binary-expansion dictionary.** On a computational-basis ket, the
measured-QFT register bridge `quditPowTower n : qudit (2ⁿ⁺¹) ≃ₛ qtower n qubit` sends `|j⟩` to the
tower product state `towerKet n b` whose bits are the binary digits of `j`, with the big-endian
reversal `Fin.rev` (tower wire `i` is register bit `n − i`), i.e.
`b i = finFunctionFinEquiv.symm j i.rev`.

This closes the recursive peel `quditPowTower_congr_quditBasis_succ` into a global closed form (by
induction on `n`, matched against the tower recursion `towerKet_succ`), the dictionary the
wire-addressed re-expression of the Figure 5.1 gates rewrites through. -/
theorem quditPowTower_congr_quditBasis (n : ℕ) (j : Fin (2 ^ (n + 1))) :
    PureState.congr (quditPowTower n) (quditBasis j)
      = towerKet n (fun i => finFunctionFinEquiv.symm j i.rev) := by
  induction n with
  | zero =>
      have hj : finFunctionFinEquiv.symm j (Fin.last 0) = j := by
        apply Fin.ext; rw [finFunctionFinEquiv_symm_last_eq_div]; simp
      rw [towerKet_zero, Fin.rev_zero, hj]
      exact PureState.congr_refl (quditBasis j)
  | succ n ih =>
      -- Decompose `j = x·2ⁿ⁺¹ + y` big-endian: leading bit `x`, tail `y = j mod 2ⁿ⁺¹`.
      have peel := quditPowTower_congr_quditBasis_succ n
        (finFunctionFinEquiv.symm j (Fin.last (n + 1)))
        ⟨(j : ℕ) % 2 ^ (n + 1), Nat.mod_lt _ (by positivity)⟩
      have hjxy : (finCongr (pow_succ' 2 (n + 1))).symm
          (finProdFinEquiv (finFunctionFinEquiv.symm j (Fin.last (n + 1)),
            ⟨(j : ℕ) % 2 ^ (n + 1), Nat.mod_lt _ (by positivity)⟩)) = j := by
        apply Fin.ext
        have hval : (((finCongr (pow_succ' 2 (n + 1))).symm
              (finProdFinEquiv (finFunctionFinEquiv.symm j (Fin.last (n + 1)),
                ⟨(j : ℕ) % 2 ^ (n + 1), Nat.mod_lt _ (by positivity)⟩))) : ℕ)
            = ((j : ℕ) % 2 ^ (n + 1))
              + 2 ^ (n + 1) * (finFunctionFinEquiv.symm j (Fin.last (n + 1)) : ℕ) := by
          simp [finCongr_symm]
        rw [hval, finFunctionFinEquiv_symm_last_eq_div]
        exact Nat.mod_add_div _ _
      rw [hjxy] at peel
      rw [peel, ih, towerKet_succ, Fin.rev_zero]
      -- Leading wire matches (`quditBasis`/`qubitBasis` agree on `Fin 2`); align the tail bits.
      congr 1
      congr 1
      funext i
      rw [Fin.rev_succ]
      apply Fin.ext
      rw [finFunctionFinEquiv_symm_apply_val, finFunctionFinEquiv_symm_apply_val, Fin.val_castSucc]
      exact (bit_eq_bit_mod_two_pow n (j : ℕ) _ (Fin.rev i).isLt).symm

/-- **The bridge dictionary in encode form** (the shape the Figure 5.1 matrix gates meet). For a
wire bit-string `k : Fin (n+1) → Fin 2`, the register ket at the little-endian index
`finFunctionFinEquiv k` is carried by the bridge `quditPowTower n` to the tower product state
`towerKet n (k ∘ Fin.rev)`. The matrix gates act on `quditBasis (finFunctionFinEquiv k)`, so this is
how such a gate's action is read on the qubit tower; it follows from
`quditPowTower_congr_quditBasis` by the round-trip
`finFunctionFinEquiv.symm ∘ finFunctionFinEquiv`. -/
theorem quditPowTower_congr_quditBasis_apply (n : ℕ) (k : Fin (n + 1) → Fin 2) :
    PureState.congr (quditPowTower n) (quditBasis (finFunctionFinEquiv k))
      = towerKet n (fun i => k i.rev) := by
  rw [quditPowTower_congr_quditBasis]
  congr 1
  funext i
  rw [Equiv.symm_apply_apply]

/-- **The bridge dictionary at the reversed wire index.** Specialising the encode form
`quditPowTower_congr_quditBasis_apply` to `k = b ∘ Fin.rev` cancels the two reversals
(`Fin.rev_rev`): the register ket at the little-endian index `finFunctionFinEquiv (b ∘ Fin.rev)` is
carried by the bridge `quditPowTower n` straight back to the tower product state `towerKet n b`.
This is exactly the shape the terminal computational-basis measurement's operator/vector bridge
consumes — the register outcome `towerMeasurementOutcomeEquiv n b`, being
`finFunctionFinEquiv (b ∘ rev)`, reads back to `towerKet n b`. It is shared
by both `qtowerMeasurement_eq_congr_quditMeasurement` and the collapse lemma
`qtowerMeasurement_postMeasurement_eq_towerKet`. -/
theorem quditPowTower_congr_quditBasis_rev (n : ℕ) (b : Fin (n + 1) → Fin 2) :
    PureState.congr (quditPowTower n) (quditBasis (finFunctionFinEquiv (fun j => b j.rev)))
      = towerKet n b := by
  rw [quditPowTower_congr_quditBasis_apply]
  congr 1
  funext i
  simp only [Fin.rev_rev]

end AxQM
