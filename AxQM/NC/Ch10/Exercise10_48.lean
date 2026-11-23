/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorLogicalOperators
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.NC.Ch10.Exercise10_6

/-!
# Nielsen & Chuang, Exercise 10.48 — the Shor-code logical operators `Z̄`, `X̄`

*(N&C §10.5.6, Fig 10.11, p. 468.)*

Show Zbar=X1..X9 and Xbar=Z1..Z9 act as logical Z,X on the Shor code.

Figure 10.11 lists these two operators alongside the eight stabilizer generators, with the
parenthetical *"(Yes, they really are the reverse of what one might naively expect!)"*: the logical
`Z` is the product of the nine Pauli **`X`**s, and the logical `X` is the product of the nine Pauli
**`Z`**s. The reversal is the signature of the phase-flip/bit-flip **concatenation**: each block
encodes a phase-flip qubit `|±⟩`, so a *bit* flip of the encoded qubit (logical `X`) is a *phase*
flip `Z⊗Z⊗Z` of the underlying blocks, and a *phase* flip of the encoded qubit (logical `Z`) is a
*bit* flip `X⊗X⊗X`.

## What this formalisation proves, and where it lives

N&C's "That is, …" spells out the meaning of "act as logical `Z` / `X`" as three things, all
formalised here (the operators `shorLogicalZBar = Z̄`, `shorLogicalXBar = X̄` and the whole algebra
are in `AxQM/Postulates/API/ShorLogicalOperators.lean`):

* **Commutation with the generators.** Each of `Z̄`, `X̄` commutes with every one of the eight
  Figure-10.11 generators `g₁ = Z₁Z₂, …, g₆ = Z₈Z₉, g₇ = X₁…X₆, g₈ = X₄…X₉`
  (`shorLogicalZBar_op_comm_shorZ12, …, shorLogicalXBar_op_comm_shorPhaseSyndromeX456789` — sixteen
  results). So both lie in the normalizer of the stabilizer. Every generator overlaps `Z̄`/`X̄` in
  an *even* number of anticommuting Pauli positions, so the signs `(−1)^{even}` cancel.
* **Anticommutation `X̄ Z̄ = −Z̄ X̄`** (`shorLogicalXBar_op_anticomm_shorLogicalZBar_op`): the two
  operators overlap in all *nine* positions, `(−1)^9 = −1` — the logical Pauli algebra that makes
  them a genuine logical `Z, X` pair.
* **Independence of the stabilizer** — the two theorems below. Every stabilizer element fixes
  both codewords (`shorZ12_hasEigenstate_one_shorCodeword`, …), whereas `Z̄` acts on `|1_L⟩` with
  eigenvalue `−1` (`shorLogicalZBar_not_hasEigenstate_one_shorCodeword_one`) and `X̄` maps `|0_L⟩`
  to `|1_L⟩ ≠ |0_L⟩` (`shorLogicalXBar_evolvePure_shorCodeword_zero_ne`); hence neither is a
  stabilizer element, i.e. both are independent of the generators.

The *operational* action on the encoded qubit — `Z̄` diagonal with eigenvalue `(−1)^s` and `X̄`
permuting the codewords — is the pair of theorems
`shorLogicalZBar_hasEigenstate_shorCodeword` / `shorLogicalXBar_evolvePure_shorCodeword` below; it
exhibits `Z̄, X̄` acting exactly as the single-qubit Paulis on `|0_L⟩, |1_L⟩` and feeds the
independence witnesses.

## Fidelity

The operator definitions and the sixteen commutations + the anticommutation are in
`AxQM/Postulates/API/ShorLogicalOperators.lean`; the operational statements and the independence
witnesses below are stated through `Observable.HasEigenstate` / `Evolution.evolvePure`. Nothing is
weakened: the operators are exactly `X₁…X₉` and `Z₁…Z₉` of Figure 10.11 and the codewords are
exactly the pair of Equation (10.13).

## Related results

The `Z ⊗ Z ⊗ Z` block phase gate `blockZGate` is N&C's phase-flip **recovery** operator `Z₁Z₂Z₃`
from Exercise 10.6 (`AxQM/Postulates/API/ShorCodePhaseFlip.lean`); `X̄` is its three-block
tensor. That
the same gate serves as both a block *recovery* (Ex 10.6) and, tensored across all three blocks, the
*logical `X`* (this exercise) is the concatenation structure at work. The sign-readout observable
`blockXObservable` (`X⊗X⊗X`) and the eight generators come from
`AxQM/Postulates/API/ShorCodeBlock.lean` and `AxQM/Postulates/API/ShorStabilizer.lean`.
-/

open scoped TensorProduct

namespace AxQM

/-- **Nielsen & Chuang, Exercise 10.48 (`Z̄` acts as logical `Z`).** The operator
`Z̄ = X₁…X₉` is diagonal on the Shor codewords with eigenvalue `(−1)^s`:
`Z̄|0_L⟩ = |0_L⟩` and `Z̄|1_L⟩ = −|1_L⟩`, exactly as logical `Z` acts on `|0_L⟩, |1_L⟩`. Each
block's `X⊗X⊗X` reads the codeword's sign `(−1)^s` (`blockXObservable_hasEigenstate_catBlockState`),
then the three signs combine as `((−1)^s)^3 = (−1)^s`. -/
theorem shorLogicalZBar_hasEigenstate_shorCodeword (s : Fin 2) :
    shorLogicalZBar.HasEigenstate ((-1 : ℝ) ^ (s : ℕ)) (shorCodeword s) := by
  have h := (blockXObservable_hasEigenstate_catBlockState s).tmul
    ((blockXObservable_hasEigenstate_catBlockState s).tmul
      (blockXObservable_hasEigenstate_catBlockState s))
  have hval : ((-1 : ℝ) ^ (s : ℕ)) * ((-1) ^ (s : ℕ) * (-1) ^ (s : ℕ)) = (-1) ^ (s : ℕ) := by
    fin_cases s <;> norm_num
  rw [hval] at h
  simpa [shorLogicalZBar, shorCodeword, shorCatProduct] using h

/-- **Nielsen & Chuang, Exercise 10.48 (`X̄` acts as logical `X`).** The operator
`X̄ = Z₁…Z₉` swaps the Shor codewords: `X̄|s_L⟩ = |(s+1)_L⟩`, i.e. `X̄|0_L⟩ = |1_L⟩` and
`X̄|1_L⟩ = |0_L⟩`, exactly as logical `X` acts on `|0_L⟩, |1_L⟩`. Each block's `Z⊗Z⊗Z` flips its cat
sign `catBlockState σ ↦ catBlockState (σ+1)` (`blockZGate_evolvePure_catBlockState`, from Exercise
10.6), so all three blocks flip and the equal-sign codeword `shorCatProduct s s s` becomes
`shorCatProduct (s+1) (s+1) (s+1)`. -/
theorem shorLogicalXBar_evolvePure_shorCodeword (s : Fin 2) :
    shorLogicalXBar.evolvePure (shorCodeword s) = shorCodeword (s + 1) := by
  simp only [shorLogicalXBar, shorCodeword, shorCatProduct, Evolution.tmul_evolvePure,
    blockZGate_evolvePure_catBlockState]

/-- **`Z̄` is independent of the stabilizer.** It does *not* fix the logical codeword `|1_L⟩`: it
acts there with eigenvalue `−1` (`shorLogicalZBar_hasEigenstate_shorCodeword` at `s = 1`), so it is
not the `+1` action of any stabilizer element (every generator fixes both codewords). Hence
`Z̄ ∉ S` — the "independent of the generators" half of the exercise for `Z̄`. -/
theorem shorLogicalZBar_not_hasEigenstate_one_shorCodeword_one :
    ¬ shorLogicalZBar.HasEigenstate 1 (shorCodeword 1) := by
  intro h
  have h2 := shorLogicalZBar_hasEigenstate_shorCodeword 1
  rw [Observable.HasEigenstate] at h h2
  rw [h] at h2
  apply (shorCodeword 1).vec_ne_zero
  simp only [Fin.val_one, pow_one] at h2
  rw [← sub_eq_zero, ← sub_smul] at h2
  norm_num at h2
  exact h2

/-- **The two logical codewords are distinct:** `|1_L⟩ ≠ |0_L⟩`, since they are orthonormal
(`shorCodeword_inner`). Used to witness that `X̄`, which swaps them, is not a stabilizer element. -/
theorem shorCodeword_one_ne_zero : shorCodeword 1 ≠ shorCodeword 0 := by
  intro h
  have h0 : (inner ℂ (shorCodeword 1).vec (shorCodeword 0).vec) = 0 := by
    simpa using shorCodeword_inner 1 0
  rw [h] at h0
  simp only [shorCodeword_inner] at h0
  norm_num at h0

/-- **`X̄` is independent of the stabilizer.** It does *not* fix the logical codeword `|0_L⟩`: it
maps it to `|1_L⟩ ≠ |0_L⟩` (`shorLogicalXBar_evolvePure_shorCodeword`, `shorCodeword_one_ne_zero`),
whereas every stabilizer element fixes both codewords. Hence `X̄ ∉ S` — the "independent of the
generators" half of the exercise for `X̄`. -/
theorem shorLogicalXBar_evolvePure_shorCodeword_zero_ne :
    shorLogicalXBar.evolvePure (shorCodeword 0) ≠ shorCodeword 0 := by
  rw [shorLogicalXBar_evolvePure_shorCodeword]
  simpa using shorCodeword_one_ne_zero

end AxQM
