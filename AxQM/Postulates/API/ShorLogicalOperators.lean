/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorStabilizer
import AxQM.Postulates.API.ShorCodePhaseFlip

/-!
# AxQM.Postulates.API — the Shor-code logical operators `Z̄`, `X̄` and their algebra

Infrastructure for Nielsen & Chuang **Exercise 10.48** (§10.5.6, Figure 10.11): the
logical operators `Z̄ = X₁X₂…X₉` and `X̄ = Z₁Z₂…Z₉` of the nine-qubit Shor code, and the
stabilizer-formalism content of the exercise — that each of `Z̄, X̄` **commutes with** the eight
generators of Figure 10.11 (so both lie in the normalizer of the stabilizer), that they are
**independent of** the stabilizer (they act non-trivially on the code space, which every stabilizer
element fixes), and that `X̄` **anticommutes with** `Z̄` (the logical Pauli algebra `X̄Z̄ = −Z̄X̄`).

## The reversal, and how the (anti)commutation is computed

Both operators are three-block tensors of a single-qubit Pauli placed on all nine qubits:
`Z̄ = (X⊗X⊗X)^{⊗3}` (`blockXObservable`) and `X̄ = (Z⊗Z⊗Z)^{⊗3}` (`blockZGate`, the Exercise 10.6
phase-flip recovery operator). N&C's parenthetical *"(Yes, they really are the reverse of what one
might naively expect!)"* is the phase-flip/bit-flip concatenation: logical `Z` is a product of `X`s
and logical `X` a product of `Z`s.

Because both operators and all eight generators are tensors of `±1` Paulis, every (anti)commutation
factorises through the single-qubit relation `X Z = −Z X` (`pauliXObservable_op_anticomm_…`): a
tensor product picks up a sign `(−1)^k`, where `k` is the number of positions at which one factor
carries `X` and the other `Z`. Every generator overlaps `Z̄`/`X̄` in an **even** number of such
positions (so it commutes), while `X̄` and `Z̄` overlap in all **nine** positions (so they
anticommute, `(−1)^9 = −1`). The sign bookkeeping is done once and for all by the three `mapL`
combinators below, which multiply the per-factor signs; the diamond that defeats a naive
`TensorProduct.mapL_mul` rewrite on the nested composite space is avoided by supplying the operator
arguments to `mapL_mul` explicitly (cf. `Observable.tmul_op_mul_self`).

The statements about eigenstates (`Observable.HasEigenstate`) and evolution of pure states
(`Evolution.evolvePure`) that use these operators are in `AxQM/NC/Ch10/Exercise10_48.lean`.
The operators are exactly `X₁…X₉` and `Z₁…Z₉` of Figure 10.11.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-! ### Sign-composing `mapL` combinators

The workhorses: `a₁ b₁ : S.space →L S.space` and `a₂ b₂ : T.space →L T.space` each (anti)commute,
and the tensor `mapL a₁ a₂`, `mapL b₁ b₂` inherits the *product* of the two signs. Each is proved by
supplying the operator arguments to `TensorProduct.mapL_mul` explicitly — this pins the instances to
the actual composite space and sidesteps the typeclass diamond that a bare `rw [mapL_mul]` hits. -/

/-- **commute × commute ⟹ commute.** -/
theorem mapL_comm_of_comm {a₁ b₁ : S.space →L[ℂ] S.space} {a₂ b₂ : T.space →L[ℂ] T.space}
    (h₁ : a₁ * b₁ = b₁ * a₁) (h₂ : a₂ * b₂ = b₂ * a₂) :
    TensorProduct.mapL a₁ a₂ * TensorProduct.mapL b₁ b₂
      = TensorProduct.mapL b₁ b₂ * TensorProduct.mapL a₁ a₂ := by
  rw [← TensorProduct.mapL_mul a₁ b₁ a₂ b₂, h₁, h₂, TensorProduct.mapL_mul b₁ a₁ b₂ a₂]

/-- **anticommute × anticommute ⟹ commute** (the two signs `(−1)(−1)` cancel). -/
theorem mapL_comm_of_anti {a₁ b₁ : S.space →L[ℂ] S.space} {a₂ b₂ : T.space →L[ℂ] T.space}
    (h₁ : a₁ * b₁ = -(b₁ * a₁)) (h₂ : a₂ * b₂ = -(b₂ * a₂)) :
    TensorProduct.mapL a₁ a₂ * TensorProduct.mapL b₁ b₂
      = TensorProduct.mapL b₁ b₂ * TensorProduct.mapL a₁ a₂ := by
  rw [← TensorProduct.mapL_mul a₁ b₁ a₂ b₂, h₁, h₂, TensorProduct.mapL_neg_left,
    TensorProduct.mapL_neg_right, neg_neg, TensorProduct.mapL_mul b₁ a₁ b₂ a₂]

/-- **anticommute (left) × commute (right) ⟹ anticommute** (a single surviving sign). -/
theorem mapL_anticomm_of_anti_comm {a₁ b₁ : S.space →L[ℂ] S.space} {a₂ b₂ : T.space →L[ℂ] T.space}
    (h₁ : a₁ * b₁ = -(b₁ * a₁)) (h₂ : a₂ * b₂ = b₂ * a₂) :
    TensorProduct.mapL a₁ a₂ * TensorProduct.mapL b₁ b₂
      = -(TensorProduct.mapL b₁ b₂ * TensorProduct.mapL a₁ a₂) := by
  rw [← TensorProduct.mapL_mul a₁ b₁ a₂ b₂, h₁, h₂, TensorProduct.mapL_neg_left,
    TensorProduct.mapL_mul b₁ a₁ b₂ a₂]

/-! ### The single-qubit seed: `Z X = −X Z` -/

/-- **`Z X = −X Z`:** the reversed-order companion of the Pauli `X`-`Z` anticommutation
`pauliXObservable_op_anticomm_pauliZObservable_op`. -/
theorem pauliZObservable_op_anticomm_pauliXObservable_op :
    pauliZObservable.op * pauliXObservable.op = -(pauliXObservable.op * pauliZObservable.op) := by
  rw [pauliXObservable_op_anticomm_pauliZObservable_op, neg_neg]

/-! ### Block-level (anti)commutation

The six block relations behind every nine-qubit statement: `X⊗X⊗X` commutes with each block
bit-flip syndrome `Z₁Z₂`, `Z₂Z₃` (an even overlap), `Z⊗Z⊗Z` commutes with them (pure `Z`s), and
`Z⊗Z⊗Z` anticommutes with `X⊗X⊗X` (three overlapping positions, `(−1)^3 = −1`). -/

/-- **`X⊗X⊗X` commutes with `Z₁Z₂`** (`X Z` twice, `X I` once: sign `(−1)^2 = +1`). -/
theorem blockXObservable_op_comm_zzIObservable_op :
    blockXObservable.op * zzIObservable.op = zzIObservable.op * blockXObservable.op := by
  simp only [blockXObservable, zzIObservable, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_anti pauliXObservable_op_anticomm_pauliZObservable_op
    (mapL_anticomm_of_anti_comm pauliXObservable_op_anticomm_pauliZObservable_op
      (Commute.one_right _).eq)

/-- **`X⊗X⊗X` commutes with `Z₂Z₃`** (`X I` once, `X Z` twice: sign `+1`). -/
theorem blockXObservable_op_comm_izzObservable_op :
    blockXObservable.op * izzObservable.op = izzObservable.op * blockXObservable.op := by
  simp only [blockXObservable, izzObservable, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm (Commute.one_right _).eq
    (mapL_comm_of_anti pauliXObservable_op_anticomm_pauliZObservable_op
      pauliXObservable_op_anticomm_pauliZObservable_op)

/-- **`Z⊗Z⊗Z` commutes with `Z₁Z₂`** (all `Z`s commute). -/
theorem blockZGate_op_comm_zzIObservable_op :
    blockZGate.op * zzIObservable.op = zzIObservable.op * blockZGate.op := by
  simp only [blockZGate, zzIObservable, Evolution.tmul_op, Observable.tmul_op, Observable.id_op,
    pauliZGate_op, ← pauliZObservable_op]
  exact mapL_comm_of_comm rfl (mapL_comm_of_comm rfl (Commute.one_right _).eq)

/-- **`Z⊗Z⊗Z` commutes with `Z₂Z₃`** (all `Z`s commute). -/
theorem blockZGate_op_comm_izzObservable_op :
    blockZGate.op * izzObservable.op = izzObservable.op * blockZGate.op := by
  simp only [blockZGate, izzObservable, Evolution.tmul_op, Observable.tmul_op, Observable.id_op,
    pauliZGate_op, ← pauliZObservable_op]
  exact mapL_comm_of_comm (Commute.one_right _).eq (mapL_comm_of_comm rfl rfl)

/-- **`Z⊗Z⊗Z` anticommutes with `X⊗X⊗X`** (`Z X` in all three positions: sign `(−1)^3 = −1`). -/
theorem blockZGate_op_anticomm_blockXObservable_op :
    blockZGate.op * blockXObservable.op = -(blockXObservable.op * blockZGate.op) := by
  simp only [blockXObservable, blockZGate, Observable.tmul_op, Evolution.tmul_op, pauliZGate_op,
    ← pauliZObservable_op]
  exact mapL_anticomm_of_anti_comm pauliZObservable_op_anticomm_pauliXObservable_op
    (mapL_comm_of_anti pauliZObservable_op_anticomm_pauliXObservable_op
      pauliZObservable_op_anticomm_pauliXObservable_op)

/-! ### The logical operators of Figure 10.11 -/

/-- **The Shor logical-`Z` operator `Z̄ = X₁X₂…X₉`** of Figure 10.11: the product of the nine Pauli
`X`s, as `X⊗X⊗X` (`blockXObservable`) on each of the three blocks of `shorReg`. Packaged as an
`Observable` (it is Hermitian), since it acts diagonally on the codewords. -/
noncomputable def shorLogicalZBar : Observable shorReg :=
  blockXObservable.tmul (blockXObservable.tmul blockXObservable)

/-- **The Shor logical-`X` operator `X̄ = Z₁Z₂…Z₉`** of Figure 10.11: the product of the nine Pauli
`Z`s, as the block phase gate `Z⊗Z⊗Z` (`blockZGate`, the Exercise 10.6 recovery operator) on each of
the three blocks of `shorReg`. Packaged as a unitary `Evolution`, since its logical action is a
permutation of the codewords. -/
noncomputable def shorLogicalXBar : Evolution shorReg :=
  blockZGate.tmul (blockZGate.tmul blockZGate)

/-! ### `Z̄ = X₁…X₉` commutes with each of the eight generators

`Z̄` carries `X` on every qubit, so it commutes with a `Z`-type generator (each overlaps it in an
even number of positions) and trivially with an `X`-type generator (`X` commutes with `X`). -/

/-- **`Z̄` commutes with `g₁ = Z₁Z₂`** (`shorZ12`). -/
theorem shorLogicalZBar_op_comm_shorZ12 :
    shorLogicalZBar.op * shorZ12.op = shorZ12.op * shorLogicalZBar.op := by
  simp only [shorLogicalZBar, shorZ12, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm blockXObservable_op_comm_zzIObservable_op
    (mapL_comm_of_comm (Commute.one_right _).eq (Commute.one_right _).eq)

/-- **`Z̄` commutes with `g₂ = Z₂Z₃`** (`shorZ23`). -/
theorem shorLogicalZBar_op_comm_shorZ23 :
    shorLogicalZBar.op * shorZ23.op = shorZ23.op * shorLogicalZBar.op := by
  simp only [shorLogicalZBar, shorZ23, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm blockXObservable_op_comm_izzObservable_op
    (mapL_comm_of_comm (Commute.one_right _).eq (Commute.one_right _).eq)

/-- **`Z̄` commutes with `g₃ = Z₄Z₅`** (`shorZ45`). -/
theorem shorLogicalZBar_op_comm_shorZ45 :
    shorLogicalZBar.op * shorZ45.op = shorZ45.op * shorLogicalZBar.op := by
  simp only [shorLogicalZBar, shorZ45, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm (Commute.one_right _).eq
    (mapL_comm_of_comm blockXObservable_op_comm_zzIObservable_op (Commute.one_right _).eq)

/-- **`Z̄` commutes with `g₄ = Z₅Z₆`** (`shorZ56`). -/
theorem shorLogicalZBar_op_comm_shorZ56 :
    shorLogicalZBar.op * shorZ56.op = shorZ56.op * shorLogicalZBar.op := by
  simp only [shorLogicalZBar, shorZ56, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm (Commute.one_right _).eq
    (mapL_comm_of_comm blockXObservable_op_comm_izzObservable_op (Commute.one_right _).eq)

/-- **`Z̄` commutes with `g₅ = Z₇Z₈`** (`shorZ78`). -/
theorem shorLogicalZBar_op_comm_shorZ78 :
    shorLogicalZBar.op * shorZ78.op = shorZ78.op * shorLogicalZBar.op := by
  simp only [shorLogicalZBar, shorZ78, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm (Commute.one_right _).eq
    (mapL_comm_of_comm (Commute.one_right _).eq blockXObservable_op_comm_zzIObservable_op)

/-- **`Z̄` commutes with `g₆ = Z₈Z₉`** (`shorZ89`). -/
theorem shorLogicalZBar_op_comm_shorZ89 :
    shorLogicalZBar.op * shorZ89.op = shorZ89.op * shorLogicalZBar.op := by
  simp only [shorLogicalZBar, shorZ89, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm (Commute.one_right _).eq
    (mapL_comm_of_comm (Commute.one_right _).eq blockXObservable_op_comm_izzObservable_op)

/-- **`Z̄` commutes with `g₇ = X₁X₂X₃X₄X₅X₆`** (`shorPhaseSyndromeX123456`): `X` commutes with `X`
everywhere. -/
theorem shorLogicalZBar_op_comm_shorPhaseSyndromeX123456 :
    shorLogicalZBar.op * shorPhaseSyndromeX123456.op
      = shorPhaseSyndromeX123456.op * shorLogicalZBar.op := by
  simp only [shorLogicalZBar, shorPhaseSyndromeX123456, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm rfl (mapL_comm_of_comm rfl (Commute.one_right _).eq)

/-- **`Z̄` commutes with `g₈ = X₄X₅X₆X₇X₈X₉`** (`shorPhaseSyndromeX456789`): `X` commutes with `X`
everywhere. -/
theorem shorLogicalZBar_op_comm_shorPhaseSyndromeX456789 :
    shorLogicalZBar.op * shorPhaseSyndromeX456789.op
      = shorPhaseSyndromeX456789.op * shorLogicalZBar.op := by
  simp only [shorLogicalZBar, shorPhaseSyndromeX456789, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm (Commute.one_right _).eq (mapL_comm_of_comm rfl rfl)

/-! ### `X̄ = Z₁…Z₉` commutes with each of the eight generators

`X̄` carries `Z` on every qubit, so it commutes with a `Z`-type generator (pure `Z`s) and with an
`X`-type generator (which overlaps it in six positions — an even number, so the six `Z X` signs
cancel). -/

/-- **`X̄` commutes with `g₁ = Z₁Z₂`** (`shorZ12`). -/
theorem shorLogicalXBar_op_comm_shorZ12 :
    shorLogicalXBar.op * shorZ12.op = shorZ12.op * shorLogicalXBar.op := by
  simp only [shorLogicalXBar, shorZ12, Evolution.tmul_op, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm blockZGate_op_comm_zzIObservable_op
    (mapL_comm_of_comm (Commute.one_right _).eq (Commute.one_right _).eq)

/-- **`X̄` commutes with `g₂ = Z₂Z₃`** (`shorZ23`). -/
theorem shorLogicalXBar_op_comm_shorZ23 :
    shorLogicalXBar.op * shorZ23.op = shorZ23.op * shorLogicalXBar.op := by
  simp only [shorLogicalXBar, shorZ23, Evolution.tmul_op, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm blockZGate_op_comm_izzObservable_op
    (mapL_comm_of_comm (Commute.one_right _).eq (Commute.one_right _).eq)

/-- **`X̄` commutes with `g₃ = Z₄Z₅`** (`shorZ45`). -/
theorem shorLogicalXBar_op_comm_shorZ45 :
    shorLogicalXBar.op * shorZ45.op = shorZ45.op * shorLogicalXBar.op := by
  simp only [shorLogicalXBar, shorZ45, Evolution.tmul_op, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm (Commute.one_right _).eq
    (mapL_comm_of_comm blockZGate_op_comm_zzIObservable_op (Commute.one_right _).eq)

/-- **`X̄` commutes with `g₄ = Z₅Z₆`** (`shorZ56`). -/
theorem shorLogicalXBar_op_comm_shorZ56 :
    shorLogicalXBar.op * shorZ56.op = shorZ56.op * shorLogicalXBar.op := by
  simp only [shorLogicalXBar, shorZ56, Evolution.tmul_op, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm (Commute.one_right _).eq
    (mapL_comm_of_comm blockZGate_op_comm_izzObservable_op (Commute.one_right _).eq)

/-- **`X̄` commutes with `g₅ = Z₇Z₈`** (`shorZ78`). -/
theorem shorLogicalXBar_op_comm_shorZ78 :
    shorLogicalXBar.op * shorZ78.op = shorZ78.op * shorLogicalXBar.op := by
  simp only [shorLogicalXBar, shorZ78, Evolution.tmul_op, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm (Commute.one_right _).eq
    (mapL_comm_of_comm (Commute.one_right _).eq blockZGate_op_comm_zzIObservable_op)

/-- **`X̄` commutes with `g₆ = Z₈Z₉`** (`shorZ89`). -/
theorem shorLogicalXBar_op_comm_shorZ89 :
    shorLogicalXBar.op * shorZ89.op = shorZ89.op * shorLogicalXBar.op := by
  simp only [shorLogicalXBar, shorZ89, Evolution.tmul_op, Observable.tmul_op, Observable.id_op]
  exact mapL_comm_of_comm (Commute.one_right _).eq
    (mapL_comm_of_comm (Commute.one_right _).eq blockZGate_op_comm_izzObservable_op)

/-- **`X̄` commutes with `g₇ = X₁X₂X₃X₄X₅X₆`** (`shorPhaseSyndromeX123456`): the two block
anticommutations `Z⊗Z⊗Z` vs `X⊗X⊗X` recombine to an even, commuting overlap. -/
theorem shorLogicalXBar_op_comm_shorPhaseSyndromeX123456 :
    shorLogicalXBar.op * shorPhaseSyndromeX123456.op
      = shorPhaseSyndromeX123456.op * shorLogicalXBar.op := by
  simp only [shorLogicalXBar, shorPhaseSyndromeX123456, Evolution.tmul_op, Observable.tmul_op,
    Observable.id_op]
  exact mapL_comm_of_anti blockZGate_op_anticomm_blockXObservable_op
    (mapL_anticomm_of_anti_comm blockZGate_op_anticomm_blockXObservable_op (Commute.one_right _).eq)

/-- **`X̄` commutes with `g₈ = X₄X₅X₆X₇X₈X₉`** (`shorPhaseSyndromeX456789`). -/
theorem shorLogicalXBar_op_comm_shorPhaseSyndromeX456789 :
    shorLogicalXBar.op * shorPhaseSyndromeX456789.op
      = shorPhaseSyndromeX456789.op * shorLogicalXBar.op := by
  simp only [shorLogicalXBar, shorPhaseSyndromeX456789, Evolution.tmul_op, Observable.tmul_op,
    Observable.id_op]
  exact mapL_comm_of_comm (Commute.one_right _).eq
    (mapL_comm_of_anti blockZGate_op_anticomm_blockXObservable_op
      blockZGate_op_anticomm_blockXObservable_op)

/-! ### The logical Pauli algebra: `X̄` anticommutes with `Z̄` -/

/-- **`X̄` anticommutes with `Z̄`:** `X̄ Z̄ = −Z̄ X̄`. Every one of the nine qubits carries `Z` in
`X̄` and `X` in `Z̄`, contributing a sign `−1`; the nine signs multiply to `(−1)^9 = −1`. This is
the logical Pauli anticommutation that makes `Z̄, X̄` a genuine logical `Z, X` pair. -/
theorem shorLogicalXBar_op_anticomm_shorLogicalZBar_op :
    shorLogicalXBar.op * shorLogicalZBar.op = -(shorLogicalZBar.op * shorLogicalXBar.op) := by
  simp only [shorLogicalXBar, shorLogicalZBar, Evolution.tmul_op, Observable.tmul_op]
  exact mapL_anticomm_of_anti_comm blockZGate_op_anticomm_blockXObservable_op
    (mapL_comm_of_anti blockZGate_op_anticomm_blockXObservable_op
      blockZGate_op_anticomm_blockXObservable_op)

end AxQM
