/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorCodeProjector

/-!
# AxQM.Postulates.API — single-qubit Pauli errors on the nine-qubit Shor register

Infrastructure for the **error set** of Nielsen & Chuang's Exercise 10.10: the
identity `I` together with the single-qubit Pauli errors `X_j, Y_j, Z_j` for `j = 1..9` on the
nine-qubit Shor register `shorReg = bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)`. This file builds those
errors and computes how a single-qubit Pauli acts on one three-qubit cat block — the per-block
building blocks from which the error-vector inner products (and hence the quantum error-correction
conditions, Theorem 10.1) are assembled.

A physical qubit of the code is addressed by a pair `(block, pos) ∈ Fin 3 × Fin 3`: `block` selects
one of the three cat blocks `(q₁q₂q₃)(q₄q₅q₆)(q₇q₈q₉)`, `pos` selects one of the three qubits inside
it. `X_j`, `Y_j`, `Z_j` (`j = 3·block + pos + 1`) is the corresponding single-qubit Pauli placed at
that qubit and the identity elsewhere.

## Contents

* `blockSinglePauli A pos` / `shorSinglePauli A block pos` — a single-qubit observable `A` placed at
  position `pos` inside a block, and at qubit `(block, pos)` of the whole register, via nested
  `Observable.tmul` with `Observable.id` on the untouched factors.
* `pauliErrorObs` (`0 ↦ X`, `1 ↦ Y`, `2 ↦ Z`) and `shorPauliError t block pos` — the single-qubit
  Pauli error **operators** `{X_j, Y_j, Z_j}`; `shorPauliError_isSelfAdjoint` records that each is
  Hermitian (`E† = E`), as Pauli errors are.
* `blockSinglePauliX_op_qubitThreeBasis` / `..Y..` / `..Z..` — the action of a single-qubit Pauli on
  a computational-basis ket of a block: `X`/`Y` flip the bit at `pos` (with `Y` picking up
  `i·(-1)ᵇ`), `Z` multiplies by `(-1)ᵇ`. They reuse the shared index combinators `qubitThreeFlip` /
  `qubitThreeCoord` (`QubitThree.lean`), and are the reusable atoms every block-level overlap
  reduces to.
* The **block cat-state action** (the per-block inner-product building blocks; the cat-vector norm
  `√2`, `catBlockVec_norm`, lives beside `catBlockVec` in `ShorCodeBlock.lean`):
  * `blockSinglePauliZ_op_catBlockVec` / `blockSinglePauliZ_op_catBlockState` — a `Z` at **any**
    position of a block **flips the block sign**, `Z c_s = c_{s+1}` (`Z` is position-independent on
    a cat block: this is the code's degeneracy — `Z₁, Z₂, Z₃` act identically).
  * `catBlockVec_inner_blockSinglePauliX` / `..Y..` and their `catBlockState` versions — an `X` or
    `Y` at any position sends a cat state **out of the two-dimensional cat span**
    `span{c₀, c₁}`: `⟪c_{s'}, X c_s⟫ = 0 = ⟪c_{s'}, Y c_s⟫` (`X`/`Y` land on weight-`1`/`2` kets,
    orthogonal to the weight-`0`/`3` kets `|000⟩, |111⟩` making up a cat vector).

This extends the code projector of `ShorCodeProjector.lean`; the quantum error-correction
conditions are in `QuantumErrorCorrection.lean`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-! ### Placing a single-qubit Pauli at a qubit of the register -/

/-- **A single-qubit observable `A` placed at position `pos` of a three-qubit block**
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`: `A` on the `pos`-th qubit, the identity on the other two.
`pos = 0 ↦ A ⊗ I ⊗ I`, `pos = 1 ↦ I ⊗ A ⊗ I`, `pos = 2 ↦ I ⊗ I ⊗ A`. -/
def blockSinglePauli (A : Observable qubit) (pos : Fin 3) : Observable bitFlipReg :=
  match pos with
  | 0 => A ⊗ (Observable.id qubit ⊗ Observable.id qubit)
  | 1 => Observable.id qubit ⊗ (A ⊗ Observable.id qubit)
  | 2 => Observable.id qubit ⊗ (Observable.id qubit ⊗ A)

/-- **A single-qubit observable `A` placed at qubit `(block, pos)` of the nine-qubit register**
`shorReg = bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)`: `blockSinglePauli A pos` on the `block`-th cat
block, the identity on the other two blocks. -/
def shorSinglePauli (A : Observable qubit) (block pos : Fin 3) : Observable shorReg :=
  match block with
  | 0 => blockSinglePauli A pos ⊗ (Observable.id bitFlipReg ⊗ Observable.id bitFlipReg)
  | 1 => Observable.id bitFlipReg ⊗ (blockSinglePauli A pos ⊗ Observable.id bitFlipReg)
  | 2 => Observable.id bitFlipReg ⊗ (Observable.id bitFlipReg ⊗ blockSinglePauli A pos)

/-- **The three single-qubit Pauli error observables indexed by `Fin 3`:** `0 ↦ X`, `1 ↦ Y`,
`2 ↦ Z`. The three non-identity single-qubit errors, used to enumerate the Shor error family
`{X_j, Y_j, Z_j}`. (Distinct from `pauliObservable : (Fin 3 → ℝ) → Observable qubit`, the
Bloch-vector observable `n·σ`; this is the discrete `{X, Y, Z}` selector.) -/
def pauliErrorObs : Fin 3 → Observable qubit :=
  ![pauliXObservable, pauliYObservable, pauliZObservable]

/-- **The single-qubit Pauli error operators** `{X_j, Y_j, Z_j}` of the Shor code, as operators on
the register state space: `shorPauliError t block pos` is the Pauli of type `t` (`0 = X`, `1 = Y`,
`2 = Z`) acting on qubit `(block, pos)`, the identity elsewhere — the operation elements the quantum
error-correction conditions (Theorem 10.1, Exercise 10.10) are checked against. -/
def shorPauliError (t block pos : Fin 3) : shorReg.space →L[ℂ] shorReg.space :=
  (shorSinglePauli (pauliErrorObs t) block pos).op

/-- **Each Pauli error is self-adjoint** (`E† = E`): a Pauli is Hermitian, and a tensor of Hermitian
operators (`X`/`Y`/`Z` and identities) is Hermitian. This is the `E† = E` used to read the
Knill–Laflamme conditions `P Eᵢ† Eⱼ P = αᵢⱼ P` as overlaps of error images `⟪Eᵢ ψ, Eⱼ ψ⟫`. -/
theorem shorPauliError_isSelfAdjoint (t block pos : Fin 3) :
    IsSelfAdjoint (shorPauliError t block pos) :=
  (shorSinglePauli (pauliErrorObs t) block pos).selfAdjoint

/-! ### The action of a single-qubit Pauli on a computational-basis ket of a block

The index combinators `qubitThreeFlip` (flip the bit at `pos`) and `qubitThreeCoord` (read the bit
at `pos`) are the shared three-qubit index maps from `QubitThree.lean`. -/

/-- **`X` at position `pos` flips the bit at `pos`:** `X_pos |b⟩ = |b ⊕ e_pos⟩`. Each factor is the
identity except the `pos`-th, where `pauliXObservable_op_apply_qubitBasis` flips the qubit. -/
theorem blockSinglePauliX_op_qubitThreeBasis (pos : Fin 3) (b : Fin 2 × Fin 2 × Fin 2) :
    (blockSinglePauli pauliXObservable pos).op (qubitThreeBasis b).vec
      = (qubitThreeBasis (qubitThreeFlip pos b)).vec := by
  obtain ⟨b1, b2, b3⟩ := b
  fin_cases pos <;>
    simp only [blockSinglePauli, qubitThreeFlip, qubitThreeBasis, PureState.tmul_vec]
  all_goals erw [Observable.tmul_op_tmul, Observable.tmul_op_tmul]
  all_goals simp only [Observable.id_op, one_apply_eq_self]
  all_goals erw [pauliXObservable_op_apply_qubitBasis]

/-- **`Z` at position `pos` multiplies by `(-1)` on that bit:** `Z_pos |b⟩ = (-1)^{b_pos} |b⟩`. Each
factor is the identity except the `pos`-th, where `pauliZObservable_op_apply_qubitBasis` gives the
sign; the sign is pulled out of the tensor with the position-explicit `Concrete` scalar lemmas. -/
theorem blockSinglePauliZ_op_qubitThreeBasis (pos : Fin 3) (b : Fin 2 × Fin 2 × Fin 2) :
    (blockSinglePauli pauliZObservable pos).op (qubitThreeBasis b).vec
      = (-1 : ℂ) ^ (qubitThreeCoord pos b : ℕ) • (qubitThreeBasis b).vec := by
  obtain ⟨b1, b2, b3⟩ := b
  fin_cases pos <;>
    simp only [blockSinglePauli, qubitThreeCoord, qubitThreeBasis, PureState.tmul_vec]
  all_goals erw [Observable.tmul_op_tmul, Observable.tmul_op_tmul]
  all_goals simp only [Observable.id_op, one_apply_eq_self]
  all_goals erw [pauliZObservable_op_apply_qubitBasis]
  all_goals first
    | exact Concrete.smul_tmul_tmul _ _ _ _
    | exact Concrete.tmul_smul_tmul _ _ _ _
    | exact Concrete.tmul_tmul_smul _ _ _ _

/-- **`Y` at position `pos` flips the bit at `pos` with a phase:** `Y_pos |b⟩ =
i·(-1)^{b_pos} |b ⊕ e_pos⟩`. Each factor is the identity except the `pos`-th, where
`pauliYObservable_op_apply_qubitBasis` flips the qubit and supplies the phase; the phase is pulled
out of the tensor with the position-explicit `Concrete` scalar lemmas. -/
theorem blockSinglePauliY_op_qubitThreeBasis (pos : Fin 3) (b : Fin 2 × Fin 2 × Fin 2) :
    (blockSinglePauli pauliYObservable pos).op (qubitThreeBasis b).vec
      = (Complex.I * (-1) ^ (qubitThreeCoord pos b : ℕ)) •
          (qubitThreeBasis (qubitThreeFlip pos b)).vec := by
  obtain ⟨b1, b2, b3⟩ := b
  fin_cases pos <;>
    simp only [blockSinglePauli, qubitThreeCoord, qubitThreeFlip, qubitThreeBasis,
      PureState.tmul_vec]
  all_goals erw [Observable.tmul_op_tmul, Observable.tmul_op_tmul]
  all_goals simp only [Observable.id_op, one_apply_eq_self]
  all_goals erw [pauliYObservable_op_apply_qubitBasis]
  all_goals first
    | exact Concrete.smul_tmul_tmul _ _ _ _
    | exact Concrete.tmul_smul_tmul _ _ _ _
    | exact Concrete.tmul_tmul_smul _ _ _ _

/-! ### The block cat-state action of a single-qubit Pauli

The three facts the error-vector overlaps of Exercise 10.10 rest on: a `Z` flips the cat sign
(position-independently — the Shor code's degeneracy), while an `X` or `Y` maps a cat state out of
the two-dimensional cat span. -/

/-- **`Z` at any position flips the cat sign** (unnormalised): `Z_pos (|000⟩ + (-1)^s|111⟩) =
|000⟩ + (-1)^{s+1}|111⟩`, i.e. `Z_pos c_s = c_{s+1}`. `Z` reads `+1` on `|000⟩` (all bits `0`) and
`-1` on `|111⟩` (all bits `1`), whichever position it sits at — so `Z₁, Z₂, Z₃` all act identically
on a block, the degeneracy that makes the Shor code's error matrix `α` non-diagonal. -/
theorem blockSinglePauliZ_op_catBlockVec (pos : Fin 3) (s : Fin 2) :
    (blockSinglePauli pauliZObservable pos).op (catBlockVec s) = catBlockVec (s + 1) := by
  rw [catBlockVec, map_add, map_smul, blockSinglePauliZ_op_qubitThreeBasis,
    blockSinglePauliZ_op_qubitThreeBasis, catBlockVec]
  fin_cases pos <;> fin_cases s <;> simp [qubitThreeCoord]

/-- **`Z` at any position flips the cat sign** (normalised): `Z_pos c_s = c_{s+1}` on the block cat
states `catBlockState`. Transported from the unnormalised `blockSinglePauliZ_op_catBlockVec` through
the common norm `√2` (`catBlockVec_norm`), which the two cat states share so the normalisation
scalar is unchanged. -/
theorem blockSinglePauliZ_op_catBlockState (pos : Fin 3) (s : Fin 2) :
    (blockSinglePauli pauliZObservable pos).op (catBlockState s).vec
      = (catBlockState (s + 1)).vec := by
  simp only [catBlockState, PureState.normalize_vec, map_smul, blockSinglePauliZ_op_catBlockVec,
    catBlockVec_norm]

/-- **`X` at any position maps a cat state out of the cat span** (unnormalised):
`⟪c_{s'}, X_pos c_s⟫ = 0`. `X_pos` flips a bit, sending the weight-`0`/`3` kets `|000⟩, |111⟩` of a
cat vector to weight-`1`/`2` kets, orthogonal to the `|000⟩, |111⟩` making up `c_{s'}`. -/
theorem catBlockVec_inner_blockSinglePauliX (pos : Fin 3) (s s' : Fin 2) :
    (inner ℂ (catBlockVec s') ((blockSinglePauli pauliXObservable pos).op (catBlockVec s)) : ℂ)
      = 0 := by
  simp only [catBlockVec, map_add, map_smul, blockSinglePauliX_op_qubitThreeBasis]
  have h := orthonormal_iff_ite.mp qubitThreeBasis_orthonormal
  fin_cases pos <;>
    simp only [qubitThreeFlip, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      h] <;>
    norm_num [Prod.ext_iff]

/-- **`Y` at any position maps a cat state out of the cat span** (unnormalised):
`⟪c_{s'}, Y_pos c_s⟫ = 0`. Like `X`, `Y_pos` flips a bit (up to a phase), sending `|000⟩, |111⟩` to
weight-`1`/`2` kets orthogonal to the `|000⟩, |111⟩` making up `c_{s'}`. -/
theorem catBlockVec_inner_blockSinglePauliY (pos : Fin 3) (s s' : Fin 2) :
    (inner ℂ (catBlockVec s') ((blockSinglePauli pauliYObservable pos).op (catBlockVec s)) : ℂ)
      = 0 := by
  simp only [catBlockVec, map_add, map_smul, blockSinglePauliY_op_qubitThreeBasis]
  have h := orthonormal_iff_ite.mp qubitThreeBasis_orthonormal
  fin_cases pos <;>
    simp only [qubitThreeCoord, qubitThreeFlip, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, h] <;>
    norm_num [Prod.ext_iff]

/-- **`X` at any position maps a cat state out of the cat span** (normalised):
`⟪c_{s'}, X_pos c_s⟫ = 0` on the block cat states `catBlockState`. Transported from the unnormalised
`catBlockVec_inner_blockSinglePauliX`: the normalisation scalars multiply a zero overlap. -/
theorem catBlockState_inner_blockSinglePauliX (pos : Fin 3) (s s' : Fin 2) :
    (inner ℂ (catBlockState s').vec
        ((blockSinglePauli pauliXObservable pos).op (catBlockState s).vec) : ℂ) = 0 := by
  simp only [catBlockState, PureState.normalize_vec, map_smul, inner_smul_left, inner_smul_right,
    catBlockVec_inner_blockSinglePauliX, mul_zero]

/-- **`Y` at any position maps a cat state out of the cat span** (normalised):
`⟪c_{s'}, Y_pos c_s⟫ = 0` on the block cat states `catBlockState`. Transported from the unnormalised
`catBlockVec_inner_blockSinglePauliY`: the normalisation scalars multiply a zero overlap. -/
theorem catBlockState_inner_blockSinglePauliY (pos : Fin 3) (s s' : Fin 2) :
    (inner ℂ (catBlockState s').vec
        ((blockSinglePauli pauliYObservable pos).op (catBlockState s).vec) : ℂ) = 0 := by
  simp only [catBlockState, PureState.normalize_vec, map_smul, inner_smul_left, inner_smul_right,
    catBlockVec_inner_blockSinglePauliY, mul_zero]

end AxQM
