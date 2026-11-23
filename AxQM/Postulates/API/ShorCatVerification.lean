/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorCodeBitFlip

/-!
# AxQM.Postulates.API — verifying the cat ancilla by parity checks

Results for the **verification** stage of the fault-tolerant cat-state
measurement (Nielsen & Chuang §10.6.3, Exercise 10.69). After the (non-fault-tolerant) preparation
of the cat ancilla `catBlockVec 0 = |000⟩ + |111⟩`, N&C **verify** it by measuring the parity
observables `ZᵢZⱼ`: a genuine cat has *even* parity on every pair of qubits, so a `−1` outcome on
any pair reveals a bit-flip error and the ancilla is discarded. On the three-qubit register
`bitFlipReg` the adjacent parities `Z₁Z₂ = zzIObservable` and `Z₂Z₃ = izzObservable`
(`AxQM/Postulates/API/BitFlipSyndromeMeasurement.lean`) generate all of them.

This file computes how the parity checks act on a cat carrying an **arbitrary bit-flip pattern**
`blockBitFlipPattern p` (`AxQM/Postulates/API/ShorCodeBitFlip.lean`), the residue a single fault
leaves after propagating through the preparation CNOTs:

* `pauliXSelect_op_apply_qubitBasis` / `blockBitFlipPattern_op_qubitThreeBasis` — the per-qubit and
  whole-register bit-flip action on the computational basis: `X^{p} |b⟩ = |b ⊕ p⟩`.
* `zzIObservable_op_blockBitFlipPattern_catBlockVec` — **the `Z₁Z₂` syndrome of a patterned cat:**
  the errored cat `X^{p}(|000⟩+|111⟩)` is an eigenvector of `Z₁Z₂` with eigenvalue
  `(−1)^{p₀}(−1)^{p₁}` — `+1` iff `p₀ = p₁`, else `−1`. (The two kets `|p⟩` and `|p̄⟩` of the
  errored cat carry the *same* `Z₁Z₂` sign, because complementing all three bits changes `p₀+p₁`
  by an even amount.)
* `izzObservable_op_blockBitFlipPattern_catBlockVec` — likewise for `Z₂Z₃`, eigenvalue
  `(−1)^{p₁}(−1)^{p₂}`, `+1` iff `p₁ = p₂`.

Hence the patterned cat passes **both** checks iff `p₀ = p₁` and `p₁ = p₂`, i.e. iff `p` is
*constant* (`000` or `111`) — and a constant pattern acts trivially on the cat (`000` is the
identity, `111 = X⊗X⊗X` is the cat's symmetry `blockXGate_op_catBlockVec`). Every *non*-constant
bit-flip residue has odd parity across some adjacent pair and is therefore **rejected** by
verification. This is the algebraic heart of Exercise 10.69's **detection** step: in general it is
verification — not merely the `X⊗X⊗X` symmetry — that removes the multi-qubit bit-flip residues a
preparation fault can produce (on the figure's three qubits the two happen to coincide; the general
register where they diverge is treated in `AxQM/Postulates/API/CatVerification.lean`, and the
assembled error-count bound in `AxQM/NC/Ch10/Exercise10_69.lean`). The statements built from these
facts are in `AxQM/NC/Ch10/Exercise10_69.lean`.

These results combine the bit-flip gates (`ShorCodeBitFlip`) and the syndrome observables
(`BitFlipSyndromeMeasurement`).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-! ### The bit-flip pattern's action on the computational basis -/

/-- **The single-qubit selector flips a basis ket:** `X^{a} |b⟩ = |b ⊕ a⟩`, i.e.
`(pauliXSelect a).op |b⟩ = |b + a⟩`. For `a = 0` it is the identity (`b + 0 = b`); for `a = 1` it is
the Pauli `X` (`pauliXGate_op_apply_qubitBasis`, `|b⟩ ↦ |b+1⟩`). -/
theorem pauliXSelect_op_apply_qubitBasis (a b : Fin 2) :
    (pauliXSelect a).op (qubitBasis b).vec = (qubitBasis (b + a)).vec := by
  fin_cases a
  · simp [pauliXSelect, Evolution.id_op]
    rfl
  · simpa [pauliXSelect] using pauliXGate_op_apply_qubitBasis b

/-- **A bit-flip pattern flips the corresponding bits of a computational basis ket:**
`X^{p} |b₀b₁b₂⟩ = |b₀⊕p₀, b₁⊕p₁, b₂⊕p₂⟩`. Each of the three tensor factors flips its qubit by
`pauliXSelect_op_apply_qubitBasis`; the whole-register companion of
`blockBitFlip_op_qubitThreeBasis` for a general pattern. -/
theorem blockBitFlipPattern_op_qubitThreeBasis (p : Fin 3 → Fin 2)
    (b : Fin 2 × Fin 2 × Fin 2) :
    (blockBitFlipPattern p).op (qubitThreeBasis b).vec
      = (qubitThreeBasis (b.1 + p 0, b.2.1 + p 1, b.2.2 + p 2)).vec := by
  obtain ⟨b0, b1, b2⟩ := b
  simp only [blockBitFlipPattern, qubitThreeBasis, PureState.tmul_vec]
  erw [Evolution.tmul_op_tmul, Evolution.tmul_op_tmul]
  rw [pauliXSelect_op_apply_qubitBasis, pauliXSelect_op_apply_qubitBasis,
    pauliXSelect_op_apply_qubitBasis]

/-! ### Parity syndromes of a patterned cat ancilla

The sign identity behind both syndromes: complementing a `Fin 2` bit negates its `(−1)`-power, so
the two kets `|p⟩`, `|p̄⟩` of the errored cat carry the same adjacent-pair parity. -/

/-- **Complementing a bit negates its sign:** `(−1)^{(1+x)} = −(−1)^{x}` (as a `Fin 2 → ℂ`-power).
The elementary fact that flipping a qubit toggles its `Z`-eigenvalue, used to match the `Z`-parity
signs of the two kets `|p⟩` and `|p̄⟩` of an errored cat. -/
theorem neg_one_pow_succ_fin_two (x : Fin 2) :
    (-1 : ℂ) ^ (((1 + x : Fin 2)) : ℕ) = -((-1 : ℂ) ^ ((x : ℕ))) := by
  fin_cases x <;> simp

/-- **The `Z₁Z₂` syndrome of a patterned cat ancilla.** The errored cat
`X^{p}(|000⟩ + |111⟩) = |p⟩ + |p̄⟩` is an eigenvector of the parity observable
`Z₁Z₂ = zzIObservable` with eigenvalue `(−1)^{p₀}(−1)^{p₁}`. Both kets carry this same sign —
`|p̄⟩` differs from `|p⟩` by
complementing every bit, which changes `p₀ + p₁` by `2` (`neg_one_pow_succ_fin_two` twice, the two
minus signs cancelling). The eigenvalue is `+1` exactly when `p₀ = p₁`; a `p₀ ≠ p₁` pattern lands in
the `−1` eigenspace, so measuring `Z₁Z₂` rejects it. -/
theorem zzIObservable_op_blockBitFlipPattern_catBlockVec (p : Fin 3 → Fin 2) :
    zzIObservable.op ((blockBitFlipPattern p).op (catBlockVec 0))
      = ((-1 : ℂ) ^ ((p 0 : ℕ)) * (-1 : ℂ) ^ ((p 1 : ℕ)))
          • (blockBitFlipPattern p).op (catBlockVec 0) := by
  rw [catBlockVec]
  simp only [Fin.val_zero, pow_zero, one_smul, map_add, blockBitFlipPattern_op_qubitThreeBasis,
    zero_add, zzI_op_ket]
  rw [neg_one_pow_succ_fin_two (p 0), neg_one_pow_succ_fin_two (p 1), neg_mul_neg]
  module

/-- **The `Z₂Z₃` syndrome of a patterned cat ancilla.** The errored cat `X^{p}(|000⟩ + |111⟩)` is an
eigenvector of `Z₂Z₃ = izzObservable` with eigenvalue `(−1)^{p₁}(−1)^{p₂}` — `+1` iff `p₁ = p₂`.
The `Z₂Z₃` analogue of `zzIObservable_op_blockBitFlipPattern_catBlockVec`. -/
theorem izzObservable_op_blockBitFlipPattern_catBlockVec (p : Fin 3 → Fin 2) :
    izzObservable.op ((blockBitFlipPattern p).op (catBlockVec 0))
      = ((-1 : ℂ) ^ ((p 1 : ℕ)) * (-1 : ℂ) ^ ((p 2 : ℕ)))
          • (blockBitFlipPattern p).op (catBlockVec 0) := by
  rw [catBlockVec]
  simp only [Fin.val_zero, pow_zero, one_smul, map_add, blockBitFlipPattern_op_qubitThreeBasis,
    zero_add, izz_op_ket]
  rw [neg_one_pow_succ_fin_two (p 1), neg_one_pow_succ_fin_two (p 2), neg_mul_neg]
  module

end AxQM
