/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorCodeBlock
import AxQM.Postulates.API.CnotPauliPropagation
import AxQM.Postulates.API.Teleportation
import AxQM.Postulates.API.EvolutionTensorHom
import AxQM.Postulates.API.RelativePhaseToffoli

/-!
# AxQM.Postulates.API — block-level bit-flip gates and their action on the cat state

Gates and results for the **bit-flip (`X`) errors** on one three-qubit cat block
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)` carrying the cat vector
`catBlockVec σ = |000⟩ + (−1)^σ |111⟩` (`AxQM/Postulates/API/ShorCodeBlock.lean`). It is the
`X`-analogue of the phase-flip file `AxQM/Postulates/API/ShorCodePhaseFlip.lean`
(`blockPhaseFlip`, `blockZGate`), and supplies the operator identities used in
`AxQM/NC/Ch10/Exercise10_69.lean` (Nielsen & Chuang, Exercise 10.69, fault-tolerant cat-state
measurement, §10.6.3).

* `blockBitFlip i` (`i : Fin 3`) — the bit-flip gate `X` on the `i`-th physical qubit of a block
  (`X ⊗ I ⊗ I`, `I ⊗ X ⊗ I`, `I ⊗ I ⊗ X`): a bit-flip error on one of the block's three qubits, the
  operational (unitary `Evolution`) form of a single `X` error.
* `blockXGate` — the gate `X ⊗ X ⊗ X` on a block: the simultaneous bit-flip of all three qubits, the
  `Evolution` companion of the sign-readout observable `blockXObservable`.
* `thirdQubit i j` — for `i ≠ j` in `Fin 3`, the unique remaining position `k ∉ {i, j}`.
* `pauliXSelect` / `blockBitFlipPattern p` — the bit `a ↦ Xᵃ` selector and the *arbitrary* bit-flip
  pattern gate `X^{p₀} ⊗ X^{p₁} ⊗ X^{p₂}` (flip the qubits with `p i = 1`), modelling an arbitrary
  bit-flip error on the block. `blockBitFlipPattern_add_one` shows complementing the pattern is
  post-composition with `blockXGate`, so a pattern and its complement act identically on the cat —
  the key step of the weight-`≤ 1` statement in `AxQM/NC/Ch10/Exercise10_69.lean`.

The structural facts, all proved on the block's cat vectors:

* `blockBitFlip_op_qubitThreeBasis` — a bit flip on qubit `i` flips the `i`-th bit of `|b⟩`
  (`X_i |b⟩ = |b ⊕ eᵢ⟩`); the `Evolution` companion of `blockSinglePauliX_op_qubitThreeBasis`.
* `blockXGate_op_catBlockVec` — **the all-qubit bit flip is the cat's `±1` symmetry:**
  `(X⊗X⊗X)(|000⟩ + (−1)^σ |111⟩) = (−1)^σ (|000⟩ + (−1)^σ |111⟩)`. Flipping all three qubits swaps
  the `|000⟩` and `|111⟩` kets, which is the identity on the `σ = 0` cat vector (eigenvalue `+1`)
  and a sign flip on `σ = 1` (eigenvalue `−1`) — exactly the `blockXObservable` eigenvalue.
* `blockBitFlip_op_op_catBlockVec_zero` — **the crux "two bit flips collapse to one":** on the
  `σ = 0` cat vector `|000⟩ + |111⟩`, a bit flip on two distinct qubits `i ≠ j` equals a single bit
  flip on the third qubit, `Xᵢ Xⱼ (|000⟩+|111⟩) = X_{thirdQubit i j} (|000⟩+|111⟩)`. This is the
  `X⊗X⊗X = 1` symmetry read as `Xᵢ Xⱼ = X_k` on the cat: no matter how a bit-flip fault fans out
  across the block, it never yields two independent `X` errors — the block collapse behind
  Exercise 10.69's "at most one `X` or `Y` error".

Proofs reduce the tensor-gate action to the single-qubit
law `pauliXGate_op_apply_qubitBasis` via `Evolution.tmul_op_tmul` / `Evolution.id_op`, mirroring
`ShorCodePhaseFlip`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-! ### The bit-flip gates on a block -/

/-- **The bit-flip gate `X` on the `i`-th qubit of a block** (`i : Fin 3`), on
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`: `X ⊗ I ⊗ I`, `I ⊗ X ⊗ I`, `I ⊗ I ⊗ X` for `i = 0, 1, 2`.
It models a bit-flip error on one of the block's three physical qubits — the `X`-analogue of the
phase-flip gate `blockPhaseFlip`. -/
def blockBitFlip : Fin 3 → Evolution bitFlipReg
  | 0 => pauliXGate ⊗ ((Evolution.id : Evolution qubit) ⊗ (Evolution.id : Evolution qubit))
  | 1 => (Evolution.id : Evolution qubit) ⊗ (pauliXGate ⊗ (Evolution.id : Evolution qubit))
  | 2 => (Evolution.id : Evolution qubit) ⊗ ((Evolution.id : Evolution qubit) ⊗ pauliXGate)

/-- **The all-qubit bit-flip gate `X ⊗ X ⊗ X`** on a block: the simultaneous bit flip of all three
physical qubits, the `Evolution` companion of the sign-readout observable `blockXObservable`. -/
def blockXGate : Evolution bitFlipReg :=
  pauliXGate ⊗ (pauliXGate ⊗ pauliXGate)

/-- **The third position of a block** `k ∉ {i, j}`, for `i ≠ j` in `Fin 3`. On the diagonal
`i = j` (never used, guarded by `i ≠ j`) it returns `0`. -/
def thirdQubit (i j : Fin 3) : Fin 3 :=
  if i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 then 2
  else if i = 0 ∧ j = 2 ∨ i = 2 ∧ j = 0 then 1 else 0

/-! ### The bit-flip action on the block's computational basis and cat vectors -/

/-- **Bridging lemma for `Evolution.tmul_op_tmul` on the three-qubit register.** Restates the
nested action of a triple product gate on a `qubitThreeBasis`-shaped vector; needed because
`(qubitBasis c1).vec ⊗ₜ[ℂ] (qubitBasis c2).vec` is generically typed at `qubit.space ⊗[ℂ]
qubit.space`, while `Evolution.tmul_op_tmul`'s inner application needs it at the bundled
`(qubit ⊗ qubit).space` — a `QSystem.compose` bundled-vs-generic diamond. The
`let` names the generic-typed value at the bundled type so `show` can cross the diamond; the final
`rfl` then re-crosses it once more, since the rewritten RHS is `b12`-expressed. -/
private theorem qubitThree_tmul_op (U V W : Evolution qubit) (c0 c1 c2 : Fin 2) :
    (U ⊗ (V ⊗ W)).op
        ((qubitBasis c0).vec ⊗ₜ[ℂ] ((qubitBasis c1).vec ⊗ₜ[ℂ] (qubitBasis c2).vec))
      = U.op (qubitBasis c0).vec ⊗ₜ[ℂ] (V.op (qubitBasis c1).vec ⊗ₜ[ℂ] W.op (qubitBasis
          c2).vec) := by
  let b12 : (qubit ⊗ qubit).space := (qubitBasis c1).vec ⊗ₜ[ℂ] (qubitBasis c2).vec
  change (U ⊗ (V ⊗ W)).op ((qubitBasis c0).vec ⊗ₜ[ℂ] b12) = _
  rw [Evolution.tmul_op_tmul, Evolution.tmul_op_tmul]
  rfl

/-- **A bit flip on qubit `i` flips the `i`-th bit of a computational basis ket:**
`Xᵢ |b⟩ = |b ⊕ eᵢ⟩ = |qubitThreeFlip i b⟩`, for every `i : Fin 3` and index
`b : Fin 2 × Fin 2 × Fin 2`. The `Evolution` companion of `blockSinglePauliX_op_qubitThreeBasis`;
each factor is the identity except the `i`-th, where `pauliXGate_op_apply_qubitBasis` flips the
qubit. -/
theorem blockBitFlip_op_qubitThreeBasis (i : Fin 3) (b : Fin 2 × Fin 2 × Fin 2) :
    (blockBitFlip i).op (qubitThreeBasis b).vec
      = (qubitThreeBasis (qubitThreeFlip i b)).vec := by
  obtain ⟨b0, b1, b2⟩ := b
  fin_cases i <;>
    simp only [blockBitFlip, qubitThreeFlip, qubitThreeBasis, PureState.tmul_vec,
      qubitThree_tmul_op, Evolution.id_op, one_apply_eq_self,
      pauliXGate_op_apply_qubitBasis] <;> rfl

/-- **`X ⊗ X ⊗ X` flips all three bits of a computational basis ket:**
`(X⊗X⊗X)|b₁,b₂,b₃⟩ = |b₁⊕1, b₂⊕1, b₃⊕1⟩`, the `Evolution` companion of
`blockXObservable_op_apply_qubitThreeBasis`. -/
theorem blockXGate_op_qubitThreeBasis (b : Fin 2 × Fin 2 × Fin 2) :
    blockXGate.op (qubitThreeBasis b).vec
      = (qubitThreeBasis (b.1 + 1, b.2.1 + 1, b.2.2 + 1)).vec := by
  obtain ⟨b0, b1, b2⟩ := b
  simp only [blockXGate, qubitThreeBasis, PureState.tmul_vec, qubitThree_tmul_op,
    pauliXGate_op_apply_qubitBasis]
  rfl

/-- **The all-qubit bit flip is the cat's `±1` symmetry:**
`(X⊗X⊗X)(|000⟩ + (−1)^σ |111⟩) = (−1)^σ (|000⟩ + (−1)^σ |111⟩)`. Flipping all three qubits swaps
`|000⟩ ↔ |111⟩`, which fixes the `σ = 0` cat vector and negates the `σ = 1` one — the same `(−1)^σ`
the observable `blockXObservable` reads off. Hence a bit flip on *all three* qubits is not an error
on the (`σ = 0`) cat ancilla; a triple of `X` errors collapses to none. -/
theorem blockXGate_op_catBlockVec (σ : Fin 2) :
    blockXGate.op (catBlockVec σ) = (-1 : ℂ) ^ (σ : ℕ) • catBlockVec σ := by
  have h0 : blockXGate.op (qubitThreeBasis (0, 0, 0)).vec = (qubitThreeBasis (1, 1, 1)).vec := by
    simpa using blockXGate_op_qubitThreeBasis (0, 0, 0)
  have h1 : blockXGate.op (qubitThreeBasis (1, 1, 1)).vec = (qubitThreeBasis (0, 0, 0)).vec := by
    simpa using blockXGate_op_qubitThreeBasis (1, 1, 1)
  simp only [catBlockVec, map_add, map_smul, h0, h1]
  fin_cases σ <;> module

/-- **Two bit flips collapse to one on the cat ancilla (the crux of Exercise 10.69).** On the
`σ = 0` cat vector `|000⟩ + |111⟩`, a bit flip on two *distinct* qubits `i ≠ j` acts exactly as a
single bit flip on the remaining qubit `thirdQubit i j`:
`Xᵢ Xⱼ (|000⟩+|111⟩) = X_{thirdQubit i j} (|000⟩+|111⟩)`. This is the `X⊗X⊗X = 1` symmetry
(`blockXGate_op_catBlockVec` at `σ = 0`) read as `Xᵢ Xⱼ = X_k` on the cat: however a bit-flip fault
fans out over the block, its effect on the cat state is never two independent `X` errors, but at
most one. Verified by flipping the two active bits of the two kets `|000⟩`, `|111⟩` and matching the
result to the single third-qubit flip (a reordering of the same two kets). -/
theorem blockBitFlip_op_op_catBlockVec_zero (i j : Fin 3) (h : i ≠ j) :
    (blockBitFlip i).op ((blockBitFlip j).op (catBlockVec 0))
      = (blockBitFlip (thirdQubit i j)).op (catBlockVec 0) := by
  simp only [catBlockVec, Fin.val_zero, pow_zero, one_smul, map_add,
    blockBitFlip_op_qubitThreeBasis]
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl h
      | (simp [thirdQubit, qubitThreeFlip]; abel)

/-! ### Arbitrary bit-flip patterns and the weight-collapse symmetry

A single fault, propagated to the ancilla output, leaves a bit-flip on some *set* of qubits — an
arbitrary pattern `p : Fin 3 → Fin 2` (`p i = 1` ↦ flip qubit `i`). The gate `blockBitFlipPattern p`
realises it, and the key fact is that flipping `p` and flipping its complement `p + 1` (all bits
toggled) act *identically* on the `+` cat ancilla, because the difference is the trivial symmetry
`X ⊗ X ⊗ X = blockXGate` (`blockXGate_op_catBlockVec` at `σ = 0`). This is the key step of the
weight-`≤ 1` statement in `AxQM/NC/Ch10/Exercise10_69.lean`. -/

/-- **The single-qubit bit-flip selected by a bit** `a : Fin 2`: `X⁰ = 1` (no flip) for `a = 0`,
`X¹ = X` (flip) for `a = 1`. The per-qubit ingredient of a bit-flip *pattern*. -/
def pauliXSelect : Fin 2 → Evolution qubit
  | 0 => Evolution.id
  | 1 => pauliXGate

/-- **Toggling the selector bit is post-composition with `X`:** `X^{a+1} = X^a · X`. For `a = 0`,
`X¹ = 1 · X`; for `a = 1`, `X⁰ = X · X = 1` (`pauliXGate_comp_pauliXGate`, the `X` involution). -/
theorem pauliXSelect_add_one (a : Fin 2) :
    pauliXSelect (a + 1) = (pauliXSelect a).comp pauliXGate := by
  fin_cases a <;> simp [pauliXSelect, Evolution.id_comp, pauliXGate_comp_pauliXGate]

/-- **`Xᵃ` acts on a computational basis ket by `d ↦ d + a`:** `(pauliXSelect a)|d⟩ = |d + a⟩`. For
`a = 0` it is the identity, for `a = 1` the flip `pauliXGate_evolvePure_qubitBasis`. The
`evolvePure` companion of `pauliXSelect`'s action. -/
theorem pauliXSelect_evolvePure_qubitBasis (a d : Fin 2) :
    (pauliXSelect a).evolvePure (qubitBasis d) = qubitBasis (d + a) := by
  fin_cases a <;>
    simp [pauliXSelect, Evolution.id_evolvePure, pauliXGate_evolvePure_qubitBasis]

/-- **A bit-flip pattern gate on a block:** `X^{p₀} ⊗ X^{p₁} ⊗ X^{p₂}` on
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`, flipping exactly the qubits `i` with `p i = 1`. It models an
arbitrary bit-flip error on the block — the shape of the residue any single fault leaves after
propagating to the ancilla output. -/
def blockBitFlipPattern (p : Fin 3 → Fin 2) : Evolution bitFlipReg :=
  pauliXSelect (p 0) ⊗ (pauliXSelect (p 1) ⊗ pauliXSelect (p 2))

/-- **A bit-flip pattern gate flips each bit of a computational basis ket:**
`X^{p}|q₀ q₁ q₂⟩ = |q₀ + p₀, q₁ + p₁, q₂ + p₂⟩`. Factorwise `pauliXSelect_evolvePure_qubitBasis`
through the product structure of `blockBitFlipPattern`. The `evolvePure` companion of the
operator lemma `blockBitFlipPattern_op_qubitThreeBasis` (`ShorCatVerification`). -/
theorem blockBitFlipPattern_evolvePure_tmul (p : Fin 3 → Fin 2) (q0 q1 q2 : Fin 2) :
    (blockBitFlipPattern p).evolvePure (qubitBasis q0 ⊗ (qubitBasis q1 ⊗ qubitBasis q2))
      = qubitBasis (q0 + p 0) ⊗ (qubitBasis (q1 + p 1) ⊗ qubitBasis (q2 + p 2)) := by
  simp only [blockBitFlipPattern, Evolution.tmul_evolvePure, pauliXSelect_evolvePure_qubitBasis]

/-- **Complementing a bit-flip pattern is post-composition with `X ⊗ X ⊗ X`:**
`blockBitFlipPattern (p + 1) = blockBitFlipPattern p · blockXGate`, where `p + 1` toggles every bit.
Factorwise this is `pauliXSelect_add_one`, assembled with `Evolution.tmul_comp`. Since `blockXGate`
fixes the `+` cat ancilla, a pattern and its complement act identically there — the reason bit-flip
errors are counted only up to complementation. -/
theorem blockBitFlipPattern_add_one (p : Fin 3 → Fin 2) :
    blockBitFlipPattern (fun i => p i + 1) = (blockBitFlipPattern p).comp blockXGate := by
  simp only [blockBitFlipPattern, blockXGate, Evolution.tmul_comp, pauliXSelect_add_one]

/-- **`blockBitFlip f` is the weight-one bit-flip pattern `X^{eᶠ}`.** A single `X` error on qubit
`f` is the pattern gate for the indicator `eᶠ = Pi.single f 1` (flip only qubit `f`); the bridge
from the single-error gate `blockBitFlip` to the pattern language of `blockBitFlipPattern`. Verified
on the computational basis (`threeQubit_evolution_ext`). -/
theorem blockBitFlip_eq_blockBitFlipPattern (f : Fin 3) :
    blockBitFlip f = blockBitFlipPattern (Pi.single f 1) := by
  apply threeQubit_evolution_ext
  intro q0 q1 q2
  rw [blockBitFlipPattern_evolvePure_tmul]
  fin_cases f <;>
    simp [blockBitFlip, Evolution.tmul_evolvePure, Evolution.id_evolvePure,
      pauliXGate_evolvePure_qubitBasis]

end AxQM
