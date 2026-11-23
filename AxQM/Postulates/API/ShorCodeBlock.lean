/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BitFlipSyndromeMeasurement
import AxQM.Postulates.API.Eigenstate

/-!
# AxQM.Postulates.API — the Shor-code blocks and their sign-readout observable

The three-qubit blocks of the nine-qubit Shor code (Nielsen & Chuang §10.2, Exercise 10.5). The
Shor code is a *concatenation*: each of the three "phase-flip qubits" `|±⟩` is encoded by the
three-qubit bit-flip code into a **block** of three physical qubits, the cat state

* `catBlockVec 0 = |000⟩ + |111⟩`  (the encoding of `|+⟩`),
* `catBlockVec 1 = |000⟩ − |111⟩`  (the encoding of `|−⟩`),

carried by the three-qubit register `bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`. This file develops one
block in isolation — the building block from which the nine-qubit register, its codewords, and the
phase-flip syndrome observables `X₁X₂X₃X₄X₅X₆`, `X₄X₅X₆X₇X₈X₉` are built.

* `catBlockVec σ` / `catBlockState σ` — the unnormalised cat vector `|000⟩ + (−1)^σ |111⟩` and its
  normalised pure state `(|000⟩ + (−1)^σ |111⟩)/√2`, the two sign eigenstates of a block. They are
  **orthonormal** (`catBlockVec_inner`: `⟪c_s, c_{s'}⟫ = 2 δ_{s,s'}`; `catBlockState_inner`:
  `⟪c_s, c_{s'}⟫ = δ_{s,s'}`), the block-level overlaps the nine-qubit codewords are built from.
* `blockXObservable` (`X ⊗ X ⊗ X`) — the **block sign-readout observable**: the product of the three
  Pauli `X`s on the block. It is a self-adjoint involution (`blockXObservable_op_mul_self`), so it
  defines a two-outcome `±1` measurement, and it acts on `catBlockState σ` by the eigenvalue
  `(−1)^σ` (`blockXObservable_hasEigenstate_catBlockState`): its `+1`/`−1` outcome *is* the block's
  `+`/`−` sign. This is the elementary fact behind Exercise 10.5 — comparing the signs of two
  blocks is measuring the product of their `X⊗X⊗X`s, hence `X₁X₂X₃X₄X₅X₆` and `X₄X₅X₆X₇X₈X₉`.

The proofs reduce every operator identity to the computational basis: `X` flips a qubit
(the general `pauliXObservable_op_apply_qubitBasis`, `X|i⟩ = |i⊕1⟩`, defined beside its `Z` sibling
in `AxQM/Postulates/API/Qubit.lean`), so `X⊗X⊗X` flips all three bits of a basis ket
(`blockXObservable_op_apply_qubitThreeBasis`), whence `X⊗X⊗X (|000⟩ ± |111⟩) = ±(|000⟩ ± |111⟩)`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-! ### The block sign-readout observable `X ⊗ X ⊗ X` -/

/-- **`X ⊗ X ⊗ X`**, the block **sign-readout observable** on the three-qubit register
`bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`: the product of the three Pauli `X`s of the block. Its `±1`
eigenvalue on a cat state reads off that block's `+`/`−` sign (`X⊗X⊗X (|000⟩ ± |111⟩) = ±(|000⟩ ±
|111⟩)`), so measuring it compares — for a pair of blocks, via the product `X⊗X⊗X ⊗ X⊗X⊗X` — the
signs of the two blocks. This is the per-block ingredient of the Shor phase-flip syndrome
observables. -/
def blockXObservable : Observable bitFlipReg :=
  pauliXObservable ⊗ (pauliXObservable ⊗ pauliXObservable)

/-- **`X ⊗ X ⊗ X` flips all three bits:** `X⊗X⊗X |b₁b₂b₃⟩ = |b₁⊕1, b₂⊕1, b₃⊕1⟩`. Each factor flips
its qubit via `pauliXObservable_op_apply_qubitBasis`. -/
theorem blockXObservable_op_apply_qubitThreeBasis (b : Fin 2 × Fin 2 × Fin 2) :
    blockXObservable.op (qubitThreeBasis b).vec
      = (qubitThreeBasis (b.1 + 1, b.2.1 + 1, b.2.2 + 1)).vec := by
  simp only [qubitThreeBasis, PureState.tmul_vec, blockXObservable]
  erw [Observable.tmul_op_tmul, Observable.tmul_op_tmul]
  simp only [pauliXObservable_op_apply_qubitBasis]
  rfl

/-- **`X ⊗ X ⊗ X` is a self-adjoint involution:** `(X⊗X⊗X)² = I`. Verified on the computational
basis, where `X⊗X⊗X` flips all three bits, so applying it twice returns each ket to itself. -/
theorem blockXObservable_op_mul_self : blockXObservable.op * blockXObservable.op = 1 := by
  apply qubitThree_op_ext
  intro b
  have h : ∀ x : Fin 2, x + 1 + 1 = x := by decide
  rw [mul_apply_eq_comp, blockXObservable_op_apply_qubitThreeBasis,
    blockXObservable_op_apply_qubitThreeBasis, one_apply_eq_self]
  simp only [h]

/-! ### The block cat states `(|000⟩ ± |111⟩)/√2` -/

/-- The **unnormalised block cat vector** `|000⟩ + (−1)^σ |111⟩` on `bitFlipReg`: `σ = 0` gives
`|000⟩ + |111⟩` (the bit-flip encoding of `|+⟩`) and `σ = 1` gives `|000⟩ − |111⟩` (the encoding of
`|−⟩`). -/
def catBlockVec (σ : Fin 2) : bitFlipReg.space :=
  (qubitThreeBasis (0, 0, 0)).vec + (-1 : ℂ) ^ (σ : ℕ) • (qubitThreeBasis (1, 1, 1)).vec

/-- The cat vector is nonzero: its `|000⟩` component is `1` (from orthonormality of the
computational basis), so it cannot be the zero vector. -/
theorem catBlockVec_ne_zero (σ : Fin 2) : catBlockVec σ ≠ 0 := by
  intro h
  have hi : inner ℂ (qubitThreeBasis (0, 0, 0)).vec (catBlockVec σ) = 0 := by
    rw [h, inner_zero_right]
  rw [catBlockVec, inner_add_right, inner_smul_right,
    orthonormal_iff_ite.mp qubitThreeBasis_orthonormal (0, 0, 0) (0, 0, 0),
    orthonormal_iff_ite.mp qubitThreeBasis_orthonormal (0, 0, 0) (1, 1, 1)] at hi
  simp at hi

/-- **The unnormalised block cat vectors satisfy `⟪c_s, c_{s'}⟫ = 2 δ_{s,s'}`.** Only the
computational-basis kets `|000⟩` and `|111⟩` appear in `catBlockVec = |000⟩ + (−1)^σ |111⟩`, so the
inner product is `1 + (−1)^{s+s'}` by the orthonormality of `qubitThreeBasis`: `2` when `s = s'` and
`0` when `s ≠ s'`. -/
theorem catBlockVec_inner (s s' : Fin 2) :
    (inner ℂ (catBlockVec s) (catBlockVec s') : ℂ) = if s = s' then 2 else 0 := by
  have h := orthonormal_iff_ite.mp qubitThreeBasis_orthonormal
  fin_cases s <;> fin_cases s' <;>
    simp only [catBlockVec, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      h] <;>
    norm_num

/-- **Each cat vector has norm `√2`:** `‖c_s‖ = √2`, since `⟪c_s, c_s⟫ = 2` (`catBlockVec_inner`).
The common normalisation constant of the two block cat states `catBlockState s = c_s / √2`, used to
transport block operator identities from the unnormalised `catBlockVec` to the normalised
`catBlockState`. -/
theorem catBlockVec_norm (s : Fin 2) : ‖catBlockVec s‖ = Real.sqrt 2 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), catBlockVec_inner]
  simp

/-- The **normalised block cat state** `(|000⟩ + (−1)^σ |111⟩)/√2`, the sign-`(−1)^σ` eigenstate of
the block. Built from `catBlockVec σ` through the shared `PureState.normalize` constructor. -/
def catBlockState (σ : Fin 2) : PureState bitFlipReg :=
  PureState.normalize (catBlockVec σ) (catBlockVec_ne_zero σ)

/-- **The normalised block cat states are orthonormal:** `⟪catBlockState s, catBlockState s'⟫ =
δ_{s,s'}`. The diagonal is `1` because a `PureState` is a unit vector (`PureState.inner_self`); the
off-diagonal vanishes because the underlying cat vectors are orthogonal (`catBlockVec_inner`), and a
normalisation scalar times `0` is `0`. -/
theorem catBlockState_inner (s s' : Fin 2) :
    (inner ℂ (catBlockState s).vec (catBlockState s').vec : ℂ) = if s = s' then 1 else 0 := by
  rcases eq_or_ne s s' with h | h
  · subst h; rw [ite_eq_left rfl]; exact PureState.inner_self _
  · rw [ite_eq_right h, catBlockState, catBlockState, PureState.normalize_vec,
        PureState.normalize_vec,
      inner_smul_left, inner_smul_right, catBlockVec_inner, ite_eq_right h, mul_zero, mul_zero]

/-- **`X ⊗ X ⊗ X` reads the block sign:** `X⊗X⊗X (|000⟩ + (−1)^σ |111⟩) = (−1)^σ (|000⟩ + (−1)^σ
|111⟩)`. `X⊗X⊗X` swaps `|000⟩ ↔ |111⟩`, so it sends the cat vector to `|111⟩ + (−1)^σ |000⟩`, which
is `(−1)^σ` times the cat vector (since `((−1)^σ)² = 1`). -/
theorem blockXObservable_op_catBlockVec (σ : Fin 2) :
    blockXObservable.op (catBlockVec σ) = (-1 : ℂ) ^ (σ : ℕ) • catBlockVec σ := by
  rw [catBlockVec, map_add, map_smul, blockXObservable_op_apply_qubitThreeBasis,
    blockXObservable_op_apply_qubitThreeBasis]
  fin_cases σ <;> simp <;> module

/-- **The block cat state is a `±1` eigenstate of the sign-readout observable:**
`catBlockState σ` is an eigenstate of `X⊗X⊗X` with eigenvalue `(−1)^σ`. Equivalently, the `+1`
outcome of measuring `X⊗X⊗X` marks a `+`-sign block (`σ = 0`) and the `−1` outcome a `−`-sign block
(`σ = 1`). Transported from the unnormalised eigenvalue equation `blockXObservable_op_catBlockVec`
through `Observable.hasEigenstate_of_smul`. -/
theorem blockXObservable_hasEigenstate_catBlockState (σ : Fin 2) :
    blockXObservable.HasEigenstate ((-1 : ℝ) ^ (σ : ℕ)) (catBlockState σ) :=
  Observable.hasEigenstate_of_smul (PureState.normalize_vec (catBlockVec σ) (catBlockVec_ne_zero σ))
    (by rw [blockXObservable_op_catBlockVec, Complex.ofReal_pow, Complex.ofReal_neg,
      Complex.ofReal_one])

end AxQM
