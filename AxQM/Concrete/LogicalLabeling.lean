/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TemporalLabeling

/-!
# Logical labeling: the population-permutation circuit (Nielsen & Chuang, Exercise 7.43)

*Logical labeling* (§7.7.1, p. 334–335) prepares an *effective pure state* on an NMR ensemble of
three nearly identical spins, using a single experiment (unlike temporal labeling, §7.7.1 /
Exercise 7.42, which averages over several). Starting from the three-spin deviation density matrix
(N&C 7.162)

`ρ = δ I + α · diag(6, 2, 2, -2, 2, -2, -2, -6)`

on the big-endian computational basis `|000⟩, …, |111⟩` (the signal populations are `6 - 4·(Hamming
weight)`; the isotropic background `δ I` is unobservable because NMR observables are traceless), one
applies a **permutation** `P` of the computational basis to obtain (N&C 7.164)

`ρ' = P ρ P† = δ I + α · diag(6, -2, -2, -2, -6, 2, 2, 2)`.

The point of the rearrangement is the upper-left `4 × 4` block of the signal part of `ρ'` (N&C
7.165):

`diag(6, -2, -2, -2) = 8 |00⟩⟨00| - 2 I`,

an *effective pure state* on the `|000⟩, |001⟩, |010⟩, |011⟩` manifold (first qubit `= 0`): running
a computation on this manifold yields, up to the unobservable background, the result one would get
from a genuine `|00⟩⟨00|` input.

**Exercise 7.43** asks for a quantum circuit realizing the permutation `P`.

## The circuit

`P` must send the source populations `(6, 2, 2, -2, 2, -2, -2, -6)` to the target
`(6, -2, -2, -2, -6, 2, 2, 2)`.
The unique `6` is fixed at `|000⟩`; the unique `-6` moves `|111⟩ → |100⟩`; and the three `+2`
(weight-1) and three `-2` (weight-2) populations swap manifolds. A clean choice is the involution

`P = (|001⟩ |101⟩)(|010⟩ |110⟩)(|100⟩ |111⟩)`,

i.e. `logicalLabelPerm = swap 1 5 * swap 2 6 * swap 4 7` on indices. This file gives `P` as an
explicit **gate circuit** — the product
`logicalLabelCircuit = logicalLabelCFlip · logicalLabelCCNot10 · logicalLabelCCNot01` of three named
gate matrices — and proves that product equals the permutation matrix
(`logicalLabelCircuit_eq_permMatrix`), mirroring the sibling temporal-labeling circuit
(`temporalLabelCircuit_eq_permMatrix`). The three gates are:

* `logicalLabelCCNot01`, `logicalLabelCCNot10` — two doubly-controlled-NOTs flipping the first qubit
  conditioned on the last two (`|001⟩ ↔ |101⟩` for `(q₁, q₂) = (0, 1)`, `|010⟩ ↔ |110⟩` for
  `(q₁, q₂) = (1, 0)`);
* `logicalLabelCFlip` — conditioned on the first qubit being `|1⟩`, the involution that exchanges
  `|00⟩ ↔ |11⟩` of the last two qubits while fixing `|01⟩, |10⟩` (flip *both* last qubits when they
  are equal), realizing `|100⟩ ↔ |111⟩`. (Note this is **not** a controlled-SWAP of the last two
  qubits: a Fredkin gate would swap `|101⟩ ↔ |110⟩` and fix `|100⟩, |111⟩`.)

Each gate is a permutation of the computational basis, so `logicalLabelCircuit` is manifestly
unitary (`logicalLabelCircuit_mem_unitaryGroup`). Since `P` is a permutation matrix, conjugating the
diagonal `ρ` by it merely permutes the diagonal (`permMatrix_mul_diagonal_mul_conjTranspose`), which
is exactly the population shuffle (7.164).

The whole exercise is a computation about explicit `8 × 8` complex matrices — a diagonal density
matrix and a permutation matrix. The statement of Exercise 7.43 is in
`AxQM/NC/Ch7/Exercise7_43.lean`. Compare `AxQM/Concrete/TemporalLabeling.lean` (Exercise 7.42),
whose general lemma `permMatrix_mul_diagonal_mul_conjTranspose` is reused here.

## Fidelity

N&C's `ρ` has `δ` a real background and `α ≪ δ` a small real constant. The statements here quantify
over **arbitrary** complex `δ, α`: the conjugation identity holds regardless (the background `δ I`
is invariant under any unitary conjugation, and the permutation identity is independent of the
magnitudes), so this is a faithful strengthening of the textbook claim, not a weakening. The circuit
`P` is recorded exactly as the exercise asks, certified unitary, and shown to produce `ρ'` (7.164);
the effective-pure-state block (7.165) is recorded as `logicalLabel_effectivePureBlock`.
-/

namespace AxQM.Concrete

open Matrix

/-- **Combining the background and signal parts of a deviation density matrix into one diagonal.**
`δ • I + α • diagonal v = diagonal (fun i => δ + α * v i)`; the `δ I` background and the `α`-scaled
signal `v` sit on the same diagonal. A small linear-algebra helper used to put `ρ` (7.162) and `ρ'`
(7.164) into the `diagonal` form that `permMatrix_mul_diagonal_mul_conjTranspose` consumes. -/
theorem diagonal_smul_one_add_smul_diagonal {n : Type*} [DecidableEq n]
    (δ α : ℂ) (v : n → ℂ) :
    δ • (1 : Matrix n n ℂ) + α • Matrix.diagonal v = Matrix.diagonal (fun i => δ + α * v i) := by
  ext i j
  by_cases h : i = j <;> simp [h]

/-- **The signal populations of `ρ` (N&C 7.162)**: `(6, 2, 2, -2, 2, -2, -2, -6)` on the big-endian
three-spin basis `|000⟩, …, |111⟩`. Entry `i` equals `6 - 4·(Hamming weight of i)`. -/
def logicalLabelDiag : Fin 8 → ℂ := ![6, 2, 2, -2, 2, -2, -2, -6]

/-- **The signal populations of `ρ'` after logical labeling (N&C 7.164)**:
`(6, -2, -2, -2, -6, 2, 2, 2)`. -/
def logicalLabelDiag' : Fin 8 → ℂ := ![6, -2, -2, -2, -6, 2, 2, 2]

/-- **`ρ` of N&C (7.162)**: the three-spin deviation density matrix `δ I + α · diag(populations)`,
with background `δ I` and signal `α · diag logicalLabelDiag`. -/
noncomputable def logicalLabelRho (δ α : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  δ • (1 : Matrix (Fin 8) (Fin 8) ℂ) + α • Matrix.diagonal logicalLabelDiag

/-- **`ρ'` of N&C (7.164)**: the state after the logical-labeling permutation,
`δ I + α · diag logicalLabelDiag'`. -/
noncomputable def logicalLabelRho' (δ α : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  δ • (1 : Matrix (Fin 8) (Fin 8) ℂ) + α • Matrix.diagonal logicalLabelDiag'

/-- **The logical-labeling permutation `P` (Exercise 7.43)**: the basis involution
`(|001⟩ |101⟩)(|010⟩ |110⟩)(|100⟩ |111⟩)`, i.e. `swap 1 5 * swap 2 6 * swap 4 7` on indices. It
fixes `|000⟩` (population `6`), moves `|111⟩ ↔ |100⟩` (the `-6`), and swaps the weight-1 and
weight-2 manifolds. -/
def logicalLabelPerm : Equiv.Perm (Fin 8) :=
  Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 4 7

/-- **Gate `A₀₁` — a doubly-controlled `NOT` on the first qubit, active when the last two qubits are
`|01⟩`.** It flips `q₀` exactly on the control pattern `(q₁, q₂) = (0, 1)`, i.e. it is the basis
transposition `|001⟩ ↔ |101⟩` (indices `1 ↔ 5`) and fixes every other computational basis state. -/
noncomputable def logicalLabelCCNot01 : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if Equiv.swap 1 5 i = j then 1 else 0

/-- **Gate `A₁₀` — a doubly-controlled `NOT` on the first qubit, active when the last two qubits are
`|10⟩`.** It flips `q₀` exactly on the control pattern `(q₁, q₂) = (1, 0)`, i.e. the basis
transposition `|010⟩ ↔ |110⟩` (indices `2 ↔ 6`), fixing every other computational basis state. -/
noncomputable def logicalLabelCCNot10 : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if Equiv.swap 2 6 i = j then 1 else 0

/-- **Gate `B` — controlled (on `q₀ = |1⟩`) exchange `|00⟩ ↔ |11⟩` of the last two qubits.** When
the first qubit is `|1⟩` it flips *both* last qubits whenever they are equal (`|00⟩ ↔ |11⟩`, fixing
`|01⟩, |10⟩`); when `q₀ = |0⟩` it acts trivially. As a basis permutation this is the transposition
`|100⟩ ↔ |111⟩` (indices `4 ↔ 7`). This is **not** a controlled-`SWAP` (Fredkin) of the last two
qubits — a Fredkin would instead exchange `|101⟩ ↔ |110⟩` and fix `|100⟩, |111⟩`. -/
noncomputable def logicalLabelCFlip : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if Equiv.swap 4 7 i = j then 1 else 0

/-- Gate `A₀₁` is the permutation matrix of the transposition `(1 5)`. -/
theorem logicalLabelCCNot01_eq_permMatrix :
    logicalLabelCCNot01 = (Equiv.swap (1 : Fin 8) 5).permMatrix ℂ :=
  permMatrix_eq_of_ite _

/-- Gate `A₁₀` is the permutation matrix of the transposition `(2 6)`. -/
theorem logicalLabelCCNot10_eq_permMatrix :
    logicalLabelCCNot10 = (Equiv.swap (2 : Fin 8) 6).permMatrix ℂ :=
  permMatrix_eq_of_ite _

/-- Gate `B` is the permutation matrix of the transposition `(4 7)`. -/
theorem logicalLabelCFlip_eq_permMatrix :
    logicalLabelCFlip = (Equiv.swap (4 : Fin 8) 7).permMatrix ℂ :=
  permMatrix_eq_of_ite _

/-- **The logical-labeling circuit `P`** (Exercise 7.43) as the explicit product of its three gates:
the two doubly-controlled-`NOT`s `logicalLabelCCNot01`, `logicalLabelCCNot10` and the controlled
exchange `logicalLabelCFlip` (written right-to-left, so the leftmost factor acts last; the three
gates commute, being disjoint, so the physical order is immaterial). Being a product of permutation
— hence unitary — gates it is a genuine reversible quantum circuit on the computational basis;
`logicalLabelCircuit_eq_permMatrix` identifies it with the permutation matrix of
`logicalLabelPerm`. -/
noncomputable def logicalLabelCircuit : Matrix (Fin 8) (Fin 8) ℂ :=
  logicalLabelCFlip * logicalLabelCCNot10 * logicalLabelCCNot01

/-- **The gate product realizes the permutation `P`**: the circuit
`logicalLabelCFlip * logicalLabelCCNot10 * logicalLabelCCNot01` equals the permutation matrix of
`logicalLabelPerm`. Each gate is the permutation matrix of one of the three disjoint transpositions
`(1 5), (2 6), (4 7)`; their product is the permutation matrix of the composite permutation by
anti-multiplicativity of `permMatrix` (`Matrix.permMatrix_mul`). -/
theorem logicalLabelCircuit_eq_permMatrix :
    logicalLabelCircuit = logicalLabelPerm.permMatrix ℂ := by
  rw [logicalLabelCircuit, logicalLabelCFlip_eq_permMatrix, logicalLabelCCNot10_eq_permMatrix,
    logicalLabelCCNot01_eq_permMatrix, logicalLabelPerm, Matrix.permMatrix_mul,
    Matrix.permMatrix_mul, mul_assoc]

/-- **The permutation rearranges the source populations into the target populations**:
`logicalLabelDiag ∘ logicalLabelPerm = logicalLabelDiag'`. This is the combinatorial heart of the
exercise — `P` maps `(6, 2, 2, -2, 2, -2, -2, -6)` to `(6, -2, -2, -2, -6, 2, 2, 2)`. -/
theorem logicalLabelDiag_comp_perm :
    logicalLabelDiag ∘ logicalLabelPerm = logicalLabelDiag' := by
  funext i
  fin_cases i <;>
    simp [logicalLabelDiag, logicalLabelDiag', logicalLabelPerm, Equiv.swap_apply_def]

/-- **The circuit `P` is unitary** — a genuine quantum operation — because it is a permutation
matrix. -/
theorem logicalLabelCircuit_mem_unitaryGroup :
    logicalLabelCircuit ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [logicalLabelCircuit_eq_permMatrix]
  exact permMatrix_mem_unitaryGroup logicalLabelPerm

/-- **Exercise 7.43 (N&C 7.164)**: the logical-labeling circuit `P` transforms `ρ` into `ρ'`,
`P ρ P† = ρ'`. Conjugating the diagonal `ρ` by the permutation matrix `P` permutes its diagonal
(`permMatrix_mul_diagonal_mul_conjTranspose`); the resulting permutation of the populations is
exactly `logicalLabelDiag_comp_perm`, and the isotropic background `δ I` is carried along unchanged.
-/
theorem logicalLabelCircuit_conj_logicalLabelRho (δ α : ℂ) :
    logicalLabelCircuit * logicalLabelRho δ α * logicalLabelCircuitᴴ = logicalLabelRho' δ α := by
  rw [logicalLabelRho, diagonal_smul_one_add_smul_diagonal, logicalLabelCircuit_eq_permMatrix,
    permMatrix_mul_diagonal_mul_conjTranspose, logicalLabelRho',
    diagonal_smul_one_add_smul_diagonal]
  simp only [Function.comp_def, ← logicalLabelDiag_comp_perm]

/-- **The effective-pure-state block (N&C 7.165)**: the upper-left `4 × 4` block of the signal part
of `ρ'` — the populations `(6, -2, -2, -2)` of the `|000⟩, |001⟩, |010⟩, |011⟩` manifold — equals
`8 |00⟩⟨00| - 2 I`, where `|00⟩⟨00| = diagonal ![1, 0, 0, 0]` and `I` is the `4 × 4` identity. This
is the effective pure state that makes logical labeling work. -/
theorem logicalLabel_effectivePureBlock :
    Matrix.diagonal ![(6 : ℂ), -2, -2, -2]
      = (8 : ℂ) • Matrix.diagonal ![(1 : ℂ), 0, 0, 0]
        - (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.diagonal, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

/-- **The block of (7.165) is the top of `ρ'`**: the first four signal populations of `ρ'` (the
first-qubit-`= 0` manifold `|000⟩, |001⟩, |010⟩, |011⟩`) are `(6, -2, -2, -2)`, the block of
`logicalLabel_effectivePureBlock`. -/
theorem logicalLabelDiag'_manifold (i : Fin 4) :
    logicalLabelDiag' (Fin.castLE (by norm_num) i) = ![(6 : ℂ), -2, -2, -2] i := by
  fin_cases i <;> rfl

end AxQM.Concrete
