/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.LogicalLabeling

/-!
# Nielsen & Chuang, Exercise 7.43 (Permutations for logical labeling)

Permutations for logical labeling: give a circuit for permutation P taking ρ of (7.163) to ρ' of
(7.165).

*Logical labeling* (§7.7.1, p. 334–335) prepares an *effective pure state* on an NMR ensemble of
three nearly identical spins in a **single** experiment. The three-spin deviation density matrix
is (N&C 7.162)

`ρ = δ I + α · diag(6, 2, 2, -2, 2, -2, -2, -6)`

on the big-endian basis `|000⟩, …, |111⟩` (populations `6 - 4·(Hamming weight)`; the background
`δ I` is unobservable since NMR observables are traceless). A permutation `P` of the computational
basis produces (N&C 7.164)

`ρ' = P ρ P† = δ I + α · diag(6, -2, -2, -2, -6, 2, 2, 2)`,

whose upper-left `4 × 4` block is the effective pure state `8 |00⟩⟨00| - 2 I` (N&C 7.165) on the
`|000⟩, |001⟩, |010⟩, |011⟩` manifold.

**Answer.** The permutation is the basis involution
`P = (|001⟩ |101⟩)(|010⟩ |110⟩)(|100⟩ |111⟩)`: it fixes `|000⟩` (population `6`), moves the `-6` via
`|111⟩ ↔ |100⟩`, and swaps the weight-1 (`+2`) and weight-2 (`-2`) manifolds so the top block
becomes `(6, -2, -2, -2)`. As a circuit it is the product of three gates: two doubly-controlled-NOTs
on the first qubit (`|001⟩ ↔ |101⟩`, `|010⟩ ↔ |110⟩`) plus, conditioned on the first qubit being
`|1⟩`, a controlled-`(|00⟩ ↔ |11⟩)` gate on the last two qubits — flipping *both* last qubits when
they are equal, which exchanges `|100⟩ ↔ |111⟩` (this is **not** a controlled-SWAP, which would
instead swap `|101⟩ ↔ |110⟩`). Each gate is a computational-basis permutation, so the circuit is a
genuine unitary quantum circuit. Conjugating the diagonal `ρ` by the permutation matrix permutes its
diagonal, giving `ρ'`.

The exercise is a computation about explicit `8 × 8` complex matrices (a diagonal density matrix and
a permutation matrix). Compare Exercise 7.42 (temporal labeling), whose supporting
lemma `permMatrix_mul_diagonal_mul_conjTranspose` is used here.

## The formalisation

In `AxQM/Concrete/LogicalLabeling.lean` (namespace `AxQM.Concrete`):

* `logicalLabelDiag` / `logicalLabelDiag'` — the signal populations of `ρ` (7.162) and `ρ'` (7.164).
* `logicalLabelRho` / `logicalLabelRho'` — the density matrices `ρ` (7.162) and `ρ'` (7.164), in the
  `δ I + α · diag(populations)` form.
* `logicalLabelPerm` — the permutation `P = (1 5)(2 6)(4 7)`.
* `logicalLabelCCNot01` / `logicalLabelCCNot10` — the two doubly-controlled-NOTs (flip `q₀` when the
  last two qubits are `|01⟩` / `|10⟩`); `logicalLabelCFlip` — the controlled (on `q₀ = |1⟩`)
  exchange `|00⟩ ↔ |11⟩` of the last two qubits. `logicalLabelCircuit` — the circuit `P` as the
  **product** of these three gates; `logicalLabelCircuit_eq_permMatrix` proves that gate product
  equals the permutation matrix of `logicalLabelPerm`.
* `logicalLabelDiag_comp_perm` — the combinatorial core: `P` maps the source populations to the
  target populations.
* `logicalLabelCircuit_mem_unitaryGroup` — `P` is unitary (a genuine quantum circuit).
* `logicalLabelCircuit_conj_logicalLabelRho` — **the exercise's `P`**: `P ρ P† = ρ'` (7.164).
* `logicalLabel_effectivePureBlock` — **N&C (7.165)**: the upper `4 × 4` block `diag(6, -2, -2, -2)`
  of the signal part of `ρ'` equals `8 |00⟩⟨00| - 2 I`; `logicalLabelDiag'_manifold` places that
  block as the first-qubit-`= 0` manifold of `ρ'`.

## Fidelity

N&C's `ρ` has `δ` a real background and `α ≪ δ` a small real constant. The formalised statements
quantify over arbitrary complex `δ, α`, so they are a faithful strengthening (the conjugation
identity is independent of the magnitudes and of positivity/normalisation), not a weakening. The
circuit `P` is recorded exactly as the exercise asks — as an explicit **gate circuit**, the product
of three named reversible gates, proved (`logicalLabelCircuit_eq_permMatrix`) to realise the
permutation — certified unitary, and shown to produce `ρ'` (7.164); the effective-pure-state block
(7.165) is recorded.
-/
