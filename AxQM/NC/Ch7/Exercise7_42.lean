/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TemporalLabeling

/-!
# Nielsen & Chuang, Exercise 7.42 (Permutations for temporal labeling)

Permutations for temporal labeling: give a quantum circuit for permutations P,P† taking ρ1 to ρ2 of
(7.154).

*Temporal labeling* (§7.7.1, p. 333) builds an effective pure state on an NMR ensemble by summing
the traceless observables of experiments run on permuted copies of the thermal state. Beginning from
the diagonal two-spin density matrix `ρ₁ = diag(a, b, c, d)` on the big-endian basis
`|00⟩, |01⟩, |10⟩, |11⟩` (7.153), a controlled-NOT circuit `P` cyclically permutes the last three
populations, and `P†` runs the cycle backwards:

* `ρ₂ = P ρ₁ P† = diag(a, c, d, b)`  (7.154),
* `ρ₃ = P† ρ₁ P = diag(a, d, b, c)`  (7.155).

**Answer.** The map on the computational basis fixes `|00⟩` and 3-cycles the rest,
`|01⟩ ↦ |11⟩ ↦ |10⟩ ↦ |01⟩`. Two controlled-NOTs realize it: `P = CNOT₂ · CNOT₁`, where `CNOT₁` has
the first qubit as control (`|10⟩ ↔ |11⟩`) and `CNOT₂` has the second qubit as control
(`|01⟩ ↔ |11⟩`). The product is the permutation matrix of the 3-cycle, and conjugating a diagonal
matrix by a permutation matrix permutes its diagonal — the population shuffle (7.154)/(7.155).

The exercise is a computation about explicit `4 × 4` complex matrices (`CNOT` gates, a diagonal
density matrix, a permutation).

## The formalisation

In `AxQM/Concrete/TemporalLabeling.lean` (namespace `AxQM.Concrete`):

* `temporalLabelRho1 / temporalLabelRho2 / temporalLabelRho3` — the density matrices `ρ₁` (7.153),
  `ρ₂` (7.154), `ρ₃` (7.155), diagonal in the populations `(a, b, c, d)`.
* `cnotSecondControlMatrix` — the `CNOT` with the second qubit as control (`|01⟩ ↔ |11⟩`), the
  mirror of the library's `cnotMatrix` (control = first qubit); `temporalLabelCircuit` — the
  circuit `P = cnotSecondControlMatrix · cnotMatrix`; `temporalLabelPerm` — the 3-cycle it realizes.
* `temporalLabelCircuit_eq_permMatrix` — `P` is the permutation matrix of `temporalLabelPerm`;
  `temporalLabelCircuit_mem_unitaryGroup` — `P` is unitary (a genuine quantum circuit).
* `temporalLabelCircuit_conj_temporalLabelRho1` — **the exercise's `P`**: `P ρ₁ P† = ρ₂` (7.154).
* `temporalLabelCircuit_conjTranspose_conj_temporalLabelRho1` — **the exercise's `P†`**:
  `P† ρ₁ P = ρ₃` (7.155).
* `permMatrix_mul_diagonal_mul_conjTranspose` — the general supporting lemma: a permutation matrix
  conjugates a diagonal matrix by permuting its diagonal, `Pσ diag v Pσᴴ = diag (v ∘ σ)`.

## Fidelity

N&C's `ρ₁` has `a, b, c, d` positive and summing to `1`; the formalised statements quantify over
arbitrary complex `a, b, c, d`, so they are a faithful strengthening (the permutation identity is
independent of positivity/normalisation), not a weakening. Both `P` and `P†` are recorded exactly as
the exercise asks, and `P` is certified unitary.
-/
