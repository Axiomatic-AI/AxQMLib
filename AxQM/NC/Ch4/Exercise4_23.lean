/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledRotation
import AxQM.NC.Ch2.Exercise2_52

/-!
# Nielsen & Chuang, Exercise 4.23 — constructing `C¹(U)` for `U = R_x(θ)`, `R_y(θ)`

*(N&C p. 181.)*

Construct C^1(U) for U=R_x/R_y using CNOT and single-qubit gates; minimize.

`C¹(U) = C(U)` is the controlled operation (N&C §4.3), a closed-system `Evolution` on
`qubit ⊗ qubit`; the exercise is a *circuit identity* expressing it through the `CNOT` gate and
single-qubit rotation gates. The faithful statement is an equality of `Evolution`s built from
`controlledUnitary`, `cnotGate`, `rotXGate`, `rotYGate`, `rotZGate`, `hadamardGate` and the gate
monoid operations (`Evolution.comp`, `Evolution.onRight`).

## The formalisation

* `AxQM.controlledUnitary_rotYGate` — **the reduced controlled-`R_y` construction:**
  `C(R_y(θ)) = (1 ⊗ R_y(θ/2)) · CNOT · (1 ⊗ R_y(-θ/2)) · CNOT`, using **two** single-qubit gates and
  two `CNOT`s — the `3 → 2` reduction the exercise asks for.
* `AxQM.controlledUnitary_rotXGate` — **the controlled-`R_x` construction:**
  `C(R_x(θ)) = (1 ⊗ H) · (1 ⊗ R_z(θ/2)) · CNOT · (1 ⊗ R_z(-θ/2)) · CNOT · (1 ⊗ H)`, built from
  `CNOT` and **three** single-qubit gates via the basis change `R_x(θ) = H R_z(θ) H` — the reduction
  to two is *not* available here (see the design note).

Both use `controlledUnitary_cnot_conj_cnot` (the general two-`CNOT` reduced construction
`(1 ⊗ V) · CNOT · (1 ⊗ W) · CNOT = C(V X W X)` when `V W = I`, itself built from
`controlledUnitary_onRight_conj` and `controlledUnitary_comp`) in
`AxQM/Postulates/API/ControlledUnitary.lean`; the gate-level `R_y`/`R_z` algebra, the Hadamard
basis change `hadamardGate_comp_rotZGate_comp_hadamardGate` (`H R_z(θ) H = R_x(θ)`), and the
controlled-`R_z` lemma `controlledUnitary_rotZGate` are in
`AxQM/Postulates/API/ControlledRotation.lean`.

## Design notes

* **Why this statement shape.** N&C's general recipe (Figure 4.6,
  Corollary 4.2) writes any single-qubit `U = e^{iα} A X B X C` with `A B C = I` and implements
  `C(U)` with three single-qubit gates `A, B, C` (plus a phase gate on the control for `α`). For a
  *rotation* `α = 0`, so no control-phase gate is needed. Both constructions here are exact
  `Evolution` (unitary) identities holding on every input, not "up to phase / on basis states"
  surrogates.
* **The `3 → 2` reduction and why it works for `R_y`/`R_z` but *not* `R_x`.** Taking `C = I`
  needs `U = A X A⁻¹ X`, i.e. `A X A⁻¹ = U X` must be a conjugate of `X` (traceless and Hermitian).
  Conjugation by `X` sends `R_a(φ) ↦ R_a(-φ)` for an axis `a ⊥ X` (`X R_y(φ) X = R_y(-φ)`), so with
  `A = R_y(θ/2)` we get `A X A⁻¹ X = R_y(θ/2) R_y(θ/2) = R_y(θ)` — the reduction succeeds with the
  two gates `A = R_y(θ/2)`, `B = A⁻¹ = R_y(-θ/2)` (and identically for `R_z`). For `R_x` this fails:
  `X` *commutes* with `R_x`, so `X R_x(-θ/2) X = R_x(-θ/2)` cancels rather than doubling, and
  `R_x(θ) X` is not a conjugate of `X`. Controlled-`R_x` therefore genuinely needs **three**
  single-qubit gates; it is built by the basis change `R_x(θ) = H R_z(θ) H` (`H Z H = X`), wrapping
  the two-gate controlled-`R_z` in a Hadamard on the target on each side.
* **Proofs.** `controlledUnitary_rotYGate` is immediate from `controlledUnitary_cnot_conj_cnot` at
  `V = R_y(θ/2)`, `W = R_y(-θ/2)`, collapsing `R_y(θ/2) X R_y(-θ/2) X` to `R_y(θ)`.
  `controlledUnitary_rotXGate` folds the inlined controlled-`R_z` circuit back to
  `controlledUnitary (rotZGate θ)` (`controlledUnitary_rotZGate`), conjugates it by `1 ⊗ H` via
  `controlledUnitary_onRight_conj` (with `H H = I`, `hadamardGate_sq`) to get
  `C(H R_z(θ) H)`, then rewrites `H R_z(θ) H = R_x(θ)`
  (`hadamardGate_comp_rotZGate_comp_hadamardGate`). Both theorems only *apply* those lemmas.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.23 (controlled-`R_y`, reduced to two single-qubit gates).** The
controlled-`R_y(θ)` gate is realised from two `CNOT`s and just two single-qubit gates:
`C(R_y(θ)) = (1 ⊗ R_y(θ/2)) · CNOT · (1 ⊗ R_y(-θ/2)) · CNOT`,
where `Evolution.onRight (rotYGate _) qubit = 1 ⊗ R_y(_)` applies the rotation to the target (right)
qubit while leaving the control untouched. This is the `3 → 2` reduction of the general Figure-4.6
recipe: the ABC witnesses are `A = R_y(θ/2)`, `B = R_y(-θ/2)`, `C = I`, so only `A`, `B` remain.

Proved by instantiating the general two-`CNOT` construction `controlledUnitary_cnot_conj_cnot` at
`V = R_y(θ/2)`, `W = R_y(-θ/2)` (with `V W = I` from `rotYGate_comp`/`rotYGate_zero`) and collapsing
the target gate `R_y(θ/2) · X · R_y(-θ/2) · X` to `R_y(θ)`. -/
theorem controlledUnitary_rotYGate (θ : ℝ) :
    controlledUnitary (rotYGate θ)
      = (((rotYGate (θ / 2)).onRight qubit).comp cnotGate).comp
          (((rotYGate (-(θ / 2))).onRight qubit).comp cnotGate) := by
  have hVW : (rotYGate (θ / 2)).comp (rotYGate (-(θ / 2))) = Evolution.id := by
    rw [rotYGate_comp, add_neg_cancel, rotYGate_zero]
  rw [controlledUnitary_cnot_conj_cnot (rotYGate (θ / 2)) (rotYGate (-(θ / 2))) hVW]
  congr 1
  rw [pauliXGate_comp_rotYGate_comp_pauliXGate, neg_neg, rotYGate_comp, add_halves]

/-- **Nielsen & Chuang, Exercise 4.23 (controlled-`R_x`).** The controlled-`R_x(θ)` gate is realised
from `CNOT` and three single-qubit gates via the basis change `R_x(θ) = H R_z(θ) H`:
`C(R_x(θ)) = (1 ⊗ H) · (1 ⊗ R_z(θ/2)) · CNOT · (1 ⊗ R_z(-θ/2)) · CNOT · (1 ⊗ H)`,
i.e. the reduced controlled-`R_z` circuit conjugated on the target qubit by a Hadamard on each side.
Unlike `R_y`/`R_z`, `R_x` commutes with `X`, so the two-single-qubit-gate reduction is unavailable
and three single-qubit gates (here `H`, `R_z(±θ/2)`, `H`) are genuinely needed.

Proved by folding the inlined controlled-`R_z` circuit back to `controlledUnitary (rotZGate θ)`
(`controlledUnitary_rotZGate`), applying `controlledUnitary_onRight_conj` (with `H H = I`) to obtain
`C(H · R_z(θ) · H)`, and rewriting `H · R_z(θ) · H = R_x(θ)`
(`hadamardGate_comp_rotZGate_comp_hadamardGate`). -/
theorem controlledUnitary_rotXGate (θ : ℝ) :
    controlledUnitary (rotXGate θ)
      = (hadamardGate.onRight qubit).comp
          (((((rotZGate (θ / 2)).onRight qubit).comp cnotGate).comp
              (((rotZGate (-(θ / 2))).onRight qubit).comp cnotGate)).comp
            (hadamardGate.onRight qubit)) := by
  have hHH : hadamardGate.comp hadamardGate = Evolution.id := by
    rw [← Evolution.mul_def, ← sq, hadamardGate_sq, Evolution.one_def]
  rw [← controlledUnitary_rotZGate θ,
    controlledUnitary_onRight_conj (rotZGate θ) hadamardGate hadamardGate hHH,
    hadamardGate_comp_rotZGate_comp_hadamardGate]

end AxQM
