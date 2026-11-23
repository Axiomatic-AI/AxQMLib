/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledTowerAction
import AxQM.Postulates.API.Associator
import AxQM.Postulates.API.SystemIsoComm

/-!
# Factoring an idle module out of a control tower (N&C Ex 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The faithful `n+1`-wire circuit is the
Barenco unfolding `barencoNCircuit` (`cnx_eq_barencoNCircuit`), whose distinctive content is
bottoming its internal multiply-controlled `NOT` blocks `Cᵏ(X)` to genuine `Toffoli`s.
Each such block is `mcCtrl k (pauliXGate.onLeft M)` acting on the
control tower `qtower k (qubit ⊗ M)` — `k` outer control qubits, the `X`-target the head of the
inner `qubit ⊗ M`, and an **idle target-module `M`** (the wires the block does not touch). Its
reduction is described from opposite ends but on **different registers**:

* `mcCtrl_pauliXGate_onLeft_evolvePure_ctrlTower` reads the block's computational-basis action on
  the tower `qtower k (qubit ⊗ M)`, with the idle `M` carried along as a right factor of the base
  state;
* `tensorPowMcCtrlX_onBlock_eq_toffoliCircuit` exhibits the bounded `O(k²)` `Toffoli` circuit, but
  on the **flattened symmetric register** `qubit ^⊗ₛ (k+1+b)`.

Matching the two needs a structural bridge that separates the idle module from the tower. This file
constructs its first step: pulling the idle right factor `M` out of the tower's inner system,
`qtower k (S ⊗ M) ≃ₛ (qtower k S) ⊗ M`. (Composed with the `qtower ↔ tensor-power` bridge
`qtowerQubitTensorPow` on the `(qtower k S)` factor and the block split `tensorPowAdd`, this
reaches the flattened register `qubit ^⊗ₛ (k+1) ⊗ (qubit ^⊗ₛ b) ≃ₛ qubit ^⊗ₛ (k+1+b)` of
`tensorPowMcCtrlX_onBlock_eq_toffoliCircuit`.)

## What is formalised

* `qtowerComposeRight k` — the **module-factoring bridge** `qtower k (S ⊗ M) ≃ₛ (qtower k S) ⊗ M`.
  Both sides prepend the same `k` control qubits; on the left the idle module `M` sits *inside* the
  tower (`qubitᵏ ⊗ (S ⊗ M)`), on the right it is pulled *out* to a trailing factor
  (`(qubitᵏ ⊗ S) ⊗ M`) — the same register up to reassociation. Built by induction on `k`: the base
  `qtower 0 (S ⊗ M) = S ⊗ M = (qtower 0 S) ⊗ M` is the identity, and each step tensors the identity
  on the peeled head control with the tail bridge and reassociates the new control past the module
  through the associator `QSystem.assoc`.
* `qtowerComposeRight_congr_ctrlTower` — the **basis dictionary**: the bridge carries a
  control-tower input whose base is a product `ρ ⊗ φ` (an inner state `ρ : PureState S` and an idle
  module state `φ : PureState M`) to the control tower over `ρ` alone, tensored with the untouched
  `φ`:
  `qtowerComposeRight k (ctrlTower k c (ρ ⊗ φ)) = (ctrlTower k c ρ) ⊗ φ`.
  With `S = qubit` and `ρ = |i⟩` this is exactly the flattening of a `barencoNCircuit`-block input
  `ctrlTower k c (|i⟩ ⊗ φ)` (`mcCtrl_pauliXGate_onLeft_evolvePure_ctrlTower`) into a control tower
  over the target qubit with the idle module split off — the form on which the block's `Toffoli`
  reduction is read.
* `qtowerComposeRight_symm_congr_tmul` — the **backward** dictionary, the `.symm` companion (via the
  `PureState.congr` roundtrip `PureState.congr_symm_congr`): the inverse bridge folds a flattened
  input `(ctrlTower k c ρ) ⊗ φ` back to the tower input `ctrlTower k c (ρ ⊗ φ)` — the direction
  used when a gate computed on the flattened register is transported back onto the block's tower.

## Design notes

* **Why general in `S`.** The controls prepended by `ctrlTower`/`qtower` are qubits regardless of
  the inner system, so nothing in the construction uses `S = qubit`; keeping `S` and `M` arbitrary
  makes the bridge reusable (the block reduction instantiates `S = qubit`, `ρ = qubitBasis i`).
* **Why the recursion matches definitionally.** `qtower (k+1) X = qubit ⊗ qtower k X`
  *definitionally* (peeling the outer control is the defining equation of `qtower` on its `ℕ`
  argument, the same reduction `mcCtrl_succ` uses), so both the
  successor isomorphism `((Iso.refl qubit).tmul (bridge k)).trans (assoc …)` (of domain
  `qubit ⊗ qtower k (S ⊗ M)`) and its codomain `(qubit ⊗ qtower k S) ⊗ M` type-check against the
  expected `qtower (k+1) (S ⊗ M) ≃ₛ (qtower (k+1) S) ⊗ M` with no `cast`.
* **Proof of the dictionary.** By `PureState.ext` it reduces to an equation of state vectors,
  proved by induction: the step peels the head control with `PureState.tmul_vec`, applies
  `QSystem.Iso.tmul_toIsometry_tmul` and the inductive hypothesis to the tail, then re-brackets the
  head control past the module with `QSystem.assoc_toIsometry_tmul_tmul`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S M : QSystem}

/-- **The module-factoring bridge** `qtower k (S ⊗ M) ≃ₛ (qtower k S) ⊗ M`: the system isomorphism
that pulls the idle right factor `M` out of a control tower's inner system, from *inside* the tower
(`qubitᵏ ⊗ (S ⊗ M)`) to a trailing factor (`(qubitᵏ ⊗ S) ⊗ M`). Built by induction on `k` — the
base `qtower 0 (S ⊗ M) = S ⊗ M = (qtower 0 S) ⊗ M` is the identity, and each step tensors the
identity on the peeled head control with the tail bridge and reassociates the new control past the
module through `QSystem.assoc`. Its basis action is `qtowerComposeRight_congr_ctrlTower`. -/
def qtowerComposeRight : (k : ℕ) → (qtower k (S ⊗ M)).Iso ((qtower k S) ⊗ M)
  | 0 => QSystem.Iso.refl (S ⊗ M)
  | k + 1 =>
      ((QSystem.Iso.refl qubit).tmul (qtowerComposeRight k)).trans
        (QSystem.assoc qubit (qtower k S) M)

/-- Base unfolding of the bridge: with no controls the tower is its inner system, so factoring the
module out is the identity. -/
@[simp] theorem qtowerComposeRight_zero :
    qtowerComposeRight (S := S) (M := M) 0 = QSystem.Iso.refl (S ⊗ M) := rfl

/-- Step unfolding of the bridge: tensor the identity on the peeled head control with the tail
bridge, then reassociate the new control past the module through `QSystem.assoc`. -/
theorem qtowerComposeRight_succ (k : ℕ) :
    qtowerComposeRight (S := S) (M := M) (k + 1)
      = ((QSystem.Iso.refl qubit).tmul (qtowerComposeRight k)).trans
          (QSystem.assoc qubit (qtower k S) M) := rfl

/-- **Basis dictionary for the module-factoring bridge.** The bridge
`qtower k (S ⊗ M) ≃ₛ (qtower k S) ⊗ M` carries a control-tower input whose base is a product state
`ρ ⊗ φ` — an inner state `ρ : PureState S` tensored with an idle module state `φ : PureState M` — to
the control tower over `ρ` alone, tensored with the untouched `φ`:

`qtowerComposeRight k (ctrlTower k c (ρ ⊗ φ)) = (ctrlTower k c ρ) ⊗ φ`.

Instantiated at `S = qubit`, `ρ = |i⟩` this flattens a `barencoNCircuit`-block input
`ctrlTower k c (|i⟩ ⊗ φ)` (the states of `mcCtrl_pauliXGate_onLeft_evolvePure_ctrlTower`) into
a control tower over the target qubit with the idle module `φ` split off as a trailing factor — the
form on which the block's bounded `Toffoli` circuit
(`tensorPowMcCtrlX_onBlock_eq_toffoliCircuit`, on the flattened register) is matched. Proved by
`PureState.ext` and induction on `k` on state vectors: peel the head control
(`PureState.tmul_vec`), push the tail through the
inductive hypothesis (`QSystem.Iso.tmul_toIsometry_tmul`), and re-bracket the head control past the
module (`QSystem.assoc_toIsometry_tmul_tmul`). -/
theorem qtowerComposeRight_congr_ctrlTower (k : ℕ) (c : Fin k → Fin 2) (ρ : PureState S)
    (φ : PureState M) :
    PureState.congr (qtowerComposeRight k) (ctrlTower k c (ρ.tmul φ))
      = (ctrlTower k c ρ).tmul φ := by
  suffices key : ∀ (m : ℕ) (d : Fin m → Fin 2),
      (qtowerComposeRight m).toIsometry (ctrlTower m d (ρ.tmul φ)).vec
        = (ctrlTower m d ρ).vec ⊗ₜ[ℂ] φ.vec by
    apply PureState.ext
    rw [PureState.congr_vec, PureState.tmul_vec]
    exact key k c
  intro m
  induction m with
  | zero =>
      intro d
      -- `qtowerComposeRight 0 = Iso.refl (S ⊗ M)` (identity isometry) and `ctrlTower 0 d ψ = ψ`.
      rw [qtowerComposeRight_zero, ctrlTower_zero, ctrlTower_zero, PureState.tmul_vec]
      rfl
  | succ k ih =>
      intro d
      -- `qtowerComposeRight (k+1)` is definitionally
      -- `((refl qubit).tmul (bridge k)).trans (assoc qubit (qtower k S) M)`; apply its two isometry
      -- factors in turn (`qtower (k+1) X = qubit ⊗ qtower k X` definitionally, so a `change` peels
      -- the head-control isometry chain into its two `QSystem.Iso` factors with no `cast`).
      rw [ctrlTower_succ, PureState.tmul_vec]
      change (QSystem.assoc qubit (qtower k S) M).toIsometry
          (((QSystem.Iso.refl qubit).tmul (qtowerComposeRight k)).toIsometry
            ((qubitBasis (d 0)).vec ⊗ₜ[ℂ] (ctrlTower k (fun i => d i.succ) (ρ.tmul φ)).vec))
          = (ctrlTower (k + 1) d ρ).vec ⊗ₜ[ℂ] φ.vec
      rw [QSystem.Iso.tmul_toIsometry_tmul, ih (fun i => d i.succ), assoc_toIsometry_tmul_tmul,
        ctrlTower_succ, PureState.tmul_vec]
      -- The residual `(Iso.refl qubit).toIsometry` on the head control is the identity isometry.
      rfl

/-- **Backward basis dictionary for the module-factoring bridge.** The *inverse* bridge
`(qtowerComposeRight k).symm` folds a flattened control-tower input `(ctrlTower k c ρ) ⊗ φ` — a
control tower over an inner state `ρ : PureState S` with a trailing idle module state
`φ : PureState M` — back into the tower input `ctrlTower k c (ρ ⊗ φ)` on `qtower k (S ⊗ M)`. The
`.symm` companion of `qtowerComposeRight_congr_ctrlTower`, obtained from it by the `PureState.congr`
roundtrip cancellation `PureState.congr_symm_congr`. This is the direction consumed when a gate
computed on the flattened register is transported back onto the block's tower. -/
theorem qtowerComposeRight_symm_congr_tmul (k : ℕ) (c : Fin k → Fin 2) (ρ : PureState S)
    (φ : PureState M) :
    PureState.congr (qtowerComposeRight k).symm ((ctrlTower k c ρ).tmul φ)
      = ctrlTower k c (ρ.tmul φ) := by
  rw [← qtowerComposeRight_congr_ctrlTower k c ρ φ, PureState.congr_symm_congr]

end AxQM
