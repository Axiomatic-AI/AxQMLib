/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledReduction

/-!
# The multiplexer `Cᵏ(G)` acts on a control tower as `G` gated on all controls (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The `n+1`-wire construction is the
Barenco unfolding `barencoNCircuit` (`cnx_eq_barencoNCircuit`): a nested stack of
`barencoTail` layers built from single-qubit-controlled `√X` gates and **multiply-controlled `NOT`
blocks** `Cᵏ(X) = mcCtrl k (pauliXGate.onLeft M)` (`Core/MultiControlledReduction.barencoTail`),
each acting on `qtower k (qubit ⊗ M)` — `k` outer control qubits, one `X`-target head of the
inner `qubit ⊗ M`, and the idle target-module `M`. Bottoming those blocks to genuine `Toffoli`s is
the other distinctive content of the exercise.

This file reads off the **computational-basis action of one such block** — the quantum side of the
per-block reduction. The basis bridge `mcCtrl_pauliXGate_evolvePure_towerKet`
(`Core/MultiControlledNotBasis`) handles the *aligned* gate `mcCtrl n pauliXGate` whose
target is the *innermost* wire (target module trivial). A `barencoNCircuit` block instead carries a
whole idle target module `M`, so its action must be stated with `M` present.

## What is formalised

* `ctrlTower k c ρ` — the **control-tower input state** on `qtower k R`: `k` computational control
  qubits `|c 0⟩ ⊗ … ⊗ |c (k-1)⟩` prepended (one per control wire) to an arbitrary base pure state
  `ρ : PureState R` on the inner system `R`. (For `R = qubit` this specialises to the aligned tower
  ket `towerKet`; here `R = qubit ⊗ M` carries the block's target-plus-idle module.)
* `mcCtrl_evolvePure_ctrlTower` — the **general multiplexer truth table**: for *any* inner gate
  `G : Evolution R`, the `k`-controlled `Cᵏ(G)` acts on `ctrlTower k c ρ` by applying `G` to the
  base state exactly when *all* `k` controls are set, and as the identity otherwise:
  `Cᵏ(G) (|c⟩ ⊗ ρ) = |c⟩ ⊗ (if ∀ j, c j = 1 then G ρ else ρ)`.
  This is the meaning of "the multiplexer fires iff every control is `|1⟩`", read
  on product inputs; it holds for an arbitrary gate on an arbitrary base system.
* `mcCtrl_pauliXGate_onLeft_evolvePure_ctrlTower` — its **specialisation to a `barencoNCircuit`
  block**: `mcCtrl k (pauliXGate.onLeft M)` flips the target qubit `|i⟩ ↦ |i + 1⟩` iff all `k`
  controls are set and leaves the idle module `M` (state `φ`) untouched:
  `Cᵏ(X) (|c⟩ ⊗ |i⟩ ⊗ φ) = |c⟩ ⊗ |i + (if ∀ j, c j = 1 then 1 else 0)⟩ ⊗ φ`.
  So each internal `Cᵏ(X)` block of the no-work-qubit `Cⁿ(X)` circuit is, on the computational
  basis, exactly the classical multiply-controlled `NOT` on its `k` control wires and target wire —
  the reversible permutation whose bounded `Toffoli` circuit is exhibited in
  `AxQM/Core/McNotCircuitDecomposition.lean`. Matching this action to that circuit (through the
  register bridge) is the block reduction.

## The proof

`mcCtrl_evolvePure_ctrlTower` is an induction on `k` peeling one control at a time, exactly the
shape of the aligned bridge `mcCtrl_pauliXGate_evolvePure_towerKet`.
`mcCtrl (k+1) G = C(mcCtrl k G)` and
`ctrlTower (k+1) c ρ = |c 0⟩ ⊗ ctrlTower k (c ∘ succ) ρ`, so the control-`|0⟩`/`|1⟩` action of
`controlledUnitary` (`controlledUnitary_evolvePure_ketZero` / `_ketOne`) splits the step: on
`c 0 = 0` the gate is the identity and the "all controls set" guard is false; on `c 0 = 1` it
recurses on the tail via the inductive hypothesis, and `Fin.forall_fin_succ` collapses the
`(k+1)`-control guard to the `k`-control one. The base `k = 0` is `mcCtrl 0 G = G` against the
vacuously-true empty guard. The specialisation then feeds `Evolution.onLeft_evolvePure`
(`(X ⊗ 1)(ψ ⊗ φ) = Xψ ⊗ φ`) and `pauliXGate_evolvePure_qubitBasis` (`X|i⟩ = |i+1⟩`) into the guard's
two branches.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {R M : QSystem}

/-- **The control-tower input state** `ctrlTower k c ρ` on `qtower k R`: the `k` computational
control qubits `|c 0⟩ ⊗ |c 1⟩ ⊗ … ⊗ |c (k-1)⟩` (wire `0` outermost) prepended one at a time to a
base pure state `ρ : PureState R` on the inner system. This is the product input on which the
multiplexer `mcCtrl k G` reads out its controlled action (`mcCtrl_evolvePure_ctrlTower`); for
`R = qubit` it is the aligned computational tower ket. -/
def ctrlTower : (k : ℕ) → (Fin k → Fin 2) → PureState R → PureState (qtower k R)
  | 0, _, ρ => ρ
  | k + 1, c, ρ => (qubitBasis (c 0)).tmul (ctrlTower k (fun i => c i.succ) ρ)

/-- Base unfolding of `ctrlTower`: with no control qubits the tower is the base state itself. -/
@[simp] theorem ctrlTower_zero (c : Fin 0 → Fin 2) (ρ : PureState R) :
    ctrlTower 0 c ρ = ρ := rfl

/-- Step unfolding of `ctrlTower`: peel the outermost control wire `|c 0⟩` as a left tensor factor,
leaving the `k`-control tower on the shifted controls. -/
theorem ctrlTower_succ (k : ℕ) (c : Fin (k + 1) → Fin 2) (ρ : PureState R) :
    ctrlTower (k + 1) c ρ = (qubitBasis (c 0)).tmul (ctrlTower k (fun i => c i.succ) ρ) := rfl

/-- **The multiplexer truth table.** For any inner gate `G : Evolution R`, the `k`-controlled gate
`Cᵏ(G) = mcCtrl k G` acts on a control-tower input `ctrlTower k c ρ` by applying `G` to the base
state `ρ` when **every** control is set (`∀ j, c j = 1`) and as the identity otherwise:

`Cᵏ(G) (|c 0⟩ ⊗ … ⊗ |c (k-1)⟩ ⊗ ρ) = |c 0⟩ ⊗ … ⊗ |c (k-1)⟩ ⊗ (if ∀ j, c j = 1 then G ρ else ρ)`.

This is the statement that the multiplexer fires iff all controls are `|1⟩`, read on product
inputs, for an arbitrary gate `G` on an arbitrary base system `R`. Proved by
induction on `k`, peeling one control with `controlledUnitary`'s `|0⟩`/`|1⟩` basis action and
collapsing the `(k+1)`-control guard to the `k`-control one via `Fin.forall_fin_succ`. -/
theorem mcCtrl_evolvePure_ctrlTower (G : Evolution R) :
    ∀ (k : ℕ) (c : Fin k → Fin 2) (ρ : PureState R),
      (mcCtrl k G).evolvePure (ctrlTower k c ρ)
        = ctrlTower k c (if ∀ j, c j = 1 then G.evolvePure ρ else ρ) := by
  intro k
  induction k with
  | zero =>
    intro c ρ
    -- `mcCtrl 0 G ≡ G` and `ctrlTower 0 c ρ ≡ ρ`; the empty-control guard `∀ j : Fin 0, _` is true.
    change G.evolvePure ρ = ctrlTower 0 c _
    rw [ctrlTower_zero, ite_eq_left (fun j => j.elim0)]
  | succ k ih =>
    intro c ρ
    -- Force `mcCtrl (k+1) G ≡ C(mcCtrl k G)` and the register `qtower (k+1) R ≡ qubit ⊗ qtower k R`
    -- so the control-branch lemmas match (cf. `mcCtrl_pauliXGate_evolvePure_towerKet`).
    change (controlledUnitary (mcCtrl k G)).evolvePure (ctrlTower (k + 1) c ρ) = _
    rw [ctrlTower_succ]
    by_cases h0 : c 0 = 1
    · rw [h0, controlledUnitary_evolvePure_ketOne, ih, ctrlTower_succ, h0]
      congr 2
      by_cases hrest : ∀ j : Fin k, c j.succ = 1
      · rw [ite_eq_left hrest, ite_eq_left (Fin.forall_fin_succ.2 ⟨h0, hrest⟩)]
      · rw [ite_eq_right hrest, ite_eq_right (fun h => hrest fun j : Fin k => h j.succ)]
    · have h0' : c 0 = 0 := by omega
      rw [h0', controlledUnitary_evolvePure_ketZero, ctrlTower_succ, h0',
        ite_eq_right (fun h => absurd ((h 0).symm.trans h0') (by decide))]

/-- **A `barencoNCircuit` internal block acts as its classical multiply-controlled `NOT`.** The
block `mcCtrl k (pauliXGate.onLeft M)` (`Cᵏ(X)` with `k` controls, the `X`-target the head of the
inner `qubit ⊗ M`, and the target module `M` idle — the shape of every `Cᵏ(X)` block of the
no-work-qubit `Cⁿ(X)` circuit, `barencoTail`) acts on a control-tower input whose base is a target
basis state tensored with an idle module state `φ : PureState M`: it flips the target
`|i⟩ ↦ |i + 1⟩` when all `k` controls are set and leaves the controls and the idle module `φ` alone:

`Cᵏ(X) (|c⟩ ⊗ |i⟩ ⊗ φ) = |c⟩ ⊗ |i + (if ∀ j, c j = 1 then 1 else 0)⟩ ⊗ φ`.

So on the computational basis each internal `Cᵏ(X)` block **is** the classical multiply-controlled
`NOT` on its `k` control wires and its target wire — the reversible permutation whose bounded
`O(k²)` `Toffoli`/`CNOT`/`NOT` circuit is exhibited in `AxQM/Core/McNotCircuitDecomposition.lean`.
Proved by feeding
`Evolution.onLeft_evolvePure` (`(X ⊗ 1)(ψ ⊗ φ) = Xψ ⊗ φ`) and `pauliXGate_evolvePure_qubitBasis`
(`X|i⟩ = |i+1⟩`) into the two guard branches of `mcCtrl_evolvePure_ctrlTower`. -/
theorem mcCtrl_pauliXGate_onLeft_evolvePure_ctrlTower (k : ℕ) (c : Fin k → Fin 2) (i : Fin 2)
    (φ : PureState M) :
    (mcCtrl k (pauliXGate.onLeft M)).evolvePure (ctrlTower k c ((qubitBasis i).tmul φ))
      = ctrlTower k c ((qubitBasis (i + if ∀ j, c j = 1 then 1 else 0)).tmul φ) := by
  rw [mcCtrl_evolvePure_ctrlTower]
  by_cases h : ∀ j, c j = 1
  · rw [ite_eq_left h, ite_eq_left h, Evolution.onLeft_evolvePure, pauliXGate_evolvePure_qubitBasis]
  · rw [ite_eq_right h, ite_eq_right h, add_zero]

end AxQM
