/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlBranchExt
import AxQM.Postulates.API.ToffoliHadamard

/-!
# The Barenco no-work-qubit reduction for multiply-controlled gates (Nielsen & Chuang §4.3)

Nielsen & Chuang's Figure 4.8 builds the *doubly*-controlled gate `C²(V²)` from single-qubit
controlled `V`, `V†` and two `CNOT`s (Exercise 4.21). Exercise 4.28 asks for the analogous
construction of an `n`-control gate `Cⁿ(V²)` **using no work qubits**. The key step, generalising
Figure 4.8, expresses an `(m+1)`-control gate on `V²` in terms of

* the single-qubit controlled `V` and `V†` (conditioned on the *innermost* control),
* two `m`-controlled `NOT`s (`Cᵐ(X)`, conditioned on the *outer* `m` controls, targeting the
  innermost control), and
* one `m`-controlled `V` (`Cᵐ(V)`, conditioned on the outer `m` controls, targeting the target).

Iterating the step (each level introduces a fresh square root `Vⱼ² = Vⱼ₋₁`) unfolds `Cⁿ(U)` all the
way down to single-qubit controlled gates and multiply-controlled `NOT`s — the no-work-qubit
construction of Exercise 4.28 (assembled, for `n = 5`, in `NC/Ch4/Exercise4_28.lean`).

## What is formalised

* `qtower n S` — the register `qubitⁿ ⊗ S`: `n` control qubits wrapping an inner system `S`.
* `mcCtrl n E` / `unCtrl n E` — `E : Evolution S` wrapped by `n` outer control qubits, **either**
  each *controlling* `E` (`mcCtrl`, so `E` fires iff all `n` controls are `|1⟩` — the `Cⁿ`
  multiplexer) **or** each *idle* (`unCtrl`, so `E` fires unconditionally). Their monoid laws
  (`mcCtrl_comp`, `unCtrl_comp`, `unCtrl_id`) and the recursion identity `mcCtrl_succ`.
* `qtower_qubit_comm`, `controlledUnitary_cast`, `mcCtrl_succ_inner` — the register-reassociation
  lemmas an *iterated* reduction needs: `qtower m (qubit ⊗ S) = qtower (m+1) S` and, on top of it,
  the one honest cast `mcCtrl (k+1) E = mcCtrl k (C(E))` moving a control from outside `mcCtrl` into
  a `controlledUnitary` (used by the `Cⁿ(U)`/`Cⁿ(X)` unfoldings of Exercises 4.28–4.30).
* `barencoReductionCircuit k Vg` — the right-hand side of the reduction on
  `qtower k (qubit ⊗ M)` (inner = control ⊗ target-module `M`, `Vg : Evolution M`): the ordered
  composition `Cᵏ(V) · Cᵏ(X) · C(V†) · Cᵏ(X) · C(V)`.
* `barencoTail k Vg` — the multiplexer-free tail `Cᵏ(X) · C(V†) · Cᵏ(X) · C(V)` of one layer, and
  `barencoReductionCircuit_eq_mux_comp_tail` splitting a layer as its leading `Cᵏ(V)` multiplexer ·
  tail: the shape an iterated reduction (Ex. 4.28–4.30) stacks, each multiplexer expanded.
* `mcCtrl_controlledUnitary_sq` — **the reduction:** `Cᵏ⁺¹(V²) = barencoReductionCircuit k Vg`,
  i.e. `mcCtrl k (C(V²)) = barencoReductionCircuit k V`. This is the heart of Exercises
  4.28–4.30; for `k = 1` it is exactly Figure 4.8 / Exercise 4.21.

## Design notes

* **Adjacency, not associators.** Taking the inner system as `qubit ⊗ M` (innermost control ⊗
  target-module) keeps every gate of the reduction adjacent: the single-qubit `C(V)`/`C(V†)` live on
  the inner `qubit ⊗ M`, the `Cᵏ(X)` flips the innermost control via `pauliXGate.onLeft M`, and the
  `Cᵏ(V)` skips the innermost control via `Vg.onRight qubit` — all placed by `mcCtrl`/`unCtrl`, so
  no associator or `SWAP` is ever needed. Letting `M` be an *arbitrary* system (not just one qubit)
  is what lets the caller recurse: the `Cᵏ(V)` term is itself a `mcCtrl` of a `V.onRight …`, a
  square, ready for the next reduction with a fresh root.
* **Proof of the reduction (induction on `k`).** `controlBranch_evolution_ext` peels the outer
  controls one at a time. The base `k = 0` is the two-qubit Figure-4.8 identity (casework on the one
  control, with `V† V = 1`, `V V† = 1`, `V(Vψ) = V²ψ`). The step conditions everything on the new
  outer qubit: with the qubit `|0⟩` the two `mᵏ` multiplexers are idle and the two idle `C(V†)`,
  `C(V)` cancel (`V† V = 1`, via `unCtrl_comp` / `controlledUnitary_comp` / `controlledUnitary_id`);
  with the qubit `|1⟩` every factor acts by its `mcCtrl k`/`unCtrl k` version and the goal is
  exactly the inductive hypothesis.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S M : QSystem}

/-! ### The control register and its two wrappings -/

/-- **The control register** `qtower n S = qubitⁿ ⊗ S`: `n` control qubits (added on the left, one
at a time) wrapping an inner system `S`. -/
def qtower : ℕ → QSystem → QSystem
  | 0, S => S
  | (n + 1), S => qubit ⊗ qtower n S

/-- **The `n`-controlled multiplexer** `mcCtrl n E = Cⁿ(E)`: the gate `E : Evolution S` wrapped by
`n` control qubits, applied to `S` exactly when *all* `n` controls are `|1⟩`. Built by iterating the
single control `controlledUnitary`; `mcCtrl 0 E = E` and `mcCtrl (n+1) E = C(mcCtrl n E)`. -/
def mcCtrl : (n : ℕ) → Evolution S → Evolution (qtower n S)
  | 0, E => E
  | (n + 1), E => controlledUnitary (mcCtrl n E)

/-- **The idle wrapping** `unCtrl n E`: the gate `E : Evolution S` wrapped by `n` *idle* qubits, so
`E` is applied to `S` regardless of the `n` qubits. Built by iterating the idle wrap
`Evolution.onRight`; `unCtrl 0 E = E` and `unCtrl (n+1) E` wraps `unCtrl n E` with an idle qubit. -/
def unCtrl : (n : ℕ) → Evolution S → Evolution (qtower n S)
  | 0, E => E
  | (n + 1), E => (unCtrl n E).onRight qubit

@[simp] theorem mcCtrl_zero (E : Evolution S) : mcCtrl 0 E = E := rfl

@[simp] theorem mcCtrl_succ (n : ℕ) (E : Evolution S) :
    mcCtrl (n + 1) E = controlledUnitary (mcCtrl n E) := rfl

@[simp] theorem unCtrl_zero (E : Evolution S) : unCtrl 0 E = E := rfl

@[simp] theorem unCtrl_succ (n : ℕ) (E : Evolution S) :
    unCtrl (n + 1) E = (unCtrl n E).onRight qubit := rfl

/-! ### Monoid laws of the wrappings -/

/-- **`Cⁿ` is a homomorphism:** `Cⁿ(A) Cⁿ(B) = Cⁿ(A B)` — stacking two `n`-controlled gates sharing
the controls is the `n`-controlled gate of the composite (`controlledUnitary_comp` per level). -/
theorem mcCtrl_comp (n : ℕ) (A B : Evolution S) :
    (mcCtrl n A).comp (mcCtrl n B) = mcCtrl n (A.comp B) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mcCtrl_succ]
    exact (controlledUnitary_comp _ _).trans (congrArg controlledUnitary ih)

/-- **The idle wrapping is a homomorphism:** `unCtrl n A · unCtrl n B = unCtrl n (A B)`. -/
theorem unCtrl_comp (n : ℕ) (A B : Evolution S) :
    (unCtrl n A).comp (unCtrl n B) = unCtrl n (A.comp B) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [unCtrl_succ]
    exact (Evolution.onRight_comp _ _ (unCtrl n A) (unCtrl n B)).trans
      (congrArg (Evolution.onRight · qubit) ih)

/-- **The idle wrapping preserves the identity:** `unCtrl n 1 = 1`. -/
theorem unCtrl_id (n : ℕ) : unCtrl n (Evolution.id : Evolution S) = Evolution.id := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [unCtrl_succ]
    rw [ih]
    exact Evolution.id_onRight qubit (qtower n S)

/-! ### Register reassociation

These identify the tower registers that an *iterated* Barenco reduction (the `Cⁿ(U)` no-work-qubit
unfoldings of Exercises 4.28–4.30) walks through: peeling a control turns the target module `M` into
`qubit ⊗ M`, so the surviving multiplexer lives on `qtower k (qubit ⊗ (qubit ⊗ M))` while its parent
lives on `qtower (k+1) (qubit ⊗ M)` — the same register, but only propositionally (`qtower` recurses
on its first argument, so it does not unfold for symbolic `k`). -/

/-- **Pushing a control from the target into the tower.** `qtower m (qubit ⊗ S) = qtower (m+1) S`:
both are the right-nested tower of `m + 1` control qubits over `S`. This is *not* definitional
(`qtower` recurses on its first argument, so `qtower m (qubit ⊗ S)` does not unfold for symbolic
`m`); it is the propositional equality that lets an iterated Barenco reduction move a peeled control
from the target module back out to a fresh control qubit. -/
theorem qtower_qubit_comm (m : ℕ) (S : QSystem) :
    qtower m (qubit ⊗ S) = qtower (m + 1) S := by
  induction m with
  | zero => rfl
  | succ k ih => exact congrArg (qubit ⊗ ·) ih

/-- Transporting a gate along a system equality commutes with adding a control: casting the target
system of `x` and then controlling equals controlling and then casting the (control-wrapped) target.
The bookkeeping lemma behind `mcCtrl_succ_inner`. -/
theorem controlledUnitary_cast {R₁ R₂ : QSystem} (hq : R₁ = R₂) (x : Evolution R₁) :
    controlledUnitary (cast (congrArg Evolution hq) x)
      = cast (congrArg Evolution (congrArg (qubit ⊗ ·) hq)) (controlledUnitary x) := by
  subst hq
  rfl

/-- **Moving a control from outside `mcCtrl` into a `controlledUnitary`.** The `(k+1)`-fold
multiplexer of `E` equals the `k`-fold multiplexer of the *single*-controlled `C(E)`, once the
registers are identified by `qtower_qubit_comm`. Both sides are `C^(k+1)(E)`; the equality is stated
with the honest cast because the two presentations live on the propositionally-equal registers
`qtower (k+1) S` and `qtower k (qubit ⊗ S)`. This is the one cast an iterated no-work-qubit
reduction (Exercises 4.28–4.30) needs to re-expose a peeled multiplexer as a square for the next
step. -/
theorem mcCtrl_succ_inner (k : ℕ) (E : Evolution S) :
    mcCtrl (k + 1) E
      = cast (congrArg Evolution (qtower_qubit_comm k S)) (mcCtrl k (controlledUnitary E)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [mcCtrl_succ, ih, mcCtrl_succ]
    exact controlledUnitary_cast (qtower_qubit_comm k S) (mcCtrl k (controlledUnitary E))

/-! ### The reduction -/

/-- **The Figure-4.8 reduction circuit** for `Cᵏ⁺¹(V²)` on `qtower k (qubit ⊗ M)` (inner = innermost
control ⊗ target-module `M`, with `Vg : Evolution M`). Reading right to left (the rightmost acts
first), the five gates are: `C(V)` on the inner control; `Cᵏ(X)` on the outer `k` controls targeting
the inner control (`pauliXGate.onLeft M`); `C(V†)` on the inner control; `Cᵏ(X)` again; and `Cᵏ(V)`
on the outer `k` controls targeting the target-module, skipping the inner control (`Vg.onRight
qubit`). The single-qubit `C(V)`/`C(V†)` are idle over the outer controls (`unCtrl`); the `Cᵏ(X)`,
`Cᵏ(V)` are controlled by them (`mcCtrl`). -/
def barencoReductionCircuit (k : ℕ) (Vg : Evolution M) : Evolution (qtower k (qubit ⊗ M)) :=
  (mcCtrl k (Vg.onRight qubit)).comp
    ((mcCtrl k (pauliXGate.onLeft M)).comp
      ((unCtrl k (controlledUnitary Vg.adjoint)).comp
        ((mcCtrl k (pauliXGate.onLeft M)).comp
          (unCtrl k (controlledUnitary Vg)))))

/-- **The tail of one Barenco reduction layer** on `qtower k (qubit ⊗ M)`: everything of
`barencoReductionCircuit k Vg` *after* the leading `Cᵏ(V)` multiplexer, i.e.
`Cᵏ(X) · C(V†) · Cᵏ(X) · C(V)` — two multiply-controlled `NOT`s (`mcCtrl k (pauliXGate.onLeft M)`)
and the two idle single-qubit-controlled gates `C(V†)`, `C(V)` (`unCtrl k (controlledUnitary …)`).
Factoring the tail out lets an iterated reduction (the `Cⁿ(U)` no-work-qubit unfoldings of Exercises
4.28–4.30) be written as a nested stack of layers whose leading multiplexers have been recursively
expanded, matching the reduction proof exactly. -/
def barencoTail (k : ℕ) (Vg : Evolution M) : Evolution (qtower k (qubit ⊗ M)) :=
  (mcCtrl k (pauliXGate.onLeft M)).comp
    ((unCtrl k (controlledUnitary Vg.adjoint)).comp
      ((mcCtrl k (pauliXGate.onLeft M)).comp
        (unCtrl k (controlledUnitary Vg))))

/-- One Barenco layer splits as its leading multiplexer `Cᵏ(V)` (`mcCtrl k (Vg.onRight qubit)`)
composed with its tail (`barencoTail k Vg`). Definitional. -/
theorem barencoReductionCircuit_eq_mux_comp_tail (k : ℕ) (Vg : Evolution M) :
    barencoReductionCircuit k Vg = (mcCtrl k (Vg.onRight qubit)).comp (barencoTail k Vg) :=
  rfl

/-- **Nielsen & Chuang, Exercise 4.28 (the reduction step).** The `(k+1)`-control gate on `V²`
decomposes, with **no work qubits**, into single-qubit controlled `V`/`V†` and multiply-controlled
gates:
`Cᵏ⁺¹(V²) = Cᵏ(V) · Cᵏ(X) · C(V†) · Cᵏ(X) · C(V)`,
i.e. `mcCtrl k (controlledUnitary (V·V)) = barencoReductionCircuit k V`. `V†` is the genuine adjoint
gate `V.adjoint`, and `M` (the target-module) is arbitrary, so a caller reduces the `Cᵏ(V)` term
again with a fresh square root of `V`. For `k = 1` this is exactly Figure 4.8 (Exercise 4.21).

Proved by induction on `k` via `controlBranch_evolution_ext`. Base `k = 0`: the two-qubit identity
by casework on the single control (`V† V = 1`, `V V† = 1`, `V(Vψ) = V²ψ`). Step: casework on the new
outer control — `|0⟩` collapses (the idle `C(V†) C(V) = C(V† V) = 1` cancels, the multiplexers
idle), `|1⟩` reduces to the inductive hypothesis. -/
theorem mcCtrl_controlledUnitary_sq (k : ℕ) (Vg : Evolution M) :
    mcCtrl k (controlledUnitary (Vg.comp Vg)) = barencoReductionCircuit k Vg := by
  induction k with
  | zero =>
    apply controlBranch_evolution_ext
    intro i ψ
    -- `qtower` normalises the register type so `evolvePure_comp` can spread the composition.
    simp only [barencoReductionCircuit, mcCtrl_zero, unCtrl_zero, qtower, Evolution.evolvePure_comp]
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue,
        controlledUnitary_evolvePure_ketZero, controlledUnitary_evolvePure_ketOne,
        Evolution.onLeft_evolvePure, Evolution.onRight_evolvePure,
        pauliXGate_evolvePure_qubitBasis, Fin.reduceAdd,
        Evolution.evolvePure_adjoint_evolvePure', Evolution.evolvePure_comp]
  | succ k ih =>
    -- The two idle single-qubit gates cancel when the new outer control is `|0⟩`.
    have hcancel : (unCtrl k (controlledUnitary Vg.adjoint)).comp
        (unCtrl k (controlledUnitary Vg)) = Evolution.id := by
      rw [unCtrl_comp, controlledUnitary_comp, Evolution.adjoint_comp_self', controlledUnitary_id,
        unCtrl_id]
    apply controlBranch_evolution_ext
    intro i ψ
    fin_cases i
    · -- outer control `|0⟩`: everything collapses to the identity.
      simp only [barencoReductionCircuit, qtower, mcCtrl_succ, unCtrl_succ,
        Evolution.evolvePure_comp, Fin.mk_zero, Fin.isValue, controlledUnitary_evolvePure_ketZero,
        Evolution.onRight_evolvePure]
      rw [← Evolution.evolvePure_comp, hcancel, Evolution.id_evolvePure]
    · -- outer control `|1⟩`: reduces to the inductive hypothesis.
      simp only [barencoReductionCircuit, qtower, mcCtrl_succ, unCtrl_succ,
        Evolution.evolvePure_comp, Fin.mk_one, Fin.isValue, controlledUnitary_evolvePure_ketOne,
        Evolution.onRight_evolvePure]
      rw [ih]
      simp only [barencoReductionCircuit, Evolution.evolvePure_comp]

end AxQM
