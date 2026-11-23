/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasureObservable
import AxQM.Postulates.API.Associator
import AxQM.Postulates.API.SystemIsoComm
import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract

/-!
# AxQM.Postulates.API — lifting the measurement circuit onto a data register

The operator-measurement circuit `measureObservableCircuit U` (`(H ⊗ 1) · C(U) · (H ⊗ 1)`,
Exercise 4.34) puts its ancilla on the **left** wire and controls the *whole* target register `S`.
When the measured observable is a single-qubit Pauli sitting on **one wire of a multi-qubit data
register** — the situation of Nielsen & Chuang Figure 10.16, where each ancilla's controlled gate
fans out to the code qubits named by the generator — the block must be re-expressed as a circuit
acting only on that wire (plus the ancilla), leaving the other data wires alone. This file provides
that **register-lifting** machinery for a Pauli on the *first* data wire.

## Main result

* `measureObservableCircuit_onLeft` — `measureObservableCircuit (U.onLeft T)
  = congr (assoc qubit S T).symm ((measureObservableCircuit U).onLeft T)`.
  Measuring `U ⊗ 1_T` (the observable `U` on the first block `S`, identity on the rest `T`) with one
  ancilla equals the two-block circuit `measureObservableCircuit U` (ancilla + `S`) run with `T`
  carried along untouched, re-associated from `(qubit ⊗ S) ⊗ T` to the ancilla's native bracketing
  `qubit ⊗ (S ⊗ T)`. This is the identity by which a Figure-10.16 controlled gate targeting one code
  qubit becomes a Figure-10.17 gate on just the ancilla + that qubit (Exercise 10.59); combined with
  the Figure 10.14 / 10.15 atomic identities it compiles the first factor of a stabilizer generator.

## Supporting lemmas

* `Evolution.congr_assoc_symm_onLeft_onLeft` / `controlledUnitary_congr_assoc_symm_onLeft` — the
  per-gate transports: a Hadamard `g ⊗ 1_S ⊗ 1_T` re-associates to `g ⊗ 1_{S⊗T}`, and a controlled
  gate `C(U) ⊗ 1_T` re-associates to `C(U ⊗ 1_T)`.
* `Evolution.congr_assoc_onRight_onRight` — the **onRight mirror** of the first: prepending two idle
  heads `(E.onRight B).onRight A` re-associates to prepending their composite `E.onRight (A ⊗ B)`.
  It is used in `CircuitBudget.onRight_qtower` (`AxQM/Core/CircuitBudgetOnRightTower.lean`).

These rest on the following general facts:
* `Evolution.congr_comp` (system-iso transport is a composition homomorphism) is in
  `AxQM/Postulates/API/SystemIsoComm.lean`, beside the other `Evolution.congr` combinator lemmas.
* the reshaping facts `LinearMap.assocIsometry_conjStarAlgEquiv_mapL_mapL` (associator
  naturality of `mapL`) and `LinearMap.assocIsometry_conjStarAlgEquiv_add` (additivity of the
  associator conjugation) are general inner-product-space facts in
  `ToMathlib/Analysis/InnerProductSpace/PartialTraceAbstract.lean`, beside the
  associator-conjugation
  family (`assocIsometry_conjStarAlgEquiv_toLinearMap`, …).

-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-! ### Per-gate transports across the associator -/

/-- **A left-factor gate re-associates.** A gate `g` on the first factor, embedded as
`(g ⊗ 1_S) ⊗ 1_T` on `(A ⊗ S) ⊗ T`, transports along the associator to `g ⊗ 1_{S⊗T}` on
`A ⊗ (S ⊗ T)`: `congr (assoc A S T).symm ((g.onLeft S).onLeft T) = g.onLeft (S ⊗ T)`. This carries
the ancilla Hadamard `H ⊗ 1` of the measurement block from the two-block bracketing to the ancilla's
native bracketing over the full data register. -/
theorem Evolution.congr_assoc_symm_onLeft_onLeft {A : QSystem} (g : Evolution A) :
    Evolution.congr (QSystem.assoc A S T).symm ((g.onLeft S).onLeft T) = g.onLeft (S ⊗ T) := by
  ext1
  rw [Evolution.congr_op, QSystem.assoc_symm_toIsometry]
  simp only [Evolution.onLeft, Evolution.tmul_op, Evolution.id_op]
  refine (LinearMap.assocIsometry_conjStarAlgEquiv_mapL_mapL g.op 1 1).trans ?_
  exact congrArg (TensorProduct.mapL g.op) TensorProduct.mapL_one

/-- **Associator naturality for the right-factor embedding.** The onRight mirror of
`Evolution.congr_assoc_symm_onLeft_onLeft`. Prepending two idle head systems `B` then `A` to a gate
`E` on `R`, `(E.onRight B).onRight A = 1_A ⊗ (1_B ⊗ E)` on `A ⊗ (B ⊗ R)`, transports along the
associator to prepending their composite in one step, `E.onRight (A ⊗ B) = 1_{A⊗B} ⊗ E` on
`(A ⊗ B) ⊗ R`: `congr (assoc A B R) ((E.onRight B).onRight A) = E.onRight (A ⊗ B)`. Proved at the
operator level: `congr (assoc A B R)` conjugates by `(assocIsometry A B R).symm`, so the nested
right-embedding `mapL 1 (mapL 1 E.op)` re-associates to `mapL (mapL 1 1) E.op`
(`LinearMap.assocIsometry_symm_conjStarAlgEquiv_mapL_mapL`, the `.symm` sibling of the map used by
the onLeft twin), and the two idle factors collapse `mapL 1 1 = 1` (`TensorProduct.mapL_one`). Its
consumer is the tower-prepend budget closure `CircuitBudget.onRight_qtower`
(`Core/CircuitBudgetOnRightTower`), which iterates it to lift a gate budget over an idle qubit
tower. -/
theorem Evolution.congr_assoc_onRight_onRight {R : QSystem} (E : Evolution R) (A B : QSystem) :
    Evolution.congr (QSystem.assoc A B R) ((E.onRight B).onRight A) = E.onRight (A ⊗ B) := by
  ext1
  rw [Evolution.congr_op, QSystem.assoc_toIsometry]
  simp only [Evolution.onRight, Evolution.tmul_op, Evolution.id_op]
  refine (LinearMap.assocIsometry_symm_conjStarAlgEquiv_mapL_mapL 1 1 E.op).trans ?_
  exact congrArg (fun X => TensorProduct.mapL X E.op) TensorProduct.mapL_one

/-- **A controlled gate re-associates onto the first data block.** The controlled-`U` gate with its
target extended by an untouched register, `C(U) ⊗ 1_T` on `(qubit ⊗ S) ⊗ T`, transports along the
associator to the controlled gate whose target is the first block, `C(U ⊗ 1_T)` on
`qubit ⊗ (S ⊗ T)`: `congr (assoc qubit S T).symm ((controlledUnitary U).onLeft T)
= controlledUnitary (U.onLeft T)`. The block-diagonal operator `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U` is split by
`LinearMap.assocIsometry_conjStarAlgEquiv_add` and each summand reshaped by
`LinearMap.assocIsometry_conjStarAlgEquiv_mapL_mapL`. -/
theorem controlledUnitary_congr_assoc_symm_onLeft (U : Evolution S) :
    Evolution.congr (QSystem.assoc qubit S T).symm ((controlledUnitary U).onLeft T)
      = controlledUnitary (U.onLeft T) := by
  ext1
  rw [Evolution.congr_op, QSystem.assoc_symm_toIsometry]
  simp only [Evolution.onLeft, Evolution.tmul_op, Evolution.id_op, controlledUnitary_op]
  refine (congrArg _ (TensorProduct.mapL_add_left _ _ _)).trans
    ((LinearMap.assocIsometry_conjStarAlgEquiv_add _ _).trans ?_)
  exact congrArg₂ (· + ·)
    ((LinearMap.assocIsometry_conjStarAlgEquiv_mapL_mapL _ 1 1).trans
      (congrArg _ TensorProduct.mapL_one))
    (LinearMap.assocIsometry_conjStarAlgEquiv_mapL_mapL _ U.op 1)

/-! ### The measurement circuit lifted onto a data register -/

/-- **The measurement circuit of a first-wire observable, lifted onto the data register.** Measuring
`U ⊗ 1_T` — the observable `U` on the first data block `S`, the identity on the remaining register
`T` — with one ancilla equals the two-block measurement circuit `measureObservableCircuit U` (on the
ancilla and `S`) with `T` carried along untouched, re-bracketed from `(qubit ⊗ S) ⊗ T` to the
ancilla's native `qubit ⊗ (S ⊗ T)`:
`measureObservableCircuit (U.onLeft T)
  = congr (assoc qubit S T).symm ((measureObservableCircuit U).onLeft T)`.

This is how a Nielsen & Chuang Figure-10.16 syndrome block — one ancilla controlling a Pauli that
targets a single code qubit while acting as the identity elsewhere — is expressed as a gate on just
the ancilla and that qubit (the Figure-10.17 form of Exercise 10.59). Combined with the Figure
10.14 / 10.15 atomic identities (`measureObservableCircuit pauliZGate = reversedCNOT`, and the `X`
analogue) it compiles the *first* factor of a generator to its reversed-CNOT form.

Proof: unfold the block `(H ⊗ 1) · C(U) · (H ⊗ 1)`, distribute the `.onLeft T` extension and the
`congr (assoc).symm` transport across the three gates (`Evolution.onLeft_comp`,
`Evolution.congr_comp`), then reshape each gate with its per-gate transport
(`Evolution.congr_assoc_symm_onLeft_onLeft` for the two Hadamards,
`controlledUnitary_congr_assoc_symm_onLeft` for the controlled gate). -/
theorem measureObservableCircuit_onLeft (U : Evolution S) (T : QSystem) :
    measureObservableCircuit (U.onLeft T)
      = Evolution.congr (QSystem.assoc qubit S T).symm ((measureObservableCircuit U).onLeft T) := by
  simp only [measureObservableCircuit]
  rw [← Evolution.onLeft_comp, ← Evolution.onLeft_comp, Evolution.congr_comp, Evolution.congr_comp,
    Evolution.congr_assoc_symm_onLeft_onLeft, controlledUnitary_congr_assoc_symm_onLeft]

/-! ### The measurement circuit lifted onto an interior data wire (the `onRight` transport) -/

/-- **Left-commutation naturality of `mapL`.** Conjugating a right-embedded operator
`1_A ⊗ (Y ⊗ Z)` (with `Y` on the ancilla-like middle factor `B` and `Z` on `C`) by the
left-commutation reshape `leftComm A B C` brings the middle operator `Y` to the front:
`leftComm.conjStarAlgEquiv (mapL X (mapL Y Z)) = mapL Y (mapL X Z)`. The `mapL` companion of the
`leftComm` pure-tensor action lemmas, proved by extensionality on triple tensors through
`conjStarAlgEquiv_apply_apply` and the `leftComm` forward / inverse tensor actions. This is the
reshaping fact that carries a gate on the *right* factor of a data register past a spectator `A` on
the left, the heart of `measureObservableCircuit_onRight`. -/
theorem QSystem.Iso.leftComm_conjStarAlgEquiv_mapL_mapL {A B C : QSystem}
    (X : A.space →L[ℂ] A.space) (Y : B.space →L[ℂ] B.space) (Z : C.space →L[ℂ] C.space) :
    (QSystem.Iso.leftComm A B C).toIsometry.conjStarAlgEquiv
        (TensorProduct.mapL X (TensorProduct.mapL Y Z))
      = TensorProduct.mapL Y (TensorProduct.mapL X Z) := by
  apply ContinuousLinearMap.coe_injective
  refine TensorProduct.ext_threefold' fun b a c => ?_
  rfl

/-- **A middle-factor gate re-associates onto the ancilla wire.** A gate `g` on the middle factor
`B`, embedded as `1_A ⊗ (g ⊗ 1_C)` on `A ⊗ (B ⊗ C)`, transports along `leftComm` to `g ⊗ 1_{A⊗C}`
on `B ⊗ (A ⊗ C)`: `congr (leftComm A B C) ((g.onLeft C).onRight A) = g.onLeft (A ⊗ C)`. This carries
the ancilla Hadamard `H ⊗ 1` of the measurement block from behind a left spectator `A` to the
ancilla's native front position. -/
theorem Evolution.congr_leftComm_onLeft_onRight {A B : QSystem} (g : Evolution B) :
    Evolution.congr (QSystem.Iso.leftComm A B S) ((g.onLeft S).onRight A) = g.onLeft (A ⊗ S) := by
  ext1
  rw [Evolution.congr_op]
  simp only [Evolution.onLeft, Evolution.onRight, Evolution.tmul_op, Evolution.id_op]
  rw [QSystem.Iso.leftComm_conjStarAlgEquiv_mapL_mapL]
  exact congrArg (TensorProduct.mapL g.op) TensorProduct.mapL_one

/-- **A controlled gate re-associates onto an interior data block.** The controlled-`U` gate with a
spectator register `A` on the left, `1_A ⊗ C(U)` on `A ⊗ (qubit ⊗ S)`, transports along `leftComm`
to the controlled gate whose target extends over `A`, `C(1_A ⊗ U) = C(U.onRight A)` on
`qubit ⊗ (A ⊗ S)`: `congr (leftComm A qubit S) ((controlledUnitary U).onRight A)
= controlledUnitary (U.onRight A)`. The block-diagonal operator `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U`, embedded
under `1_A ⊗ ·`, is split by `mapL_add_right` / additivity of the conjugation and each summand
reshaped by `leftComm_conjStarAlgEquiv_mapL_mapL`. -/
theorem controlledUnitary_congr_leftComm_onRight (U : Evolution S) (A : QSystem) :
    Evolution.congr (QSystem.Iso.leftComm A qubit S) ((controlledUnitary U).onRight A)
      = controlledUnitary (U.onRight A) := by
  ext1
  rw [Evolution.congr_op]
  simp only [Evolution.onRight, Evolution.tmul_op, Evolution.id_op, controlledUnitary_op]
  refine (congrArg _ (TensorProduct.mapL_add_right _ _ _)).trans
    ((map_add (QSystem.Iso.leftComm A qubit S).toIsometry.conjStarAlgEquiv _ _).trans ?_)
  exact congrArg₂ (· + ·)
    ((QSystem.Iso.leftComm_conjStarAlgEquiv_mapL_mapL _ _ _).trans
      (congrArg _ TensorProduct.mapL_one))
    (QSystem.Iso.leftComm_conjStarAlgEquiv_mapL_mapL _ _ _)

/-- **The measurement circuit of an interior-wire observable, lifted onto the data register.**
Measuring `1_A ⊗ U` — the identity on a spectator register `A`, the observable `U` on the block `S`
to its right — with one ancilla equals the two-block measurement circuit
`measureObservableCircuit U` (on the ancilla and `S`) with `A` carried along untouched, re-bracketed
from `A ⊗ (qubit ⊗ S)` to the ancilla's native `qubit ⊗ (A ⊗ S)` by the left-commutation reshape:
`measureObservableCircuit (U.onRight A)
  = congr (leftComm A qubit S) ((measureObservableCircuit U).onRight A)`.

This is the `onRight` companion of `measureObservableCircuit_onLeft`: where `onLeft` lifts a Pauli
on the *first* data wire, this lifts one on an *interior* wire — a stabilizer generator's factor
sitting past the wires that precede it (Nielsen & Chuang Figure 10.16 → 10.17). Together with the
Figure 10.14 / 10.15 atomic identities it compiles any single factor of a generator to its
reversed-CNOT form, regardless of which data wire it acts on.

Proof: unfold the block `(H ⊗ 1) · C(U) · (H ⊗ 1)`, distribute the `.onRight A` extension
(`Evolution.onRight_comp`) and the `congr (leftComm)` transport (`Evolution.congr_comp`) across the
three gates, then reshape each gate with its per-gate transport
(`Evolution.congr_leftComm_onLeft_onRight` for the two ancilla Hadamards,
`controlledUnitary_congr_leftComm_onRight` for the controlled gate). -/
theorem measureObservableCircuit_onRight (U : Evolution S) (A : QSystem) :
    measureObservableCircuit (U.onRight A)
      = Evolution.congr (QSystem.Iso.leftComm A qubit S)
          ((measureObservableCircuit U).onRight A) := by
  simp only [measureObservableCircuit]
  rw [← Evolution.onRight_comp, ← Evolution.onRight_comp, Evolution.congr_comp,
    Evolution.congr_comp, Evolution.congr_leftComm_onLeft_onRight,
    controlledUnitary_congr_leftComm_onRight]

/-! ### The measurement circuit lifted onto an interior data wire with spectators on both sides -/

/-- **The measurement circuit of a both-spectator interior-wire observable, lifted onto the data
register.** Measuring `1_A ⊗ U ⊗ 1_B` — the observable `U` on a data block flanked by a spectator
register `A` on its left *and* a spectator register `B` on its right — with one ancilla equals the
two-block measurement circuit `measureObservableCircuit U` (on the ancilla and `U`'s block) with `A`
and `B` carried along untouched, re-bracketed to the ancilla's native front:
`measureObservableCircuit ((U.onLeft B).onRight A) = congr (leftComm A qubit (S ⊗ B))
  ((congr (assoc qubit S B).symm ((measureObservableCircuit U).onLeft B)).onRight A)`.

This is the genuine **interior-wire** lift — the composite `onRight ∘ onLeft` that
`measureObservableCircuit_onLeft` (a first wire, spectator only on the right) and
`measureObservableCircuit_onRight` (a wire with a spectator only on the left) do not individually
reach. Every code qubit strictly between the first and the last of a Nielsen & Chuang Figure-10.16
data register is exactly such a both-spectator factor. Proof: strip the right spectator `B` with
`measureObservableCircuit_onLeft`, then the left spectator `A` with
`measureObservableCircuit_onRight` — the two one-sided lifts compose with no new physical content,
only nested reshaping. -/
theorem measureObservableCircuit_onMiddle (U : Evolution S) (A B : QSystem) :
    measureObservableCircuit ((U.onLeft B).onRight A)
      = Evolution.congr (QSystem.Iso.leftComm A qubit (S ⊗ B))
          ((Evolution.congr (QSystem.assoc qubit S B).symm
            ((measureObservableCircuit U).onLeft B)).onRight A) := by
  rw [measureObservableCircuit_onRight, measureObservableCircuit_onLeft]

end AxQM
