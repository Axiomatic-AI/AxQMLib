/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.CircuitBudget
import AxQM.Postulates.API.ControlledUnitary
import AxQM.Postulates.API.Evolution

/-!
# The adjoint of a budgeted circuit is budgeted (N&C Problem 4.1, the `U_f†` uncompute)
# The adjoint of a budgeted circuit is budgeted (N&C Problem 4.1, the `U_f†` uncompute)

Nielsen & Chuang, Problem 4.1 builds the compute–phase–uncompute circuit
`C = U_f† ∘ (I_A ⊗ D) ∘ U_f` and counts it as `2T + n` gates: the two Toffoli blocks `U_f`, `U_f†`
(`2T`) and the `n`-gate phase layer `D`. The uncompute step `U_f†` is, in N&C's words, "another `T`
Toffoli gates" — physically because *reversing* a circuit of `T` gates gives a circuit of `T` gates
(a Toffoli/CNOT/NOT is its own inverse, so `U_f†` is literally the same `T` gates in reverse order).

The gate-count predicate `CircuitBudget E t s` (N&C Ex 4.29, `AxQM/Core/CircuitBudget.lean`) needs
the matching **closure**: if `E` is realised by at most `t` `≤ 2`-control gates and `s` single-qubit
gates, so is its adjoint `E†`. This file proves that closure, so that the `2T + n` count can
derive `CircuitBudget U_f† T 0` from the oracle's given `CircuitBudget U_f T 0` — rather than
assuming `U_f†`'s budget as a second, redundant hypothesis (which would be a weakening: `U_f†`'s
count is a *consequence* of `U_f`'s, not an independent given).

## What is formalised

* `CircuitBudget.adjoint` — **the closure**: `CircuitBudget E t s → CircuitBudget E.adjoint t s`,
  by induction on the budget derivation. The reversal is honest per constructor — a controlled
  single-qubit gate `C(V)` becomes `C(V†)` (`ctrlGate ↔ ctrlGateAdj`), a bare single-qubit gate
  `g` becomes `g†`, a sequential composition reverses order (`(E ∘ F)† = F† ∘ E†`, budgets still
  add), register transport commutes with the adjoint, and a `≤ 2`-control block `gs`
  becomes the **reversed block** `gs.reverse` (same length, same valid gates). The gate *counts*
  `(t, s)` are preserved exactly.

The `block` case rests on the classical fact `Concrete.mcNotDenote_mcNotDenote_reverse` (a reversed
multiply-controlled-`NOT` circuit inverts the original, `mcNotDenote gs (mcNotDenote gs.reverse x) =
x`, from `Concrete.mcNot_involutive`), which is pure `Concrete` bit-string combinatorics and is
in `AxQM/Concrete/MultiControlledNotCircuit.lean` beside its `mcNotDenote_*` siblings.

* `controlledUnitary_adjoint`, `unCtrl_adjoint`, `Evolution.onRight_adjoint`,
  `Evolution.congr_adjoint`, `Evolution.adjoint_id` — the **adjoint-distribution helpers** the
  closure fans out over: `C(U)† = C(U†)`, `(unCtrl n E)† = unCtrl n E†`, `(1 ⊗ V)† = 1 ⊗ V†`,
  `(congr e U)† = congr e U†`, `1† = 1`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **The identity gate is self-adjoint**, `1† = 1`. -/
theorem Evolution.adjoint_id : (Evolution.id : Evolution S).adjoint = Evolution.id := by
  apply Evolution.ext
  rw [Evolution.adjoint_op, Evolution.id_op, ← ContinuousLinearMap.star_eq_adjoint, star_one]

/-- **The adjoint distributes over the right-factor lift**, `(1 ⊗ V)† = 1 ⊗ V†`: the adjoint of a
gate acting on the right factor `T` of `S ⊗ T` (identity on `S`) is that factor gate's adjoint,
still on the right. The `.op` is `TensorProduct.mapL 1 V.op` (`Evolution.onRight`/`tmul_op`/
`id_op`), whose adjoint distributes over the tensor (`TensorProduct.adjoint_mapL`), fixing the
self-adjoint
identity slot. -/
theorem Evolution.onRight_adjoint (V : Evolution T) (S : QSystem) :
    (V.onRight S).adjoint = V.adjoint.onRight S := by
  apply Evolution.ext
  have hone : ContinuousLinearMap.adjoint (1 : S.space →L[ℂ] S.space) = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  -- restate at the raw tensor head, where `adjoint`/`mapL` align for `TensorProduct.adjoint_mapL`
  change ContinuousLinearMap.adjoint (TensorProduct.mapL (1 : S.space →L[ℂ] S.space) V.op)
      = TensorProduct.mapL (1 : S.space →L[ℂ] S.space) (ContinuousLinearMap.adjoint V.op)
  rw [TensorProduct.adjoint_mapL, hone]

/-- **The adjoint commutes with register transport**, `(congr e U)† = congr e U†`: transporting `U`
along a system isomorphism `e` and taking the adjoint is the same as taking the adjoint and then
transporting. Holds because transport is conjugation by a `⋆`-algebra equivalence
(`LinearIsometryEquiv.conjStarAlgEquiv`), which preserves `star = adjoint` (`map_star`). -/
theorem Evolution.congr_adjoint (e : S.Iso T) (U : Evolution S) :
    (Evolution.congr e U).adjoint = Evolution.congr e U.adjoint := by
  apply Evolution.ext
  rw [Evolution.adjoint_op, Evolution.congr_op, Evolution.congr_op, Evolution.adjoint_op,
    ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint, map_star]

/-- **The adjoint of the idle wrapping**, `(unCtrl n E)† = unCtrl n E†`: wrapping a gate with `n`
idle control qubits and taking the adjoint equals taking the adjoint and re-wrapping (idle wires are
untouched by the reversal). Induction on `n` via `unCtrl_succ` and `Evolution.onRight_adjoint`. -/
theorem unCtrl_adjoint (n : ℕ) (E : Evolution S) :
    (unCtrl n E).adjoint = unCtrl n E.adjoint := by
  induction n with
  | zero => rfl
  | succ n ih =>
      -- `unCtrl (n+1) E = (unCtrl n E).onRight qubit` definitionally; restate to align the
      -- `Evolution.adjoint` system index with `onRight_adjoint`'s (`rw` needs a syntactic match)
      change ((unCtrl n E).onRight qubit).adjoint = (unCtrl n E.adjoint).onRight qubit
      rw [Evolution.onRight_adjoint, ih]

/-- **The controlled-`U` gate's adjoint is the controlled adjoint**, `C(U)† = C(U†)`
(Nielsen & Chuang §4.3): `(|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U)† = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U†`, since the
rank-one computational-basis projectors and `I` are self-adjoint and the adjoint distributes over
`+` and `TensorProduct.mapL` (`TensorProduct.adjoint_mapL`). This mirrors the `hadjop` step of
`controlledUnitary_op_mem_unitary`. It is what turns a controlled single-qubit gate `C(V)` in a
`CircuitBudget` into `C(V†)` under the adjoint (`ctrlGate ↔ ctrlGateAdj`). -/
theorem controlledUnitary_adjoint (U : Evolution S) :
    (controlledUnitary U).adjoint = controlledUnitary U.adjoint := by
  apply Evolution.ext
  have hone : ContinuousLinearMap.adjoint (1 : S.space →L[ℂ] S.space) = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  -- restate at the raw tensor head `qubit.space ⊗[ℂ] S.space`, where the `+`/`adjoint`/`mapL`
  -- align so the distribution lemmas fire (the composite `(qubit ⊗ S).space` head blocks them)
  change ContinuousLinearMap.adjoint
      (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
          (1 : S.space →L[ℂ] S.space)
        + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
            U.op)
    = TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
          (1 : S.space →L[ℂ] S.space)
      + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
          (ContinuousLinearMap.adjoint U.op)
  simp only [map_add, TensorProduct.adjoint_mapL, InnerProductSpace.adjoint_rankOne, hone]

/-- **The adjoint of a budgeted circuit has the same budget** (Nielsen & Chuang Problem 4.1: the
`U_f†` uncompute costs the same `T` gates as `U_f`). If `E` is realised by at most `t` `≤ 2`-control
gates and `s` single-qubit gates (`CircuitBudget E t s`), then its adjoint `E†` is too:
`CircuitBudget E.adjoint t s`. The counts are preserved *exactly* — reversing a circuit neither adds
nor removes gates.

Proved by induction on the budget derivation, reversing each constructor honestly:

* `block gs` — the adjoint realises the **reversed** gate list `gs.reverse` (same length, same valid
  gates): `U†` sends `|c⟩ ↦ |mcNotDenote gs.reverse c⟩`, obtained from `U|c⟩ = |mcNotDenote gs c⟩`
  by `Evolution.evolvePure_adjoint_evolvePure` and the reverse-inverts identity
  `Concrete.mcNotDenote_mcNotDenote_reverse`.
* `ctrlGate` / `ctrlGateAdj` — a controlled single-qubit gate `C(V)` swaps with its adjoint `C(V†)`
  (`controlledUnitary_adjoint`, `unCtrl_adjoint`, and `Evolution.adjoint_adjoint`).
* `single` / `bare` — a single-qubit gate `g` becomes `g†` (`Evolution.onRight_adjoint`,
  `unCtrl_adjoint`).
* `comp` — `(E ∘ F)† = F† ∘ E†` (`Evolution.adjoint_comp`); the budgets still add (`+` is
  commutative).
* `congr` — transport commutes with the adjoint (`Evolution.congr_adjoint`).
* `mono` — a preserved budget is still `≤` the weakened bound. -/
theorem CircuitBudget.adjoint {E : Evolution S} {t s : ℕ} (h : CircuitBudget E t s) :
    CircuitBudget E.adjoint t s := by
  induction h with
  | block gs U hgs hU =>
      have hb : CircuitBudget U.adjoint gs.reverse.length 0 :=
        CircuitBudget.block gs.reverse U.adjoint
          (fun g hg => hgs g (List.mem_reverse.mp hg))
          (fun c => by
            have hrev : Concrete.mcNotDenote gs (Concrete.mcNotDenote gs.reverse c) = c :=
              Concrete.mcNotDenote_mcNotDenote_reverse gs (fun g hg => (hgs g hg).2) c
            have hval := hU (Concrete.mcNotDenote gs.reverse c)
            simp only [hrev] at hval
            have h2 := congrArg U.adjoint.evolvePure hval
            erw [Evolution.evolvePure_adjoint_evolvePure] at h2
            exact h2.symm)
      rwa [List.length_reverse] at hb
  | ctrlGate g =>
      rw [unCtrl_adjoint, controlledUnitary_adjoint]
      exact CircuitBudget.ctrlGateAdj g
  | ctrlGateAdj g =>
      rw [unCtrl_adjoint, controlledUnitary_adjoint, Evolution.adjoint_adjoint]
      exact CircuitBudget.ctrlGate g
  | single g =>
      rw [Evolution.onRight_adjoint, unCtrl_adjoint]
      exact CircuitBudget.single g.adjoint
  | bare g => exact CircuitBudget.bare g.adjoint
  | comp hE hF ihE ihF =>
      rw [Evolution.adjoint_comp]
      simpa only [Nat.add_comm] using ihF.comp ihE
  | congr e hE ih =>
      rw [Evolution.congr_adjoint]
      exact CircuitBudget.congr e ih
  | mono hE ht hs ih => exact ih.mono ht hs

end AxQM
