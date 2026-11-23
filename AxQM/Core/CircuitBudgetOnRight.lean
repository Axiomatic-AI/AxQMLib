/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.CircuitBudget
import AxQM.Core.PiTensorSuccHead
import AxQM.Postulates.API.TensorPowSplit
import AxQM.Postulates.API.SystemIsoCongrTmul
import AxQM.Postulates.API.LeftPairGate

/-!
# Adding an idle head wire preserves the elementary-gate budget (N&C Ex 4.29 / Prob 4.1)

The elementary-gate budget `CircuitBudget E t s` (`Core/CircuitBudget`) is closed under sequential
composition, register transport, and weakening, but its constructors only *place* a gate on a fixed
register. Assembling a circuit wire-by-wire — the wire-addressed single-qubit gates of Problem 4.1's
phase layer `D`, each a `qtowerSingleWire n i g` peeling an idle head wire off the tower — needs one
more closure: **prepending an idle qubit preserves the budget.** That closure,
`CircuitBudget.onRight`, is the main result of this file.

`CircuitBudget.onRight` — `CircuitBudget E t s → CircuitBudget (E.onRight qubit) t s`. Wrapping a
circuit with one idle head qubit `1 ⊗ E` costs no extra gates. By induction on the budget
derivation: the `single`/`ctrlGate`/`ctrlGateAdj` leaves absorb the extra idle qubit into their
`unCtrl` wrap (`unCtrl_succ`); `comp`/`congr`/`mono` distribute (via `Evolution.onRight_comp`, the
naturality `Evolution.congr_onRight`, and `mono`); and the `block` leaf reindexes its
classical `McNotGate` circuit by the head-wire shift `Concrete.mcNotConsWire` — the new head wire
`0` passes through (`Concrete.mcNotDenote_map_mcNotConsWire`), and the shifted block, transported
across the head split `QSystem.tensorPowSuccHead qubit m : qubit ^⊗ₛ (m+1) ≃ₛ qubit ⊗ qubit ^⊗ₛ m`,
is exactly `U.onRight qubit`.

The proof uses the following general lemmas:
`Evolution.congr_tmul` / `Evolution.congr_onRight` (`AxQM/Postulates/API/SystemIsoCongrTmul.lean`),
`Evolution.evolvePure_congr` (`AxQM/Postulates/API/LeftPairGate.lean`), `QSystem.Iso.symm_symm`
(`AxQM/Postulates/API/SystemIsoComm.lean`), and the `PureState` head-split dictionaries
`tensorPowSuccHead_congr_piTensor` / `tensorPowSuccHead_symm_congr_tmul_piTensor`
(`AxQM/Core/PiTensorSuccHead.lean`, beside their `State` sibling); the `McNotGate` prepend-wire
reindex lemmas are in `AxQM/Concrete/MultiControlledNotCircuit.lean`.
-/

open scoped InnerProductSpace TensorProduct

namespace AxQM

noncomputable section

/-- **Adding an idle head qubit preserves the elementary-gate budget** (the wire-by-wire assembly
closure of N&C Ex 4.29's cost model). If `E` is built from at most `t` `≤ 2`-control gates and `s`
single-qubit gates, then so is the idle-front wrap `1 ⊗ E = E.onRight qubit`: wrapping a circuit
with one untouched head qubit adds no gates,
`CircuitBudget E t s → CircuitBudget (E.onRight qubit) t s`.

Proved by induction on the budget derivation:

* `single` / `ctrlGate` / `ctrlGateAdj`: the extra idle qubit is absorbed into the leaf's own idle
  wrap, `(unCtrl n _).onRight qubit = unCtrl (n+1) _` (`unCtrl_succ`), reproducing the same leaf one
  level up.
* `bare`: a bare gate `g.onRight qubit` is the `single` leaf at zero lifting, `unCtrl 0 g = g`
  (`unCtrl_zero`).
* `comp`: the wrap distributes over composition (`Evolution.onRight_comp`) and the sub-budgets add.
* `congr`: the wrap commutes with the transport by the naturality `Evolution.congr_onRight`, then
  `CircuitBudget.congr` re-applies it.
* `mono`: weaken the wrapped budget.
* `block`: the classical circuit `gs` on `qubit ^⊗ₛ m` is reindexed by the head-wire shift
  `Concrete.mcNotConsWire` to a circuit `gs.map …` on `qubit ^⊗ₛ (m+1)` of the same length; the new
  head wire passes through (`Concrete.mcNotDenote_map_mcNotConsWire`), so the shifted block —
  transported across the head split `QSystem.tensorPowSuccHead qubit m` — is exactly
  `U.onRight qubit`. The `1 ⊗ U` is realised on the computational basis by peeling the head factor
  (`tensorPowSuccHead_congr_piTensor`), letting `U` act on the tail (`Evolution.onRight_evolvePure`,
  `hU`), and reassembling the `cons` (`tensorPowSuccHead_symm_congr_tmul_piTensor`). -/
theorem CircuitBudget.onRight {R : QSystem} {E : Evolution R} {t s : ℕ}
    (h : CircuitBudget E t s) : CircuitBudget (E.onRight qubit) t s := by
  induction h with
  | @block m gs U hgs hU =>
      -- The shifted block, transported across the head split, is `U.onRight qubit`.
      have key : CircuitBudget
          (Evolution.congr (QSystem.tensorPowSuccHead qubit m).symm (U.onRight qubit))
          (gs.map Concrete.mcNotConsWire).length 0 := by
        refine CircuitBudget.block (gs.map Concrete.mcNotConsWire) _ ?_ ?_
        · intro g' hg'
          simp only [List.mem_map] at hg'
          obtain ⟨g, hg, rfl⟩ := hg'
          exact ⟨by rw [Concrete.mcNotConsWire_card]; exact (hgs g hg).1,
            Concrete.mcNotConsWire_target_not_mem (hgs g hg).2⟩
        · intro c'
          erw [Evolution.evolvePure_congr, QSystem.Iso.symm_symm, tensorPowSuccHead_congr_piTensor]
          erw [Evolution.onRight_evolvePure]
          rw [hU (fun j => c' j.succ), tensorPowSuccHead_symm_congr_tmul_piTensor]
          have hmc : Concrete.mcNotDenote (gs.map Concrete.mcNotConsWire) c'
              = Fin.cons (c' 0) (Concrete.mcNotDenote gs fun j => c' j.succ) := by
            conv_lhs => rw [← Fin.cons_self_tail c']
            rw [Concrete.mcNotDenote_map_mcNotConsWire]
            rfl
          congr 1
          funext i
          rw [hmc]
          refine Fin.cases ?_ (fun j => ?_) i <;>
            simp only [Fin.cons_zero, Fin.cons_succ]
      rw [List.length_map] at key
      have hcongr := CircuitBudget.congr (QSystem.tensorPowSuccHead qubit m) key
      rwa [Evolution.congr_congr_symm] at hcongr
  | @single d g =>
      rw [← unCtrl_succ]; exact CircuitBudget.single g
  | @bare g =>
      -- one idle head qubit over a bare gate is the `single` leaf with no lifting (`unCtrl 0`)
      have h := CircuitBudget.single (d := 0) g
      rwa [unCtrl_zero] at h
  | @ctrlGate d n g =>
      rw [← unCtrl_succ]; exact CircuitBudget.ctrlGate g
  | @ctrlGateAdj d n g =>
      rw [← unCtrl_succ]; exact CircuitBudget.ctrlGateAdj g
  | comp _ _ ihE ihF =>
      rw [← Evolution.onRight_comp]; exact CircuitBudget.comp ihE ihF
  | congr e _ ih =>
      rw [Evolution.congr_onRight]; exact CircuitBudget.congr _ ih
  | mono _ ht hs ih =>
      exact ih.mono ht hs

end

end AxQM
