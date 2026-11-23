/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliYGate
import AxQM.Postulates.API.CnotPauliPropagation

/-!
# AxQM.Postulates.API — CNOT involution and the CNOT–`Y` propagation rules

The `Y` companions of `AxQM/Postulates/API/CnotPauliPropagation.lean` (which handles the
`X`/`Z` rules), plus the **CNOT involution** — the two ingredients, beyond the
`X`/`Z` propagation rules, needed to assemble the eight conjugation identities of Nielsen & Chuang
**Exercise 4.31** in `AxQM/NC/Ch4/Exercise4_31.lean`.

## What is formalised

* `cnotGate_comp_cnotGate` — **CNOT is an involution**: `CNOT · CNOT = 1`.  (`CNOT` is Hermitian and
  unitary, so it is its own inverse.)  This is what turns each Clifford *commutation* rule
  `CNOT · P = P' · CNOT` into the *conjugation* identity `CNOT · P · CNOT = P'` of the exercise:
  `CNOT·P·CNOT = P'·CNOT·CNOT = P'`.  Proved on the computational basis, where
  `CNOT²|c,t⟩ = |c, (t ⊕ c) ⊕ c⟩ = |c,t⟩`.
* `Evolution.comp_comp_self_of_comm` — the general `Evolution`-monoid fact that packages that step:
  from `C · P = Q · C` and `C · C = 1`, conclude `C · P · C = Q`.  Each of the six identities
  of Exercise 4.31 is one application of it to a propagation rule and `cnotGate_comp_cnotGate`.
* `cnotGate_comp_pauliYGate_onLeft` — **`Y` on the control copies an `X` to the target through
  `CNOT`:** `CNOT · (Y ⊗ 1) = (Y ⊗ 1)·(1 ⊗ X)·CNOT`.  (`Y₁ = i X₁ Z₁`: the `X₁` copies to the
  target as for `cnotGate_comp_pauliXGate_onLeft`, the `Z₁` commutes, and the phase `i·(-1)ᶜ` is
  carried unchanged.)
* `cnotGate_comp_pauliYGate_onRight` — **`Y` on the target picks up a control-`Z` through `CNOT`:**
  `CNOT · (1 ⊗ Y) = (Z ⊗ 1)·(1 ⊗ Y)·CNOT`.  (`Y₂ = i X₂ Z₂`: the `Z₂` copies back to the control as
  a `Z₁` as for `cnotGate_comp_pauliZGate_onRight`, while the `X₂` and the phase stay on the target,
  leaving a `Y₂`.)

## Design notes

* **Statement shape (fidelity).**  Each rule is a genuine equality of the gate `Evolution`s
  (Postulate 5), holding on *every* input, in the commutation form `CNOT · P = P' · CNOT` — the form
  from which the conjugation identities follow with one use of `cnotGate_comp_cnotGate`.
* **Proof.**  The two `Y` rules are verified on the four computational-basis inputs
  (`twoQubit_evolution_ext`), dropping to the vector level (`PureState.ext`) because `Y` carries the
  phase `i·(-1)ⁱ`; the phase is moved through `CNOT` with the raw-tensor-head homogeneity lemma
  `cnotGate_op_smul`, exactly as in the `Z` rules of `CnotPauliPropagation.lean`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **CNOT is an involution:** `CNOT · CNOT = 1`.  `CNOT` is Hermitian and unitary, hence its own
inverse; on the computational basis `CNOT²|c,t⟩ = |c, (t ⊕ c) ⊕ c⟩ = |c,t⟩` since `c ⊕ c = 0`.  This
is the ingredient that turns a Clifford commutation rule `CNOT · P = P' · CNOT` into the conjugation
identity `CNOT · P · CNOT = P'` (Nielsen & Chuang Exercise 4.31). -/
theorem cnotGate_comp_cnotGate : cnotGate.comp cnotGate = Evolution.id := by
  apply twoQubit_evolution_ext
  intro c t
  rw [Evolution.evolvePure_comp, cnotGate_evolvePure_qubitBasis, cnotGate_evolvePure_qubitBasis,
    Evolution.id_evolvePure, add_assoc, show (c + c : Fin 2) = 0 from by fin_cases c <;> rfl,
    add_zero]

/-- **Conjugation by an involution turns a commutation rule into an equality.**  If `C` is an
involution (`C · C = 1`) and `P` commutes past `C` to `Q` (`C · P = Q · C`), then conjugating `P` by
`C` gives `Q`: `C · P · C = Q`.  (`C·P·C = (C·P)·C = (Q·C)·C = Q·(C·C) = Q·1 = Q`.)  A general
`Evolution`-monoid fact, placed beside `cnotGate_comp_cnotGate` because the two together turn each
Clifford *commutation* rule `C · P = P' · C` into the *conjugation* identity `C · P · C = P'` of
Nielsen & Chuang Exercise 4.31 — the shared step behind all six theorems there. -/
theorem Evolution.comp_comp_self_of_comm {S : QSystem} {C P Q : Evolution S}
    (hcomm : C.comp P = Q.comp C) (hinv : C.comp C = Evolution.id) :
    C.comp (P.comp C) = Q := by
  rw [← Evolution.comp_assoc, hcomm, Evolution.comp_assoc, hinv, Evolution.comp_id]

/-- **Conjugation by an involution preserves commutativity.** If `C` is an involution
(`C · C = 1`) and `g`, `h` are its conjugates of two commuting elements — `g · C = C · P`,
`h · C = C · Q` with `P · Q = Q · P` — then `g` and `h` commute: `g · h = h · g`. Since
`g = C·P·C` and `h = C·Q·C` (`comp_comp_self_of_comm`), `g·h = C·(P·Q)·C = C·(Q·P)·C = h·g`.
The Clifford/stabilizer companion of `comp_comp_self_of_comm`: a conjugated stabilizer generating
set inherits the commutativity of the generators it is conjugated from. -/
theorem Evolution.comm_of_conj_comm {S : QSystem} {C g h P Q : Evolution S}
    (hinv : C.comp C = Evolution.id) (hcg : g.comp C = C.comp P) (hch : h.comp C = C.comp Q)
    (hPQ : P.comp Q = Q.comp P) : g.comp h = h.comp g := by
  have keyGH : (g.comp h).comp C = C.comp (P.comp Q) := by
    rw [Evolution.comp_assoc, hch, ← Evolution.comp_assoc, hcg, Evolution.comp_assoc]
  have keyHG : (h.comp g).comp C = C.comp (Q.comp P) := by
    rw [Evolution.comp_assoc, hcg, ← Evolution.comp_assoc, hch, Evolution.comp_assoc]
  rw [← Evolution.comp_comp_self_of_comm keyGH.symm hinv,
    ← Evolution.comp_comp_self_of_comm keyHG.symm hinv, hPQ]

/-- **Conjugation by an involution preserves the involution property.** If `C` is an involution
(`C · C = 1`) and `g` is its conjugate of an involution — `g · C = C · P` with `P · P = 1` — then
`g` is an involution: `g · g = 1`. Since `g = C·P·C` (`comp_comp_self_of_comm`),
`g·g = C·P²·C = C·C = 1`. A self-inverse unitary is Hermitian, so a conjugated Pauli-involution
stabilizer generator is a genuine `±1`-outcome observable. -/
theorem Evolution.comp_self_of_conj_comp_self {S : QSystem} {C g P : Evolution S}
    (hinv : C.comp C = Evolution.id) (hcg : g.comp C = C.comp P)
    (hP : P.comp P = Evolution.id) : g.comp g = Evolution.id := by
  have key : (g.comp g).comp C = C.comp (P.comp P) := by
    rw [Evolution.comp_assoc, hcg, ← Evolution.comp_assoc, hcg, Evolution.comp_assoc]
  rw [← Evolution.comp_comp_self_of_comm key.symm hinv, hP, Evolution.id_comp, hinv]

/-- **`Y` on the control copies an `X` to the target through `CNOT`:**
`CNOT · (Y ⊗ 1) = (Y ⊗ 1)·(1 ⊗ X)·CNOT`.  Writing `Y = iXZ`, the `X` part copies to the target as
for `cnotGate_comp_pauliXGate_onLeft` and the `Z` part commutes with `CNOT`, so pushing `Y` on the
control to the output side leaves a `Y` on the control and an `X` on the target (the phase `i·(-1)ᶜ`
rides along).  A basis-state verification via `twoQubit_evolution_ext`, descending to the vector
level for the phase. -/
theorem cnotGate_comp_pauliYGate_onLeft :
    cnotGate.comp (pauliYGate.onLeft qubit)
      = ((pauliYGate.onLeft qubit).comp (pauliXGate.onRight qubit)).comp cnotGate := by
  apply twoQubit_evolution_ext
  intro c t
  apply PureState.ext
  rw [Evolution.evolvePure_vec, Evolution.evolvePure_vec, PureState.tmul_vec]
  erw [Evolution.comp_op, ContinuousLinearMap.comp_apply]
  rw [Evolution.onLeft_op_tmul,
    pauliYGate_op_apply_qubitBasis, ← TensorProduct.smul_tmul', cnotGate_op_smul,
    cnotGate_op_qubitBasisVec_tmul]
  erw [Evolution.comp_op, ContinuousLinearMap.comp_apply]
  rw [cnotGate_op_qubitBasisVec_tmul]
  erw [Evolution.comp_op, ContinuousLinearMap.comp_apply]
  rw [Evolution.onRight_op_tmul, pauliXGate_op_apply_qubitBasis, Evolution.onLeft_op_tmul,
    pauliYGate_op_apply_qubitBasis, ← TensorProduct.smul_tmul']
  congr 2
  rw [add_assoc]

/-- **`Y` on the target picks up a control-`Z` through `CNOT`:**
`CNOT · (1 ⊗ Y) = (Z ⊗ 1)·(1 ⊗ Y)·CNOT`.  Writing `Y = iXZ`, the `Z` part copies back to the control
as a `Z₁` (as for `cnotGate_comp_pauliZGate_onRight`), while the `X` part and the phase `i·(-1)ᵗ`
stay on the target, so the output-side byproduct is a `Z` on the control and a `Y` on the target.  A
basis-state verification via `twoQubit_evolution_ext`, descending to the vector level for the phase;
the two control phases `(-1)ᶜ · (-1)ᵗ⁺ᶜ = (-1)ᵗ` are reconciled by cases. -/
theorem cnotGate_comp_pauliYGate_onRight :
    cnotGate.comp (pauliYGate.onRight qubit)
      = ((pauliZGate.onLeft qubit).comp (pauliYGate.onRight qubit)).comp cnotGate := by
  apply twoQubit_evolution_ext
  intro c t
  apply PureState.ext
  rw [Evolution.evolvePure_vec, Evolution.evolvePure_vec, PureState.tmul_vec]
  erw [Evolution.comp_op, ContinuousLinearMap.comp_apply]
  rw [Evolution.onRight_op_tmul, pauliYGate_op_apply_qubitBasis, TensorProduct.tmul_smul,
    cnotGate_op_smul, cnotGate_op_qubitBasisVec_tmul]
  erw [Evolution.comp_op, ContinuousLinearMap.comp_apply]
  rw [cnotGate_op_qubitBasisVec_tmul]
  erw [Evolution.comp_op, ContinuousLinearMap.comp_apply]
  rw [Evolution.onRight_op_tmul, pauliYGate_op_apply_qubitBasis, Evolution.onLeft_op_tmul,
    pauliZGate_op_apply_qubitBasis, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul,
    show (t + 1 + c : Fin 2) = t + c + 1 from by abel]
  congr 1
  fin_cases c <;> fin_cases t <;> simp [pow_succ]

end AxQM
