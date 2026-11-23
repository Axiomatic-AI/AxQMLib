/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledUnitaryDecomposition
import AxQM.Postulates.API.RelativePhaseToffoli

/-!
# AxQM.Postulates.API — scalar/phase lemmas for the controlled-`U` gate

Small lemmas about how the controlled-`U` gate (`controlledUnitary`) and the Pauli-`X` gate act on
**scalar-multiplied** computational-basis states — the tools a circuit-assembly proof needs when a
control wire carries a *relative phase* (a scalar multiple of `|0⟩` or `|1⟩` rather than a bare
basis state).

They are used by the Exercise 4.22 gate-count assembly (`AxQM/NC/Ch4/Exercise4_22.lean`), where
phase gates on the control qubits leave the intervening `CNOT`s facing a phased control; the
combined-circuit definition and correctness lemma also live here.

## What is formalised

* `pauliXGate_evolvePure_pauliXGate` — the pure-state form `X (X ψ) = ψ` of the Pauli-`X`
  involution (reusing the existing `pauliXGate_comp_pauliXGate`).
* `controlledUnitary_evolvePure_smul_ketOne` — a controlled gate **fires** through a control that is
  a scalar multiple of `|1⟩`: if `χ.vec = c • |1⟩` then `C(W)(χ ⊗ φ) = χ ⊗ W φ`, the phase `c`
  staying on the (unchanged) control factor.
* `controlledUnitary_evolvePure_smul_ketZero` — a controlled gate is the **identity** through a
  control that is a scalar multiple of `|0⟩`: `C(W)(χ ⊗ φ) = χ ⊗ φ`.

## Design notes

These statements are about the underlying vectors (`.vec`, `EuclideanSpace` via `qubitBasis`,
`TensorProduct`). The scalar-control proofs unfold the controlled gate to its block operator `|0⟩⟨0|
⊗ I + |1⟩⟨1| ⊗ W` (`change` to the raw tensor head, as in `controlledUnitary_op_mem_unitary`) and
use linearity of the rank-one projectors in the applied vector (`inner_smul_right`): the `|0⟩`
projector annihilates `c • |1⟩` (and vice versa), the diagonal one scales by `c`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **`X (X ψ) = ψ`** on pure states: applying the Pauli-`X` gate twice is the identity. Reuses the
existing involution `pauliXGate_comp_pauliXGate : pauliXGate.comp pauliXGate = Evolution.id`. -/
theorem pauliXGate_evolvePure_pauliXGate (ψ : PureState qubit) :
    pauliXGate.evolvePure (pauliXGate.evolvePure ψ) = ψ := by
  rw [← Evolution.evolvePure_comp, pauliXGate_comp_pauliXGate, Evolution.id_evolvePure]

/-- **A controlled gate fires through a scalar-`|1⟩` control.** If the control state `χ` is a scalar
multiple `c • |1⟩` of the computational-basis state `|1⟩` (a `|1⟩` carrying a relative phase), then
`C(W)(χ ⊗ φ) = χ ⊗ W φ`: the gate `W` is applied to the target and the phase `c` stays on the
unchanged control factor. -/
theorem controlledUnitary_evolvePure_smul_ketOne (W : Evolution S) (χ : PureState qubit)
    (φ : PureState S) (c : ℂ) (hχ : χ.vec = c • (qubitBasis 1).vec) :
    (controlledUnitary W).evolvePure (χ ⊗ φ) = χ ⊗ W.evolvePure φ := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec, hχ]
  change (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
        (1 : S.space →L[ℂ] S.space)
      + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec) W.op)
      ((c • (qubitBasis 1).vec) ⊗ₜ[ℂ] φ.vec) = (c • (qubitBasis 1).vec) ⊗ₜ[ℂ] W.op φ.vec
  rw [_root_.add_apply, TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
    InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply,
    one_apply_eq_self, inner_smul_right, inner_smul_right,
    qubitBasis_inner_qubitBasis, qubitBasis_inner_qubitBasis]
  simp only [Fin.isValue, zero_ne_one, ↓reduceIte, mul_zero, qubitBasis_vec, mul_one, add_eq_right]
  exact (congrArg (· ⊗ₜ[ℂ] φ.vec) (zero_smul ℂ _)).trans (TensorProduct.zero_tmul _ _)

/-- **A controlled gate is the identity through a scalar-`|0⟩` control.** If the control state `χ`
is a scalar multiple `c • |0⟩` of `|0⟩`, then `C(W)(χ ⊗ φ) = χ ⊗ φ`: the target is untouched. -/
theorem controlledUnitary_evolvePure_smul_ketZero (W : Evolution S) (χ : PureState qubit)
    (φ : PureState S) (c : ℂ) (hχ : χ.vec = c • (qubitBasis 0).vec) :
    (controlledUnitary W).evolvePure (χ ⊗ φ) = χ ⊗ φ := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec, hχ]
  change (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
        (1 : S.space →L[ℂ] S.space)
      + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec) W.op)
      ((c • (qubitBasis 0).vec) ⊗ₜ[ℂ] φ.vec) = (c • (qubitBasis 0).vec) ⊗ₜ[ℂ] φ.vec
  rw [_root_.add_apply, TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
    InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply,
    one_apply_eq_self, inner_smul_right, inner_smul_right,
    qubitBasis_inner_qubitBasis, qubitBasis_inner_qubitBasis]
  simp only [Fin.isValue, ↓reduceIte, mul_one, qubitBasis_vec, one_ne_zero, mul_zero, add_eq_left]
  exact (congrArg (· ⊗ₜ[ℂ] W.op φ.vec) (zero_smul ℂ _)).trans (TensorProduct.zero_tmul _ _)

/-! ### Gate-level ABC decomposition -/

/-- **Gate-level ABC decomposition** (Nielsen & Chuang, Corollary 4.2, at the `Evolution` level).
Every single-qubit gate `V` factors as `V = e^{iα}(A X B X C)` with single-qubit gates `A, B, C`
satisfying `A B C = 1`. Lifts `Concrete.exists_abc_decomposition` (the matrix statement) to gates
through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM` (`map_mul` carrying matrix product to
operator composition). Shared by the controlled-gate constructions of Chapter 4 that need `V`'s
uncontrolled action (e.g. the Exercise 4.22 assembly). -/
theorem Evolution.exists_abc_decomposition (V : Evolution qubit) :
    ∃ (A B C : Evolution qubit) (α : ℝ), (A.comp B).comp C = 1 ∧
      V.op = Complex.exp ((α : ℂ) * Complex.I) •
        (A.op.comp (pauliXGate.op.comp (B.op.comp (pauliXGate.op.comp C.op)))) := by
  set clm := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) with hclm
  obtain ⟨α, Am, Bm, Cm, hAm, hBm, hCm, hABCm, hVm⟩ :=
    Concrete.exists_abc_decomposition (clm.symm V.op) (Unitary.map_mem clm.symm V.unitary)
  set A : Evolution qubit := ⟨clm Am, Unitary.map_mem clm hAm⟩ with hA
  set B : Evolution qubit := ⟨clm Bm, Unitary.map_mem clm hBm⟩ with hB
  set C : Evolution qubit := ⟨clm Cm, Unitary.map_mem clm hCm⟩ with hC
  refine ⟨A, B, C, α, ?_, ?_⟩
  · apply Evolution.ext
    rw [Evolution.comp_op, Evolution.comp_op]
    change ((clm Am).comp (clm Bm)).comp (clm Cm) = (1 : Evolution qubit).op
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, ← map_mul, ← map_mul,
      hABCm, map_one]
    rfl
  · have hVeq : clm (clm.symm V.op) = V.op := clm.apply_symm_apply V.op
    rw [← hVeq, hVm, map_smul]
    refine congrArg (_ • ·) ?_
    change clm (Am * Concrete.pauliX * Bm * Concrete.pauliX * Cm)
        = (clm Am).comp ((clm Concrete.pauliX).comp
            ((clm Bm).comp ((clm Concrete.pauliX).comp (clm Cm))))
    simp only [map_mul, ContinuousLinearMap.mul_def]
    rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc]

/-! ### The combined Figure-4.8 circuit for `C²(U)` (Exercise 4.22's count-optimal decomposition) -/

/-- **The count-optimised `C²(V²)` circuit** of Exercise 4.22 (`A, B, C, α` the ABC decomposition of
`V`), as a bare `Evolution` product on `qubit ⊗ (qubit ⊗ qubit)` — the `8`-one-qubit / `6`-CNOT
decomposition of Figure 4.8, in operator order (leftmost applied last):
`P(α)₀ · A₂ · CNOT(0,2) · B₂ · CNOT(1,2) · CNOT(0,1) · P(-α)₁ · B†₂ · CNOT(0,1) · CNOT(0,2) ·`
`P(α)₁ · B₂ · CNOT(1,2) · C₂`. The trailing `· 1` mirrors the `List.prod` unit of `gateCircuit`, so
the count model's denotation is *definitionally* this product. -/
def ccontrolledUnitaryMergedCircuit (A B C : Evolution qubit) (α : ℝ) :
    Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  ((phaseShiftGate α).onLeft (qubit ⊗ qubit)).comp
    (((A.onRight qubit).onRight qubit).comp
      ((controlledUnitary (pauliXGate.onRight qubit)).comp
        (((B.onRight qubit).onRight qubit).comp
          ((cnotGate.onRight qubit).comp
            ((controlledUnitary (pauliXGate.onLeft qubit)).comp
              ((((phaseShiftGate (-α)).onLeft qubit).onRight qubit).comp
                (((B.adjoint.onRight qubit).onRight qubit).comp
                  ((controlledUnitary (pauliXGate.onLeft qubit)).comp
                    ((controlledUnitary (pauliXGate.onRight qubit)).comp
                      ((((phaseShiftGate α).onLeft qubit).onRight qubit).comp
                        (((B.onRight qubit).onRight qubit).comp
                          ((cnotGate.onRight qubit).comp
                            (((C.onRight qubit).onRight qubit).comp 1)))))))))))))

/-- **The combined circuit implements `C²(V²)`.** For any single-qubit gates `A, B, C`, phase `α`
and gate `V` whose ABC data satisfies `A B C = 1` and `V = e^{iα}(A X B X C)` (as operators), the
count-optimised circuit `ccontrolledUnitaryMergedCircuit A B C α` equals the doubly-controlled gate
`C²(V²) = ccontrolledUnitary (V.comp V)`. (The third ABC fact `B† = C A` is *derived* here from
`A B C = 1` and the gates' unitarity, so it is not a hypothesis.)

Checked on the eight computational-basis inputs (`threeQubit_evolution_ext`) with casework on the
two controls. The inactive branches collapse by `B† B = 1`, `X² = 1`, `A B C = 1`; the `(1,1)`
branch's blocked `CNOT(1,2)` fires through a phase-scaled `|1⟩` control
(`controlledUnitary_evolvePure_smul_ketOne`), giving `A X B X B† X B X C = (A X B X C)² = V²` (using
`B† = C A` and `V = e^{iα} A X B X C`) with a global `e^{2iα}`. -/
theorem ccontrolledUnitaryMergedCircuit_eq (A B C V : Evolution qubit) (α : ℝ)
    (hABC : (A.comp B).comp C = 1)
    (hVop : V.op = Complex.exp ((α : ℂ) * Complex.I) •
      (A.op.comp (pauliXGate.op.comp (B.op.comp (pauliXGate.op.comp C.op))))) :
    ccontrolledUnitaryMergedCircuit A B C α = ccontrolledUnitary (V.comp V) := by
  -- `B† = C A`, derived from `A B C = 1` and the gates' unitarity: `C = (A B)† = B† A†`, so
  -- `C A = B† A† A = B†` (the cyclic rotation of `A B C = 1`).
  have hBadj : B.adjoint = C.comp A := by
    apply Evolution.ext
    rw [Evolution.adjoint_op, Evolution.comp_op, ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.mul_def]
    have hsA : star A.op * A.op = 1 := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
      exact A.adjoint_comp_self
    have hsB : star B.op * B.op = 1 := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
      exact B.adjoint_comp_self
    have hABCop : A.op * B.op * C.op = 1 := by
      have h := congrArg Evolution.op hABC
      rwa [Evolution.comp_op, Evolution.comp_op, ← ContinuousLinearMap.mul_def,
        ← ContinuousLinearMap.mul_def, Evolution.one_def, Evolution.id_op] at h
    have hAB : star (A.op * B.op) * (A.op * B.op) = 1 := by
      rw [star_mul, mul_assoc, ← mul_assoc (star A.op) A.op B.op, hsA, one_mul, hsB]
    have hC : C.op = star (A.op * B.op) := by
      have h : star (A.op * B.op) * (A.op * B.op * C.op) = C.op := by rw [← mul_assoc, hAB, one_mul]
      rw [hABCop, mul_one] at h
      exact h.symm
    rw [hC, star_mul, mul_assoc, hsA, mul_one]
  -- `A (B (C ψ)) = ψ` (the `A B C = 1` identity on pure states).
  have hABCψ : ∀ ψ : PureState qubit, A.evolvePure (B.evolvePure (C.evolvePure ψ)) = ψ := by
    intro ψ
    rw [← Evolution.evolvePure_comp, ← Evolution.evolvePure_comp, hABC, Evolution.one_def,
      Evolution.id_evolvePure]
  -- `P(β)|1⟩` has vector `e^{iβ}|1⟩`.
  have hPvec1 : ∀ β : ℝ, ((phaseShiftGate β).evolvePure (qubitBasis 1)).vec
      = Complex.exp ((β : ℂ) * Complex.I) • (qubitBasis 1).vec := by
    intro β
    rw [Evolution.evolvePure_vec, phaseShiftGate_op_apply_qubitBasis]
    simp
  -- The bit flip `X|0⟩ = |1⟩`, `X|1⟩ = |0⟩` at the operator level.
  have hX0 : pauliXGate.op (qubitBasis 0).vec = (qubitBasis 1).vec := by
    rw [← Evolution.evolvePure_vec, pauliXGate_evolvePure_qubitBasis]; rfl
  have hX1 : pauliXGate.op (qubitBasis 1).vec = (qubitBasis 0).vec := by
    rw [← Evolution.evolvePure_vec, pauliXGate_evolvePure_qubitBasis]; rfl
  -- Two `tmul` scalar-cancellation shapes for the phase reconciliations (`s t = 1`; `s s`).
  have hcancelL : ∀ (m n p : qubit.space) (s t : ℂ), s * t = 1 →
      (s • m) ⊗ₜ[ℂ] ((t • n) ⊗ₜ[ℂ] p) = m ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] p) := by
    intro m n p s t h
    rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_smul, h, one_smul]
  have hcancelS : ∀ (m n p : qubit.space) (s : ℂ),
      (s • m) ⊗ₜ[ℂ] ((s • n) ⊗ₜ[ℂ] p) = m ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] ((s * s) • p)) := by
    intro m n p s
    rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_smul, TensorProduct.smul_tmul]
  -- the phases `e^{iα}`, `e^{-iα}` on the controls cancel (`α + (-α) = 0`).
  have hphase : (α : ℂ) * Complex.I + (↑(-α) : ℂ) * Complex.I = 0 := by push_cast; ring
  apply threeQubit_evolution_ext
  intro q1 q2 q3
  simp only [ccontrolledUnitaryMergedCircuit, cnotGate, Evolution.evolvePure_comp,
    Evolution.one_def, Evolution.id_evolvePure]
  fin_cases q1 <;> fin_cases q2 <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceAdd,
      Evolution.onLeft_evolvePure, Evolution.onRight_evolvePure,
      controlledUnitary_evolvePure_ketZero, controlledUnitary_evolvePure_ketOne,
      pauliXGate_evolvePure_qubitBasis, phaseShiftGate_evolvePure_qubitBasis_zero,
      ccontrolledUnitary_evolvePure_ketZero_left, ccontrolledUnitary_evolvePure_ketOne_left,
      hABCψ, Evolution.evolvePure_adjoint_evolvePure]
  · -- control `(0,1)`: the two phase gates on wire 1 cancel, then the blocked CNOT fires cleanly.
    have hPP1 : (phaseShiftGate (-α)).evolvePure ((phaseShiftGate α).evolvePure (qubitBasis 1))
        = qubitBasis 1 := by
      apply PureState.ext
      rw [Evolution.evolvePure_vec, hPvec1, ContinuousLinearMap.map_smul,
        phaseShiftGate_op_apply_qubitBasis]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, smul_smul, ← Complex.exp_add]
      rw [hphase, Complex.exp_zero, one_smul]
    rw [hPP1]
    simp only [controlledUnitary_evolvePure_ketOne, Evolution.onRight_evolvePure,
      pauliXGate_evolvePure_pauliXGate, hABCψ]
  · -- control `(1,0)`: the blocked CNOT sees a control `∝ |0⟩`, so it is the identity.
    have hc : (pauliXGate.evolvePure ((phaseShiftGate (-α)).evolvePure (qubitBasis 1))).vec
        = Complex.exp ((↑(-α) : ℂ) * Complex.I) • (qubitBasis 0).vec := by
      rw [Evolution.evolvePure_vec, hPvec1, ContinuousLinearMap.map_smul, hX1]
    rw [controlledUnitary_evolvePure_smul_ketZero pauliXGate _ _ _ hc]
    simp only [Evolution.onRight_evolvePure, pauliXGate_evolvePure_pauliXGate, hABCψ,
      Evolution.evolvePure_adjoint_evolvePure']
    -- reconcile the leftover phases on the two controls (they cancel, `e^{iα} e^{-iα} = 1`).
    apply PureState.ext
    simp only [PureState.tmul_vec, hPvec1, hc]
    refine hcancelL _ _ _ _ _ ?_
    rw [← Complex.exp_add, hphase, Complex.exp_zero]
  · -- control `(1,1)`: the blocked CNOT `∝ |1⟩` fires, giving `V²` with global phase `e^{2iα}`.
    have hc : (pauliXGate.evolvePure ((phaseShiftGate (-α)).evolvePure
        (pauliXGate.evolvePure ((phaseShiftGate α).evolvePure (qubitBasis 1))))).vec
        = Complex.exp ((α : ℂ) * Complex.I) • (qubitBasis 1).vec := by
      simp only [Evolution.evolvePure_vec, phaseShiftGate_op_apply_qubitBasis,
        ContinuousLinearMap.map_smul, hX0, hX1, Matrix.cons_val_zero, Matrix.cons_val_one,
        one_smul]
    rw [controlledUnitary_evolvePure_smul_ketOne pauliXGate _ _ _ hc]
    simp only [Evolution.onRight_evolvePure, hBadj]
    apply PureState.ext
    simp only [PureState.tmul_vec, hPvec1, hc, Evolution.evolvePure_vec, Evolution.evolvePure_comp,
      hVop, ContinuousLinearMap.comp_apply, _root_.smul_apply,
      ContinuousLinearMap.map_smul, smul_smul]
    exact hcancelS _ _ _ _

end AxQM
