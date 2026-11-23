/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.Qudit
import AxQM.Concrete.ABCDecomposition

/-!
# AxQM.Postulates.API — Figure 4.6: controlled-`U` from single-qubit gates and two CNOTs

Nielsen & Chuang's **controlled-operation gate count** (N&C §4.3, Figure 4.6): a
single-qubit-controlled gate `C(U)` is built from *unconditional* single-qubit gates and exactly
**two** CNOTs, using the ABC decomposition of `U` (Corollary 4.2). This is the fact that one
controlled-single-qubit gate costs two CNOTs, on which the gate counting of Exercise 4.22 (`C²(U)`
from ≤ 8 one-qubit gates and 6 CNOTs) rests, and it is reused by the other controlled-gate
constructions of Chapter 4 (Exercises 4.23, 4.28).

## What is formalised

* `phaseShiftGate α` — the **single-qubit phase-shift gate** `P(α) = diag(1, e^{iα})`, the general
  relative-phase gate (`S = P(π/2)`, `T = P(π/4)` are special cases), as an `Evolution qubit`.
  `phaseShiftGate_op`, `phaseShiftGate_op_apply_qubitBasis` (`P(α)|i⟩ = [1, e^{iα}]ᵢ |i⟩`) and
  `phaseShiftGate_evolvePure_qubitBasis_zero` (`P(α)|0⟩ = |0⟩`) record its action.
* `twoQubit_evolution_ext` — **computational-basis extensionality** for two-qubit gates: two
  evolutions of `qubit ⊗ qubit` are equal as soon as they agree on the four basis states
  `|q₁⟩ ⊗ |q₂⟩`. The two-qubit analogue of `threeQubit_evolution_ext`.
* `controlledUnitary_eq_abc_cnot_circuit` — **Figure 4.6:** for every single-qubit gate `U` there
  exist single-qubit gates `A, B, C` and a phase `α` with `A B C = 1` such that
  `C(U) = (P(α) ⊗ 1) · (1 ⊗ A) · CNOT · (1 ⊗ B) · CNOT · (1 ⊗ C)`, i.e. `C(U)` is implemented by the
  phase-shift gate on the control, the three unconditional single-qubit gates `A, B, C` on the
  target, and two CNOTs. So a controlled-single-qubit gate needs **four one-qubit gates and two
  CNOTs**.

## Design notes

* **Statement shape.** The theorem is the faithful "for *any* single-qubit `U`" form (N&C states
  Figure 4.6 for an arbitrary single-qubit unitary): `A, B, C, α` are existentially quantified and
  produced from the genuine ABC decomposition of `U` (`Concrete.exists_abc_decomposition`, Corollary
  4.2), with `A B C = 1` the honest witness condition, and it is a full equality of the gate
  `Evolution`s (holding on every input), not an on-basis-states or up-to-phase surrogate. The
  **relative** phase gate `P(α)` sits on the control (not folded into `A` as a global phase on the
  target): a global phase absorbed into `A` would break the `|0⟩`-control branch (`P(α) A B C ≠ A B
  C = 1`), so the controlled phase is essential — it is exactly why `C(U)` needs a phase gate that
  `U` alone does not.
* **The phase-shift gate.** `phaseShiftGate α` is built directly as the computational-basis
  diagonal operator `diag(1, e^{iα})` (`OrthonormalBasis.diagonalOperator`), unitary because both
  diagonal entries have unit modulus, mirroring `diagPhase`; its action on `|i⟩` then comes for free
  from `basisFun_diagonalOperator_apply_single`.
* **Proof.** `twoQubit_evolution_ext` reduces the equality to the four basis inputs `|q₁⟩ ⊗ |q₂⟩`;
  casework on the control `q₁` (`fin_cases`) drives the factorwise gate actions
  (`Evolution.onLeft/onRight_evolvePure`, `controlledUnitary_evolvePure_ketZero/ketOne`). Control
  `|0⟩`: all CNOTs idle and `P(α)|0⟩ = |0⟩`, so the target sees `A B C = 1` (the ABC identity,
  transported to gates through `Matrix.toEuclideanCLM`'s `map_mul`). Control `|1⟩`: the CNOTs act as
  `X`, the target sees `A X B X C` and `P(α)|1⟩ = e^{iα}|1⟩`, matching `U = e^{iα}(A X B X C)`
  (the ABC decomposition through `toEuclideanCLM`) once the control's relative phase is pushed into
  the target factor (`TensorProduct.tmul_smul`/`smul_tmul'`).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap Matrix

noncomputable section

namespace AxQM

/-! ### The single-qubit phase-shift gate `P(α) = diag(1, e^{iα})` -/

/-- **The phase-shift gate** `P(α) = diag(1, e^{iα})` as a closed-system `Evolution` of the qubit:
the operator diagonal in the computational basis with entries `1` on `|0⟩` and `e^{iα}` on `|1⟩`.
It is unitary because both entries have unit modulus. This is the general relative-phase gate
(N&C §4.2), with the `S` gate `P(π/2) = diag(1, i)` and the `T` gate `P(π/4) = diag(1, e^{iπ/4})` as
special cases; it is the phase gate placed on the control qubit in Figure 4.6's controlled-`U`
construction. -/
def phaseShiftGate (α : ℝ) : Evolution qubit where
  op := (EuclideanSpace.basisFun (Fin 2) ℂ).diagonalOperator
          (fun i => ![(1 : ℂ), Complex.exp ((α : ℂ) * Complex.I)] i)
  unitary := by
    refine OrthonormalBasis.diagonalOperator_mem_unitary _ _ (fun i => ?_)
    fin_cases i <;> simp [Complex.norm_exp]

/-- The underlying operator of `phaseShiftGate α` is the computational-basis diagonal operator
with entries `[1, e^{iα}]`. -/
theorem phaseShiftGate_op (α : ℝ) :
    (phaseShiftGate α).op = (EuclideanSpace.basisFun (Fin 2) ℂ).diagonalOperator
      (fun i => ![(1 : ℂ), Complex.exp ((α : ℂ) * Complex.I)] i) := rfl

/-- **Eigenvalue action of the phase-shift gate:** `P(α)|i⟩ = [1, e^{iα}]ᵢ |i⟩`, i.e. `P(α)` fixes
`|0⟩` and multiplies `|1⟩` by `e^{iα}`. -/
theorem phaseShiftGate_op_apply_qubitBasis (α : ℝ) (i : Fin 2) :
    (phaseShiftGate α).op (qubitBasis i).vec
      = ![(1 : ℂ), Complex.exp ((α : ℂ) * Complex.I)] i • (qubitBasis i).vec := by
  rw [qubitBasis_vec, phaseShiftGate_op]
  exact basisFun_diagonalOperator_apply_single _ i

/-- **The phase-shift gate's diagonal basis action as a phase power:**
`P(α)|j⟩ = (e^{iα})^j |j⟩`, i.e. `P(α)` fixes `|0⟩` and multiplies `|1⟩` by `e^{iα}`, written as the
`j`-th power of `e^{iα}` (`(e^{iα})^0 = 1`, `(e^{iα})^1 = e^{iα}`). The `evolvePure`/`.vec`-level
restatement of `phaseShiftGate_op_apply_qubitBasis` with the diagonal entry `![1, e^{iα}]ⱼ` folded
into `(e^{iα})^{j}` — the form in which the phase gate composes across the wires of a phase-gradient
layer (the exponents adding). The `Fin 2`-general companion of
`phaseShiftGate_evolvePure_qubitBasis_zero` (its `j = 0` case), and the diagonal analogue of
`rotZGate_evolvePure_qubitBasis_sum`. -/
theorem phaseShiftGate_evolvePure_qubitBasis (α : ℝ) (j : Fin 2) :
    ((phaseShiftGate α).evolvePure (qubitBasis j)).vec
      = Complex.exp ((α : ℂ) * Complex.I) ^ (j : ℕ) • (qubitBasis j).vec := by
  rw [Evolution.evolvePure_vec, phaseShiftGate_op_apply_qubitBasis]
  fin_cases j <;> simp

/-- **The phase-shift gate fixes `|0⟩`:** `P(α)|0⟩ = |0⟩`, the `|0⟩`-branch of the phase gate's
action (the control-`|0⟩` case of Figure 4.6, where no relative phase is applied). -/
theorem phaseShiftGate_evolvePure_qubitBasis_zero (α : ℝ) :
    (phaseShiftGate α).evolvePure (qubitBasis 0) = qubitBasis 0 := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, phaseShiftGate_op_apply_qubitBasis]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val_zero, qubitBasis_vec]
  erw [one_smul]

/-! ### Computational-basis extensionality for two-qubit gates -/

/-- **A two-qubit gate is determined by its action on the computational basis.** Two evolutions
`A`, `B` of `qubit ⊗ qubit` are equal as soon as they agree on every computational-basis state
`|q₁⟩ ⊗ |q₂⟩`, `qᵢ ∈ {0, 1}`. The two-qubit analogue of `threeQubit_evolution_ext`: it reduces a
case-by-case verification of a two-qubit circuit on the four basis inputs to a genuine equality of
unitary gates.

The proof reduces to operator equality (`Evolution.ext`), then linear-map equality
(`ContinuousLinearMap.coe_injective`), and applies `Module.Basis.ext` to the tensor-product basis
built from `EuclideanSpace.basisFun` by `OrthonormalBasis.tensorProduct`, whose basis vectors are
the computational-basis unit vectors `(qubitBasis _).vec`; the hypothesis supplies the required
agreement after unfolding `evolvePure_vec` and `PureState.tmul_vec`. -/
theorem twoQubit_evolution_ext {A B : Evolution (qubit ⊗ qubit)}
    (h : ∀ q1 q2 : Fin 2,
      A.evolvePure ((qubitBasis q1) ⊗ (qubitBasis q2))
        = B.evolvePure ((qubitBasis q1) ⊗ (qubitBasis q2))) :
    A = B := by
  apply Evolution.ext
  apply ContinuousLinearMap.coe_injective
  let bq : OrthonormalBasis (Fin 2) ℂ qubit.space := EuclideanSpace.basisFun (Fin 2) ℂ
  have hbq : ∀ i : Fin 2, bq i = (qubitBasis i).vec := fun i => by
    rw [qubitBasis_vec]; exact EuclideanSpace.basisFun_apply (Fin 2) ℂ i
  refine Module.Basis.ext (bq.tensorProduct bq).toBasis ?_
  rintro ⟨q1, q2⟩
  have hb : (bq.tensorProduct bq).toBasis (q1, q2)
      = (qubitBasis q1).vec ⊗ₜ[ℂ] (qubitBasis q2).vec := by
    rw [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply, hbq, hbq]
  rw [hb]
  have hh := congrArg PureState.vec (h q1 q2)
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec] at hh
  exact hh

/-! ### Figure 4.6: `C(U)` from `A, B, C`, a phase gate, and two CNOTs -/

/-- **Nielsen & Chuang, Figure 4.6: the controlled-`U` gate from single-qubit gates and two CNOTs.**
For every single-qubit gate `U` there exist single-qubit gates `A, B, C` and a real phase `α` with
`A B C = 1` such that the controlled-`U` gate factors as
`C(U) = (P(α) ⊗ 1) · (1 ⊗ A) · CNOT · (1 ⊗ B) · CNOT · (1 ⊗ C)`,
the phase-shift gate `P(α)` on the control, the three unconditional single-qubit gates `A, B, C`
on the target, and two CNOTs. Hence a single-controlled single-qubit gate is built from four
one-qubit gates and two CNOTs — the count used in Exercise 4.22.

The witnesses `A, B, C, α` are the genuine ABC decomposition of `U` (Corollary 4.2,
`Concrete.exists_abc_decomposition`): `A B C = 1` and `U = e^{iα}(A X B X C)`. Proved by two-qubit
computational-basis extensionality (`twoQubit_evolution_ext`) with casework on the control: control
`|0⟩` gives `A B C = 1` on the target (CNOTs idle, no phase); control `|1⟩` gives `e^{iα} A X B X C
= U` on the target (CNOTs act as `X`, `P(α)|1⟩ = e^{iα}|1⟩`). -/
theorem controlledUnitary_eq_abc_cnot_circuit (U : Evolution qubit) :
    ∃ (A B C : Evolution qubit) (α : ℝ),
      (A.comp B).comp C = 1 ∧
      controlledUnitary U =
        ((phaseShiftGate α).onLeft qubit).comp
          ((A.onRight qubit).comp
            (cnotGate.comp
              ((B.onRight qubit).comp
                (cnotGate.comp (C.onRight qubit))))) := by
  set clm := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) with hclm
  -- The ABC decomposition of `U`'s matrix (Corollary 4.2): `A B C = 1`, `U = e^{iα}(A X B X C)`.
  obtain ⟨α, Am, Bm, Cm, hAm, hBm, hCm, hABCm, hUm⟩ :=
    Concrete.exists_abc_decomposition (clm.symm U.op) (Unitary.map_mem clm.symm U.unitary)
  -- Lift the matrix witnesses `A, B, C` to single-qubit gates through `toEuclideanCLM`.
  set A : Evolution qubit := ⟨clm Am, Unitary.map_mem clm hAm⟩ with hA
  set B : Evolution qubit := ⟨clm Bm, Unitary.map_mem clm hBm⟩ with hB
  set C : Evolution qubit := ⟨clm Cm, Unitary.map_mem clm hCm⟩ with hC
  -- `A B C = 1` at the gate level (`toEuclideanCLM` carries matrix product to composition).
  have hABC : (A.comp B).comp C = 1 := by
    apply Evolution.ext
    rw [Evolution.comp_op, Evolution.comp_op]
    change ((clm Am).comp (clm Bm)).comp (clm Cm) = (1 : Evolution qubit).op
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, ← map_mul, ← map_mul,
      hABCm, map_one]
    rfl
  -- `U = e^{iα}(A X B X C)` at the operator level.
  have hUop : U.op = Complex.exp ((α : ℂ) * Complex.I) •
      (A.op.comp (pauliXGate.op.comp (B.op.comp (pauliXGate.op.comp C.op)))) := by
    have hUeq : clm (clm.symm U.op) = U.op := clm.apply_symm_apply U.op
    rw [← hUeq, hUm, map_smul]
    refine congrArg (_ • ·) ?_
    change clm (Am * Concrete.pauliX * Bm * Concrete.pauliX * Cm)
        = (clm Am).comp ((clm Concrete.pauliX).comp
            ((clm Bm).comp ((clm Concrete.pauliX).comp (clm Cm))))
    simp only [map_mul, ContinuousLinearMap.mul_def]
    rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc]
  refine ⟨A, B, C, α, hABC, ?_⟩
  -- Verify on the four computational-basis inputs, casing on the control qubit.
  apply twoQubit_evolution_ext
  intro q1 q2
  fin_cases q1
  · -- control `|0⟩`: CNOTs idle, phase trivial; the target sees `A B C = 1`.
    simp only [Fin.isValue, Fin.mk_zero, Evolution.evolvePure_comp, Evolution.onLeft_evolvePure,
      Evolution.onRight_evolvePure, cnotGate, controlledUnitary_evolvePure_ketZero,
      phaseShiftGate_evolvePure_qubitBasis_zero]
    congr 1
    rw [← Evolution.evolvePure_comp, ← Evolution.evolvePure_comp, hABC, Evolution.one_def,
      Evolution.id_evolvePure]
  · -- control `|1⟩`: CNOTs act as `X`, phase `e^{iα}`; the target sees `e^{iα} A X B X C = U`.
    simp only [Fin.isValue, Fin.mk_one, Evolution.evolvePure_comp, Evolution.onLeft_evolvePure,
      Evolution.onRight_evolvePure, cnotGate, controlledUnitary_evolvePure_ketOne]
    apply PureState.ext
    simp only [PureState.tmul_vec, Evolution.evolvePure_vec]
    rw [hUop, phaseShiftGate_op_apply_qubitBasis]
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      _root_.smul_apply, ContinuousLinearMap.comp_apply]
    rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']

end AxQM
