/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Composite
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.API.Qubit
import AxQM.Postulates.API.BellReducedState
import AxQM.Concrete.Pauli

/-!
# AxQM.Postulates.API — the controlled-`U` gate and CNOT

Nielsen & Chuang's controlled operations (N&C §4.3): the single-qubit-controlled unitary `C(U)`
and, as its canonical instance, the controlled-`NOT` gate.  It is reused throughout Chapter 4 (and
by Problem 4.6's gate-teleportation formalisation).

## What is formalised

* `pauliXGate` — the Pauli-`X` (quantum `NOT`) gate as an `Evolution qubit`, obtained by promoting
  the concrete matrix `Concrete.pauliX` through `Matrix.toEuclideanCLM`; unitarity is transported
  from `Concrete.pauliX_mem_unitaryGroup` (N&C Exercise 2.19).
* `pauliXGate_evolvePure_qubitBasis` — the bit flip `X|i⟩ = |i ⊕ 1⟩` (`i + 1` in `Fin 2`).
* `controlledUnitary U` — the **controlled-`U` operation** `C(U) = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U`
  on `qubit ⊗ S` (control qubit on the left, target system `S` arbitrary), N&C eq. (4.24). This is
  a genuine `Evolution` (Postulate 5): the unitarity obligation is exactly the statement that the
  block-diagonal operator is unitary, discharged in `controlledUnitary_op_mem_unitary`.
* `controlledUnitary_evolvePure_ketZero` / `controlledUnitary_evolvePure_ketOne` — the **defining
  action**: with control `|0⟩` the target is untouched, with control `|1⟩` the gate `U` is applied
  to the target, i.e. `C(U)(|0⟩⊗ψ) = |0⟩⊗ψ` and `C(U)(|1⟩⊗ψ) = |1⟩⊗Uψ`.
* `controlledUnitary_onRight_conj` — **conjugating the target** of `C(U)` by local gates `V`, `W`
  on the target factor (with `V W = 1`) conjugates the controlled unitary:
  `(1 ⊗ V) · C(U) · (1 ⊗ W) = C(V U W)`. The general circuit identity behind building one controlled
  gate from another (e.g. `CNOT` from a controlled-`Z` and two Hadamards, N&C Exercise 4.17).
* `cnotGate = controlledUnitary pauliXGate` — the **controlled-`NOT`** gate on `qubit ⊗ qubit`.
* `cnotGate_evolvePure_qubitBasis` — N&C's CNOT truth table `|c, t⟩ ↦ |c, t ⊕ c⟩` (with `⊕` the
  `Fin 2` addition `t + c`), together with its two control-branch specialisations.

## Design notes

* **Generality / N&C fidelity.** `controlledUnitary` is the general controlled operation `C(U)`
  for an *arbitrary* target system `S` (N&C §4.3), not just a two-qubit gate; `cnotGate` is the
  `U = X` instance. This matches N&C, which introduces CNOT (§1.3.2) and then generalises to
  controlled-`U`, and makes the construction reusable for every later controlled gate. CNOT's
  truth table is a *corollary* of the controlled action composed with the bit flip `X|t⟩ = |t⊕1⟩`;
  the definition is faithful because `pauliXGate` *is* the `NOT` gate.
* **Construction.** `C(U)` is the operator sum `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U` built from the rank-one
  computational-basis projectors and `TensorProduct.mapL`. Unitarity is a one-shot operator
  computation: `C(U)† C(U) = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U†U = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ I = I` (the cross
  terms vanish because `|0⟩⟨0|` and `|1⟩⟨1|` are orthogonal, `⟨0|1⟩ = 0`, and `|0⟩⟨0| + |1⟩⟨1| = I`
  by `sum_rankOne_qubitBasis_eq_one`), and symmetrically for `C(U) C(U)†` using `UU† = I`.
* **Type heads.** The composite `(qubit ⊗ S).space` and the raw `qubit.space ⊗[ℂ] S.space` are
  definitionally equal but present different heads, so `star`/`adjoint` and `rw` do not match across
  them. `controlledUnitary_op_mem_unitary` is therefore stated and proved entirely at the raw
  tensor head; it slots into the `Evolution` `unitary` field by defeq. The action lemmas restate the
  applied operator at the raw head via `show` before firing `TensorProduct.mapL_tmul`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The Pauli-`X` (`NOT`) gate -/

/-- The **Pauli-`X` gate** `X` (the quantum `NOT`) as a closed-system `Evolution` of the qubit:
its operator is the concrete matrix `Concrete.pauliX = !![0,1;1,0]` promoted to a continuous linear
map via `Matrix.toEuclideanCLM`, with unitarity (the `Evolution` obligation, N&C Exercise 2.19)
transported from `Concrete.pauliX_mem_unitaryGroup`. -/
def pauliXGate : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) Concrete.pauliX_mem_unitaryGroup

/-- The underlying operator of `pauliXGate` is `Matrix.toEuclideanCLM Concrete.pauliX`. -/
@[simp]
theorem pauliXGate_op :
    pauliXGate.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX := rfl

/-- **The Pauli-`X` gate flips the computational basis:** `X|i⟩ = |i ⊕ 1⟩`, i.e.
`pauliXGate` sends `|i⟩` to `|i + 1⟩` (addition in `Fin 2`). This is the `NOT` truth table; it is
the reason `cnotGate` implements the controlled-`NOT`. -/
theorem pauliXGate_evolvePure_qubitBasis (i : Fin 2) :
    pauliXGate.evolvePure (qubitBasis i) = qubitBasis (i + 1) := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, pauliXGate_op, qubitBasis_vec, qubitBasis_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX)
        (EuclideanSpace.single i 1)).ofLp
      = (EuclideanSpace.single (i + 1) 1 : EuclideanSpace ℂ (Fin 2)).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases i <;> fin_cases j <;>
      simp [Concrete.pauliX, Matrix.mulVec, dotProduct, EuclideanSpace.single]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-! ### Computational-basis rank-one projectors -/

/-- The computational-basis rank-one projectors are **idempotent**: `|i⟩⟨i| · |i⟩⟨i| = |i⟩⟨i|`
(from `⟨i|i⟩ = 1`). Shared building block for the block-diagonal algebra of `controlledUnitary`. -/
theorem rankOne_qubitBasis_comp_self (i : Fin 2) :
    (InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec).comp
        (InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec)
      = InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec := by
  rw [InnerProductSpace.rankOne_comp_rankOne, qubitBasis_inner_qubitBasis]; simp

/-- The computational-basis rank-one projectors are **orthogonal**: `|i⟩⟨i| · |j⟩⟨j| = 0` for
`i ≠ j` (from `⟨i|j⟩ = 0`). Shared building block for the block-diagonal algebra of
`controlledUnitary`. -/
theorem rankOne_qubitBasis_comp_orthogonal {i j : Fin 2} (hij : i ≠ j) :
    (InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec).comp
        (InnerProductSpace.rankOne ℂ (qubitBasis j).vec (qubitBasis j).vec) = 0 := by
  rw [InnerProductSpace.rankOne_comp_rankOne, qubitBasis_inner_qubitBasis]; simp [hij]

/-- The identity operator composed with itself is the identity, `1 ∘ 1 = 1` (the `Evolution`-target
`I·I = I` step in the controlled-`U` block algebra). -/
theorem one_comp_one : (1 : S.space →L[ℂ] S.space).comp (1 : S.space →L[ℂ] S.space) = 1 := by
  rw [← ContinuousLinearMap.mul_def, mul_one]

/-! ### The controlled-`U` gate -/

/-- **The controlled-`U` operator is unitary** (N&C §4.3). For a single-qubit-controlled unitary,
the block-diagonal operator `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U` on `qubit.space ⊗ S.space` lies in the
unitary group: `C(U)† C(U) = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U†U = I` (the cross terms drop by orthogonality
`⟨0|1⟩ = 0`, and `|0⟩⟨0| + |1⟩⟨1| = I`), and symmetrically `C(U) C(U)† = I`.

Stated at the raw tensor head `qubit.space ⊗[ℂ] S.space` (where `star`/`adjoint` present a single
head); it discharges the `unitary` obligation of `controlledUnitary` by definitional equality with
`(qubit ⊗ S).space`. -/
theorem controlledUnitary_op_mem_unitary (U : Evolution S) :
    (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
        (1 : S.space →L[ℂ] S.space)
      + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec) U.op)
      ∈ unitary (qubit.space ⊗[ℂ] S.space →L[ℂ] qubit.space ⊗[ℂ] S.space) := by
  set p0 := InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec with hp0
  set p1 := InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec with hp1
  -- rank-one projector composition: `|i⟩⟨i| |j⟩⟨j| = δ_{ij} |i⟩⟨i|` (shared projector lemmas)
  have h00 : p0.comp p0 = p0 := by rw [hp0]; exact rankOne_qubitBasis_comp_self 0
  have h11 : p1.comp p1 = p1 := by rw [hp1]; exact rankOne_qubitBasis_comp_self 1
  have h01 : p0.comp p1 = 0 := by
    rw [hp0, hp1]; exact rankOne_qubitBasis_comp_orthogonal (by decide)
  have h10 : p1.comp p0 = 0 := by
    rw [hp0, hp1]; exact rankOne_qubitBasis_comp_orthogonal (by decide)
  -- the projectors are self-adjoint and resolve the identity
  have hadj0 : adjoint p0 = p0 := by rw [hp0, InnerProductSpace.adjoint_rankOne]
  have hadj1 : adjoint p1 = p1 := by rw [hp1, InnerProductSpace.adjoint_rankOne]
  have hadjone : adjoint (1 : S.space →L[ℂ] S.space) = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  have hsum : p0 + p1 = 1 := by
    rw [hp0, hp1]; have := sum_rankOne_qubitBasis_eq_one; rwa [Fin.sum_univ_two] at this
  -- unitarity of the target gate `U`
  have hUU : (adjoint U.op).comp U.op = 1 := U.adjoint_comp_self
  have hUUr : U.op.comp (adjoint U.op) = 1 := U.comp_adjoint_self
  have hadjop : adjoint (TensorProduct.mapL p0 (1 : S.space →L[ℂ] S.space)
      + TensorProduct.mapL p1 U.op)
      = TensorProduct.mapL p0 1 + TensorProduct.mapL p1 (adjoint U.op) := by
    simp only [map_add, TensorProduct.adjoint_mapL, hadj0, hadj1, hadjone]
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def, hadjop,
      comp_add, add_comp, add_comp, ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp,
      ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp, h00, h01, h10, h11, hUU, one_comp_one,
      TensorProduct.mapL_zero_left, TensorProduct.mapL_zero_left, add_zero, zero_add,
      ← TensorProduct.mapL_add_left, hsum, TensorProduct.mapL_one]
  · rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def, hadjop,
      comp_add, add_comp, add_comp, ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp,
      ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp, h00, h01, h10, h11, hUUr, one_comp_one,
      TensorProduct.mapL_zero_left, TensorProduct.mapL_zero_left, add_zero, zero_add,
      ← TensorProduct.mapL_add_left, hsum, TensorProduct.mapL_one]

/-- **The controlled-`U` gate** `C(U)` (Nielsen & Chuang §4.3, eq. 4.24): the `Evolution` on the
composite `qubit ⊗ S` whose operator is `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U` — the identity on the target when
the control qubit is `|0⟩`, and the unitary `U` on the target when it is `|1⟩`. Unitarity (the
`Evolution` obligation) is `controlledUnitary_op_mem_unitary`. -/
def controlledUnitary (U : Evolution S) : Evolution (qubit ⊗ S) where
  op := TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
      (1 : S.space →L[ℂ] S.space)
    + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec) U.op
  unitary := controlledUnitary_op_mem_unitary U

/-- The underlying operator of `controlledUnitary U` is `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U`. -/
@[simp]
theorem controlledUnitary_op (U : Evolution S) :
    (controlledUnitary U).op
      = TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec) 1
        + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
            U.op := rfl

/-- **Controlled-`U`, control `|0⟩`:** the target is untouched, `C(U)(|0⟩ ⊗ ψ) = |0⟩ ⊗ ψ`. -/
theorem controlledUnitary_evolvePure_ketZero (U : Evolution S) (ψ : PureState S) :
    (controlledUnitary U).evolvePure ((qubitBasis 0) ⊗ ψ) = (qubitBasis 0) ⊗ ψ := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, PureState.tmul_vec]
  change (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
        (1 : S.space →L[ℂ] S.space)
      + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec) U.op)
      ((qubitBasis 0).vec ⊗ₜ[ℂ] ψ.vec) = (qubitBasis 0).vec ⊗ₜ[ℂ] ψ.vec
  rw [_root_.add_apply, TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
    InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply,
    qubitBasis_inner_qubitBasis, qubitBasis_inner_qubitBasis, one_apply_eq_self,
    ite_eq_left rfl, ite_eq_right (by
        decide), one_smul, zero_smul, TensorProduct.zero_tmul, add_zero]

/-- **Controlled-`U`, control `|1⟩`:** the gate `U` is applied to the target,
`C(U)(|1⟩ ⊗ ψ) = |1⟩ ⊗ Uψ`. -/
theorem controlledUnitary_evolvePure_ketOne (U : Evolution S) (ψ : PureState S) :
    (controlledUnitary U).evolvePure ((qubitBasis 1) ⊗ ψ) = (qubitBasis 1) ⊗ (U.evolvePure ψ) := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, PureState.tmul_vec, PureState.tmul_vec, Evolution.evolvePure_vec]
  change (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
        (1 : S.space →L[ℂ] S.space)
      + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec) U.op)
      ((qubitBasis 1).vec ⊗ₜ[ℂ] ψ.vec) = (qubitBasis 1).vec ⊗ₜ[ℂ] U.op ψ.vec
  rw [_root_.add_apply, TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
    InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply,
    qubitBasis_inner_qubitBasis, qubitBasis_inner_qubitBasis, one_apply_eq_self,
    ite_eq_right (by
        decide), ite_eq_left rfl, zero_smul, one_smul, TensorProduct.zero_tmul, zero_add]

/-! ### Conjugating the target of a controlled gate -/

/-- **Conjugating the target of a controlled-`U` gate conjugates `U`.** Sandwiching `C(U)` between
`1 ⊗ V` on the left and `1 ⊗ W` on the right (gates acting on the *target* factor `S`, the control
qubit untouched) — with `V W = 1`, i.e. `W = V⁻¹` — turns `C(U)` into `C(V U W)`:
`(1 ⊗ V) · C(U) · (1 ⊗ W) = C(V U W)`.

The control branch `|0⟩⟨0| ⊗ I` becomes `|0⟩⟨0| ⊗ (V W) = |0⟩⟨0| ⊗ I` (this is where `V W = 1` is
used), and the active branch `|1⟩⟨1| ⊗ U` becomes `|1⟩⟨1| ⊗ (V U W)`. This is the general circuit
identity behind building one controlled gate from another by conjugating the target with local
gates — e.g. `CNOT` from a controlled-`Z` and two Hadamards (N&C Exercise 4.17), where `V = W = H`
and `H Z H = X`.

Proved by cracking to operators at the raw tensor head (`show`), where `1 ⊗ V = TensorProduct.mapL
1 V.op` etc., and running the `TensorProduct.mapL` composition algebra (`mapL_comp`, distributing
over the block sum); `V.op ∘ W.op = 1` collapses the `|0⟩` branch. -/
theorem controlledUnitary_onRight_conj (U V W : Evolution S) (h : V.comp W = Evolution.id) :
    (Evolution.onRight V qubit).comp
        ((controlledUnitary U).comp (Evolution.onRight W qubit))
      = controlledUnitary (V.comp (U.comp W)) := by
  have hVW : V.op.comp W.op = 1 := by rw [← Evolution.comp_op, h, Evolution.id_op]
  have e1 : (Evolution.onRight V qubit).op = TensorProduct.mapL 1 V.op := by
    unfold Evolution.onRight
    rw [Evolution.tmul_op, Evolution.id_op]
  have e2 : (Evolution.onRight W qubit).op = TensorProduct.mapL 1 W.op := by
    unfold Evolution.onRight
    rw [Evolution.tmul_op, Evolution.id_op]
  -- The generic-tensor algebra, entirely at the raw head `qubit.space ⊗[ℂ] S.space`, where the
  -- `mapL` composition algebra applies (the composite head would block the `mapL` rewrites by
  -- presenting a different, defeq, `.comp`).
  have goalGeneric : (TensorProduct.mapL 1 V.op).comp
      ((TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
            (1 : S.space →L[ℂ] S.space)
          + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
              U.op).comp (TensorProduct.mapL 1 W.op))
      = TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
          (1 : S.space →L[ℂ] S.space)
        + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
            (V.op.comp (U.op.comp W.op)) := by
    set p0 := InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec
    set p1 := InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec
    rw [ContinuousLinearMap.add_comp, ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp,
      ContinuousLinearMap.comp_add, ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_id, hVW]
  apply Evolution.ext
  rw [Evolution.comp_op, Evolution.comp_op, e1, e2, controlledUnitary_op, controlledUnitary_op]
  exact goalGeneric

/-- **Controlled gates compose by composing their targets:** `C(U) · C(V) = C(U · V)`. Both are
block-diagonal — `C(U) = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U` and likewise for `V` — so their product multiplies
out to `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ (U · V)`: the `|0⟩`/`|1⟩` cross terms drop by orthogonality of the
computational-basis projectors (`⟨0|1⟩ = 0`) and `|0⟩⟨0|² = |0⟩⟨0|`, `|1⟩⟨1|² = |1⟩⟨1|`. This is the
key algebra of the controlled-`U` construction: stacking two controlled gates sharing the control is
the controlled gate of the composite target — used, e.g., to append a `CNOT` to a partially built
controlled rotation (N&C Exercise 4.23).

Proved by cracking to operators at the raw tensor head `qubit.space ⊗[ℂ] S.space` (`change`, as in
`controlledUnitary_op_mem_unitary` — the composite head would block the `mapL` rewrites) and running
the `TensorProduct.mapL` composition algebra (`mapL_comp` distributing over the block sum), with the
projector products `p₀ ∘ p₀ = p₀`, `p₀ ∘ p₁ = 0`, `p₁ ∘ p₀ = 0`, `p₁ ∘ p₁ = p₁` collapsing the
diagonal. -/
theorem controlledUnitary_comp (U V : Evolution S) :
    (controlledUnitary U).comp (controlledUnitary V) = controlledUnitary (U.comp V) := by
  apply Evolution.ext
  set p0 := InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec with hp0
  set p1 := InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec with hp1
  have h00 : p0.comp p0 = p0 := by rw [hp0]; exact rankOne_qubitBasis_comp_self 0
  have h11 : p1.comp p1 = p1 := by rw [hp1]; exact rankOne_qubitBasis_comp_self 1
  have h01 : p0.comp p1 = 0 := by
    rw [hp0, hp1]; exact rankOne_qubitBasis_comp_orthogonal (by decide)
  have h10 : p1.comp p0 = 0 := by
    rw [hp0, hp1]; exact rankOne_qubitBasis_comp_orthogonal (by decide)
  change (TensorProduct.mapL p0 (1 : S.space →L[ℂ] S.space) + TensorProduct.mapL p1 U.op).comp
      (TensorProduct.mapL p0 (1 : S.space →L[ℂ] S.space) + TensorProduct.mapL p1 V.op)
    = TensorProduct.mapL p0 (1 : S.space →L[ℂ] S.space) + TensorProduct.mapL p1 (U.op.comp V.op)
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_add,
    ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp,
    ← TensorProduct.mapL_comp, h00, h01, h10, h11, one_comp_one, TensorProduct.mapL_zero_left,
    TensorProduct.mapL_zero_left, add_zero, zero_add]

/-! ### The controlled-`NOT` gate -/

/-- **The controlled-`NOT` (CNOT) gate** on two qubits (Nielsen & Chuang §1.3.2), the controlled-`U`
gate with `U = X`: it flips the target qubit exactly when the control qubit is `|1⟩`. -/
def cnotGate : Evolution (qubit ⊗ qubit) := controlledUnitary pauliXGate

/-- `cnotGate` is definitionally the controlled-`X` gate: `CNOT = C(X)`. The citable unfolding used
whenever a `CNOT` needs to be handled through the general `controlledUnitary` API. -/
theorem cnotGate_def : cnotGate = controlledUnitary pauliXGate := rfl

/-- **CNOT, control `|0⟩`:** the target is untouched, `CNOT(|0⟩ ⊗ |t⟩) = |0⟩ ⊗ |t⟩`. -/
theorem cnotGate_evolvePure_ketZero (t : Fin 2) :
    cnotGate.evolvePure ((qubitBasis 0) ⊗ (qubitBasis t)) = (qubitBasis 0) ⊗ (qubitBasis t) :=
  controlledUnitary_evolvePure_ketZero pauliXGate (qubitBasis t)

/-- **CNOT, control `|1⟩`:** the target is flipped, `CNOT(|1⟩ ⊗ |t⟩) = |1⟩ ⊗ |t ⊕ 1⟩`. -/
theorem cnotGate_evolvePure_ketOne (t : Fin 2) :
    cnotGate.evolvePure ((qubitBasis 1) ⊗ (qubitBasis t))
      = (qubitBasis 1) ⊗ (qubitBasis (t + 1)) := by
  rw [cnotGate, controlledUnitary_evolvePure_ketOne, pauliXGate_evolvePure_qubitBasis]

/-- **The CNOT truth table** (Nielsen & Chuang §1.3.2): `CNOT|c, t⟩ = |c, t ⊕ c⟩`, where `⊕` is
addition in `Fin 2` (`t + c`). The control qubit is unchanged and the target is XORed with the
control. -/
theorem cnotGate_evolvePure_qubitBasis (c t : Fin 2) :
    cnotGate.evolvePure ((qubitBasis c) ⊗ (qubitBasis t))
      = (qubitBasis c) ⊗ (qubitBasis (t + c)) := by
  fin_cases c
  · simpa using cnotGate_evolvePure_ketZero t
  · simpa using cnotGate_evolvePure_ketOne t

/-- **The two-`CNOT`, two-single-qubit-gate controlled construction** (Nielsen & Chuang §4.3,
Exercise 4.23). For target-qubit gates `V`, `W` with `V · W = I`, sandwiching two `CNOT`s between
them realises a controlled gate whose target is `V X W X`:
`(1 ⊗ V) · CNOT · (1 ⊗ W) · CNOT = C(V · X · W · X)`,
with the two `X` gates supplied by the `CNOT`s (conditioned on the control) and only `V`, `W`
applied unconditionally. This is the reduced Figure-4.6 circuit with `C = I`: when the target `U`
of a controlled-`U` factors as `U = V X W X` with `V W = I` (so `V`, `W` are the only single-qubit
gates), `C(U)` needs just these **two** single-qubit gates — the `3 → 2` reduction the exercise asks
for. It applies to `U = R_y(θ)` and `U = R_z(θ)` (`V = R_a(θ/2)`, `W = R_a(-θ/2)`), whose axes are
perpendicular to `X`; it does *not* apply to `R_x` (which commutes with `X`).

Derived, not recomputed: reassociating to `((1 ⊗ V) · (CNOT · (1 ⊗ W))) · CNOT`, the bracket is
`controlledUnitary_onRight_conj` at `U = X` (using `V · W = I`), giving `C(V X W)`, and the trailing
`CNOT = C(X)` is absorbed by `controlledUnitary_comp` into `C(V X W · X)`. -/
theorem controlledUnitary_cnot_conj_cnot (V W : Evolution qubit) (h : V.comp W = Evolution.id) :
    ((V.onRight qubit).comp cnotGate).comp ((W.onRight qubit).comp cnotGate)
      = controlledUnitary (V.comp (pauliXGate.comp (W.comp pauliXGate))) := by
  rw [Evolution.comp_assoc, ← Evolution.comp_assoc cnotGate (W.onRight qubit) cnotGate,
    ← Evolution.comp_assoc (V.onRight qubit) (cnotGate.comp (W.onRight qubit)) cnotGate,
    cnotGate_def, controlledUnitary_onRight_conj pauliXGate V W h, controlledUnitary_comp,
    Evolution.comp_assoc, Evolution.comp_assoc]

end AxQM
