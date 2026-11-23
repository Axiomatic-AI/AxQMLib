/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CnotXBasis
import AxQM.Postulates.API.PauliEigen
import AxQM.Postulates.API.ToffoliHadamard
import AxQM.Postulates.API.ControlBranchExt

/-!
# AxQM.Postulates.API — measuring an observable with a Hadamard-controlled-`U` circuit

Nielsen & Chuang's Exercise 4.34 ("Measuring an operator"): the circuit
that implements a projective measurement of a single-qubit `±1` observable `U` (an operator that is
both Hermitian and unitary, hence both an observable and a gate) using one ancilla qubit, a
controlled-`U`, and two Hadamards.

```
|0⟩ ─── H ───•─── H ───⊙   (measure ancilla)
             │
|ψ⟩ ─────────U──────────
```

## What is formalised

* `Evolution.toObservable U hsa` — a **Hermitian gate viewed as an observable**: a unitary `U`
  (an `Evolution`) that is additionally self-adjoint (`IsSelfAdjoint U.op`) is packaged as an
  `Observable`.  `Evolution.toObservable_op_mul_self` records the resulting **involution**
  `U² = I` (from unitary ∧ self-adjoint), the hypothesis every `±1`-observable API needs.
* `measureObservableCircuit U` — the **circuit** `(H ⊗ 1) · C(U) · (H ⊗ 1)` on `qubit ⊗ qubit`
  (ancilla = left/control qubit; target = right qubit), an `Evolution`.
* `measureObservableCircuit_op_qubitBasisZero_tmul` — **the circuit action**: with the ancilla
  prepared in `|0⟩`, the circuit sends `|0⟩ ⊗ |ψ⟩` to `|0⟩ ⊗ P₊|ψ⟩ + |1⟩ ⊗ P₋|ψ⟩`, where
  `P₊ = (I + U)/2` and `P₋ = (I − U)/2` are the eigenprojectors of `U`.  Stated at the raw operator
  level (`(I ± U)/2` applied to a target vector `x`) so it needs no self-adjointness hypothesis.
* `measureObservableCircuit_op_qubitBasisZero_tmul_projMeas` — the same, with the target components
  written as the eigenprojectors `Observable.projPlus`/`Observable.projMinus` of the observable
  `U.toObservable`.
* `measureObservableCircuit_op_qubitBasisZero_tmul_signMeasurement` — the same, with the target
  components written as the measurement operators `M₀`, `M₁` of `Observable.signMeasurement` — the
  projective measurement **of the observable `U`** (N&C §2.2.5).  This is the precise sense in which
  the circuit *implements a measurement of `U`*: the theorem proves the *pre-measurement* correlated
  state `|0⟩ ⊗ M₀x + |1⟩ ⊗ M₁x`, whose `|i⟩`-ancilla branch carries the target through the `i`-th
  measurement operator of that measurement.  A computational-basis measurement of the ancilla (read
  `0 ↦ +1`, `1 ↦ −1`) then collapses the target onto `Mᵢx` with Born weight `‖Mᵢx‖²` — the
  statistics and post-measurement states of the sign measurement of `U`.  That last step is the
  physical interpretation of the correlation, not part of what this theorem states (running the
  ancilla measurement explicitly is done in `MeasureObservableAncilla.lean`; see the
  `AxQM/NC/Ch4/Exercise4_34.lean` scope note).

The **deterministic eigenstate behaviour** — on a `±1` eigenstate input the ancilla flags the
eigenvalue and leaves the target unchanged — is stated in
`AxQM/NC/Ch4/Exercise4_34.lean` and proved from the circuit action here.

## Design notes

* **Fidelity to N&C.**  N&C's `U` is "both Hermitian and unitary, so it can be regarded
  both as an observable and a quantum gate."  We honour both roles literally: `U : Evolution qubit`
  supplies the *gate* (fed to `controlledUnitary`), and `U.toObservable hsa` (with
  `hsa : IsSelfAdjoint U.op`) supplies the *observable*, whose `signMeasurement` is precisely "the
  measurement of `U`."  The circuit action is a full operator identity on the whole target vector
  `x`, not a claim about selected inputs, so the two eigenprojector branches `P₊`, `P₋` capture the
  measurement completely (`P₊ + P₋ = I`).
* **Proof.**  The core identity is a direct computation at the raw tensor head: `H` on the control
  turns `|0⟩` into `(|0⟩ + |1⟩)/√2`; `C(U)` correlates the branches (`|1⟩` picks up `U` on the
  target); the second `H` interferes them into `|0⟩ ⊗ (I + U)/2 · x + |1⟩ ⊗ (I − U)/2 · x`.  The
  `√2` factors combine to the eigenprojector coefficient `1/2` (`Concrete.invSqrt2_mul_self`).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### A Hermitian gate viewed as an observable -/

/-- **A Hermitian gate as an observable.** A unitary evolution `U` (Postulate 5) that is
additionally self-adjoint is, by Postulate 2, an observable with the same underlying operator.
This is the object N&C's Exercise 4.34 calls "regarding `U` both as an observable and a quantum
gate": the gate is `U` itself, and the observable is `U.toObservable hsa`. -/
def Evolution.toObservable (U : Evolution S) (hsa : IsSelfAdjoint U.op) : Observable S where
  op := U.op
  selfAdjoint := hsa

/-- The underlying operator of `U.toObservable` is `U.op`. -/
@[simp]
theorem Evolution.toObservable_op (U : Evolution S) (hsa : IsSelfAdjoint U.op) :
    (U.toObservable hsa).op = U.op := rfl

/-- **A self-adjoint unitary is an involution:** `U² = I`.  From unitarity `U† U = I` and
self-adjointness `U† = U`, so `U U = U† U = I`.  This is the `±1`-observable hypothesis
(`A.op * A.op = 1`) required by `Observable.signMeasurement` and the eigenprojector API. -/
theorem Evolution.toObservable_op_mul_self (U : Evolution S) (hsa : IsSelfAdjoint U.op) :
    (U.toObservable hsa).op * (U.toObservable hsa).op = 1 := by
  rw [Evolution.toObservable_op]
  have hu : star U.op * U.op = 1 := (Unitary.mem_iff.mp U.unitary).1
  have hsa' : star U.op = U.op := hsa
  rwa [hsa'] at hu

/-! ### Vector-level action of the Hadamard gate on the computational basis -/

/-- The Hadamard gate on `|0⟩` at the vector level: `H|0⟩ = (|0⟩ + |1⟩)/√2`. The operator-applied
form of `hadamardGate_evolvePure_qubitBasis_zero` (`H|0⟩ = |+⟩`) expanded through
`qubitPlus_vec_eq_smul_add`. -/
theorem hadamardGate_op_qubitBasisVec_zero :
    hadamardGate.op (qubitBasis 0).vec
      = Concrete.invSqrt2 • ((qubitBasis 0).vec + (qubitBasis 1).vec) := by
  rw [← Evolution.evolvePure_vec, hadamardGate_evolvePure_qubitBasis_zero,
    qubitPlus_vec_eq_smul_add]

/-- The Hadamard gate on `|1⟩` at the vector level: `H|1⟩ = (|0⟩ − |1⟩)/√2`. The operator-applied
form of `hadamardGate_evolvePure_qubitBasis_one` (`H|1⟩ = |−⟩`) expanded through
`qubitMinus_vec_eq_smul_sub`. -/
theorem hadamardGate_op_qubitBasisVec_one :
    hadamardGate.op (qubitBasis 1).vec
      = Concrete.invSqrt2 • ((qubitBasis 0).vec - (qubitBasis 1).vec) := by
  rw [← Evolution.evolvePure_vec, hadamardGate_evolvePure_qubitBasis_one,
    qubitMinus_vec_eq_smul_sub]

/-! ### The measurement circuit and its action -/

/-- **The Hadamard-controlled-`U` measurement circuit** of Nielsen & Chuang Exercise 4.34: the
`Evolution` on `qubit ⊗ S` given by `(H ⊗ 1) · C(U) · (H ⊗ 1)` — a Hadamard on the control
(left/ancilla) qubit, then the controlled-`U` gate, then another Hadamard on the control.  Reading
the ancilla in the computational basis after this circuit is a measurement of the observable `U`.

The target register `S` is *arbitrary* (not just a single qubit): with `S = qubit` and a `±1`
(Hermitian, unitary) `U` this is Exercise 4.34's operator-measurement circuit, and with an arbitrary
target and an eigenstate input it is **Kitaev's phase-estimation circuit** (Problem 5.3), whose
control-measurement statistics read off the eigenphase. -/
def measureObservableCircuit (U : Evolution S) : Evolution (qubit ⊗ S) :=
  (hadamardGate.onLeft S).comp ((controlledUnitary U).comp (hadamardGate.onLeft S))

/-- **The measurement circuit splits over a product observable — the `H² = 1` block factorisation.**
Measuring the product `U · V` of two observables on the target register with one Hadamard-controlled
block is the same as measuring `U` and then `V` with two separate blocks:
`measureObservableCircuit (U · V) = measureObservableCircuit U · measureObservableCircuit V`.

The controlled gate splits, `C(U·V) = C(U)·C(V)` (`controlledUnitary_comp`, the lemma this mirrors),
and the two ancilla Hadamards that meet where the blocks join annihilate — `H² = 1` on the ancilla
wire (`hadamardOnLeft_sq`, the `(H.onLeft S)·(H.onLeft S) = 1` lemma, whose
`Evolution.onLeft_comp`/`id_onLeft` reduction carries the Hadamard involution through
`TensorProduct.mapL`) — leaving the single block
`(H ⊗ 1)·C(U)·C(V)·(H ⊗ 1)` for `U·V`. Stated for an arbitrary target `S`, so a generator on any
number of data qubits factors one Pauli at a time.

This is the identity by which a syndrome-measurement block for a *product* of stabilizer generators
(Nielsen & Chuang Figure 10.16) is rewritten as a *sequence* of single-generator blocks
(Exercise 10.59), each then simplified in isolation by the Figures 10.14 / 10.15 identities. -/
theorem measureObservableCircuit_comp (U V : Evolution S) :
    measureObservableCircuit (U.comp V)
      = (measureObservableCircuit U).comp (measureObservableCircuit V) := by
  simp only [measureObservableCircuit, ← controlledUnitary_comp, Evolution.comp_assoc]
  rw [← Evolution.comp_assoc (hadamardGate.onLeft S) (hadamardGate.onLeft S),
    hadamardOnLeft_sq S, Evolution.id_comp]

/-- **Measuring the identity observable is the identity circuit:** `measureObservableCircuit 1 = 1`.
Controlling the identity gate does nothing (`controlledUnitary_id`, `C(1) = 1`), leaving the two
ancilla Hadamards adjacent, and they annihilate (`hadamardOnLeft_sq`, `H² = 1` on the ancilla wire).
This is the *unit* law that, with the *product* law `measureObservableCircuit_comp`, makes
`measureObservableCircuit` a composition-monoid homomorphism; see
`measureObservableCircuit_listComp`. -/
theorem measureObservableCircuit_id :
    measureObservableCircuit (Evolution.id : Evolution S) = Evolution.id := by
  simp only [measureObservableCircuit, controlledUnitary_id, Evolution.id_comp]
  exact hadamardOnLeft_sq S

/-- **The measurement circuit splits over a product of any length — the `n`-fold `H² = 1` block
factorisation.** Measuring the ordered product `L.prod` of a list `L` of observables on the target
with one Hadamard-controlled block equals the product of the per-factor blocks:
`measureObservableCircuit L.prod = (L.map measureObservableCircuit).prod`. The product is the one of
the gate monoid `Evolution.instMonoid` (unit `Evolution.id`, multiplication `Evolution.comp`), so
this is exactly the statement that `measureObservableCircuit` is a *monoid homomorphism*
`(Evolution S, ·, 1) → (Evolution (qubit ⊗ S), ·, 1)` — the `n`-ary form of
`measureObservableCircuit_comp` (`map_mul`) with unit `measureObservableCircuit_id` (`map_one`),
proved by induction on `L`.

This is the Nielsen & Chuang Figure 10.16 → Figure 10.17 block step in full generality: a single
ancilla's block for a stabilizer generator `gₐ = ∏ᵢ Pᵢ` — a product of single-wire Paulis of *any*
weight — becomes the *sequence* of one-Pauli blocks, the ancilla Hadamards between consecutive
factors having annihilated. Each one-factor block `measureObservableCircuit Pᵢ` is then compiled to
its reversed-CNOT Figure-10.17 form on its data wire by a register lift
(`measureObservableCircuit_onLeft` / `_onRight` / `_onMiddle`) and the atomic Figures 10.14 / 10.15
identities (Exercise 10.59). -/
theorem measureObservableCircuit_listComp (L : List (Evolution S)) :
    measureObservableCircuit L.prod = (L.map measureObservableCircuit).prod := by
  induction L with
  | nil =>
    simp only [List.prod_nil, List.map_nil, Evolution.one_def]
    exact measureObservableCircuit_id
  | cons f t ih =>
    rw [List.prod_cons, Evolution.mul_def, measureObservableCircuit_comp, ih, List.map_cons,
      List.prod_cons, Evolution.mul_def]

/-- **The measurement circuit's action** (Nielsen & Chuang Exercise 4.34).  With the ancilla
prepared in `|0⟩`, the circuit sends `|0⟩ ⊗ x` to
`|0⟩ ⊗ ½(I + U)x + |1⟩ ⊗ ½(I − U)x`: the ancilla `|0⟩` branch carries the target through the `+1`
eigenprojector `P₊ = ½(I + U)` and the `|1⟩` branch through the `−1` eigenprojector `P₋ = ½(I − U)`.

Stated at the raw operator level (`½(x ± U·x)`), so it holds for *every* target vector `x` and needs
no self-adjointness hypothesis; the eigenprojector / measurement readings are the corollaries below.

Proof: `H` turns the control `|0⟩` into `(|0⟩ + |1⟩)/√2`; `C(U)` applies `U` on the `|1⟩` branch
only, giving `(|0⟩ ⊗ x + |1⟩ ⊗ Ux)/√2`; the second `H` interferes the control back, and the two
`1/√2` factors combine (`invSqrt2_mul_self`) into the `1/2` of the eigenprojectors. -/
theorem measureObservableCircuit_op_qubitBasisZero_tmul (U : Evolution S) (x : S.space) :
    (measureObservableCircuit U).op ((qubitBasis 0).vec ⊗ₜ[ℂ] x)
      = (qubitBasis 0).vec ⊗ₜ[ℂ] ((2⁻¹ : ℂ) • (x + U.op x))
        + (qubitBasis 1).vec ⊗ₜ[ℂ] ((2⁻¹ : ℂ) • (x - U.op x)) := by
  -- Restate the whole circuit at the *raw* tensor head.  The two operators written below are the
  -- definitional forms of the gates — `(hadamardGate.onLeft qubit).op = mapL H.op 1` (`Evolution`
  -- `.onLeft`/`tmul_op`/`id_op`) and `(controlledUnitary U).op = mapL |0⟩⟨0| 1 + mapL |1⟩⟨1| U.op`
  -- (`controlledUnitary_op`, which is `rfl`) — so this `change` is a definitional re-heading, not
  -- an independent hand-derivation.  It is required (not `rw`/`simp only [controlledUnitary_op]`)
  -- because that lemma leaves the operator at the *composite* head `(qubit ⊗ qubit).space →L …`,
  -- where the bundled `+`/`•` block `ContinuousLinearMap.add_apply` / `map_add` / `map_smul` when
  -- applied to a raw-tensor argument; at the raw head all the `TensorProduct.mapL` and CLM algebra
  -- fires uniformly.  This mirrors the sibling `controlledUnitary_op_mem_unitary` / `_comp` /
  -- `_onRight_conj` lemmas, which restate the same operator at the raw head.
  change (TensorProduct.mapL hadamardGate.op (1 : S.space →L[ℂ] S.space))
      ((TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
            (1 : S.space →L[ℂ] S.space)
          + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
              U.op)
        ((TensorProduct.mapL hadamardGate.op (1 : S.space →L[ℂ] S.space))
          ((qubitBasis 0).vec ⊗ₜ[ℂ] x))) = _
  rw [TensorProduct.mapL_tmul, one_apply_eq_self, hadamardGate_op_qubitBasisVec_zero,
    ← TensorProduct.smul_tmul', TensorProduct.add_tmul, smul_add]
  -- After the first Hadamard: `(|0⟩⊗x)/√2 + (|1⟩⊗x)/√2`.  Distribute `C(U)` over the sum.
  simp only [_root_.add_apply, map_add, map_smul, TensorProduct.mapL_tmul,
    one_apply_eq_self, InnerProductSpace.rankOne_apply, qubitBasis_inner_qubitBasis]
  -- After `C(U)`: `(|0⟩⊗x)/√2 + (|1⟩⊗Ux)/√2`.  Apply the second Hadamard and collapse the
  -- projector coefficients (`⟨i|j⟩ = δᵢⱼ`, `Fin.reduceEq`).
  simp only [hadamardGate_op_qubitBasisVec_zero, hadamardGate_op_qubitBasisVec_one, ite_true,
    Fin.reduceEq, ite_false, one_smul, zero_smul, TensorProduct.zero_tmul, add_zero, zero_add]
  -- Combine the two `1/√2` factors into `1/2` and distribute both sides into the four basis atoms.
  rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', smul_smul, smul_smul,
    Concrete.invSqrt2_mul_self]
  simp only [TensorProduct.add_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_add,
    TensorProduct.tmul_sub, TensorProduct.tmul_smul, smul_add, smul_sub]
  module

/-- **The measurement circuit's action in terms of the eigenprojectors of `U`.**  With the ancilla
in `|0⟩`, the circuit sends `|0⟩ ⊗ x` to `|0⟩ ⊗ P₊x + |1⟩ ⊗ P₋x`, where `P₊ = Observable.projPlus`
and `P₋ = Observable.projMinus` are the `±1` eigenprojectors of the observable `U.toObservable hsa`.
Restatement of `measureObservableCircuit_op_qubitBasisZero_tmul` recognising `½(x ± U·x)` as the
eigenprojectors applied to `x`. -/
theorem measureObservableCircuit_op_qubitBasisZero_tmul_projMeas (U : Evolution S)
    (hsa : IsSelfAdjoint U.op) (x : S.space) :
    (measureObservableCircuit U).op ((qubitBasis 0).vec ⊗ₜ[ℂ] x)
      = (qubitBasis 0).vec ⊗ₜ[ℂ] ((U.toObservable hsa).projPlus x)
        + (qubitBasis 1).vec ⊗ₜ[ℂ] ((U.toObservable hsa).projMinus x) := by
  have hplus : (2⁻¹ : ℂ) • (x + U.op x) = (U.toObservable hsa).projPlus x := by
    simp only [Observable.projPlus, Evolution.toObservable_op, _root_.smul_apply,
      _root_.add_apply, one_apply_eq_self]
  have hminus : (2⁻¹ : ℂ) • (x - U.op x) = (U.toObservable hsa).projMinus x := by
    simp only [Observable.projMinus, Evolution.toObservable_op, _root_.smul_apply,
      _root_.sub_apply, one_apply_eq_self]
  rw [measureObservableCircuit_op_qubitBasisZero_tmul, hplus, hminus]

/-- **The circuit implements the measurement of the observable `U`.**  With the ancilla in `|0⟩`,
the circuit sends `|0⟩ ⊗ x` to `|0⟩ ⊗ M₀x + |1⟩ ⊗ M₁x`, where `M₀`, `M₁` are the two measurement
operators of `Observable.signMeasurement` — the projective measurement *of the observable `U`*
(N&C §2.2.5), with `M₀ = P₊` (outcome `+1`) and `M₁ = P₋` (outcome `−1`).  Thus reading the ancilla
in the computational basis after the circuit and interpreting `0 ↦ +1`, `1 ↦ −1` realises exactly
that measurement: outcome `i` occurs with probability `‖Mᵢx‖²` and leaves the target in the
(unnormalised) collapsed state `Mᵢx` — an eigenvector of `U` with the corresponding eigenvalue. -/
theorem measureObservableCircuit_op_qubitBasisZero_tmul_signMeasurement (U : Evolution S)
    (hsa : IsSelfAdjoint U.op) (x : S.space) :
    (measureObservableCircuit U).op ((qubitBasis 0).vec ⊗ₜ[ℂ] x)
      = (qubitBasis 0).vec ⊗ₜ[ℂ]
          (((U.toObservable hsa).signMeasurement (U.toObservable_op_mul_self hsa)).op 0 x)
        + (qubitBasis 1).vec ⊗ₜ[ℂ]
          (((U.toObservable hsa).signMeasurement (U.toObservable_op_mul_self hsa)).op 1 x) := by
  simp only [Observable.signMeasurement_op_zero, Observable.signMeasurement_op_one]
  exact measureObservableCircuit_op_qubitBasisZero_tmul_projMeas U hsa x

end AxQM
