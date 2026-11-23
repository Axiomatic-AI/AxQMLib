/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledZ

/-!
# AxQM.Postulates.API — the SWAP gate and the symmetry of controlled-`Z`

The two-qubit `SWAP` gate and the operator identity behind Nielsen & Chuang Exercise 4.18 (the
controlled-`Z` gate is symmetric between the control and target qubits). Compare
`controlledUnitary`, `cnotGate`, and `controlledZGate`.

## What is formalised

* `Evolution.swap` — the **`SWAP` gate** `SWAP` on `S ⊗ S`, the closed-system evolution that
  exchanges the two factors of an identical-system composite. It is
  `Evolution.ofLinearIsometryEquiv` of the factor-swap `TensorProduct.commIsometry`, so it is
  grounded in Postulate 5 and its action is `SWAP(x ⊗ y) = y ⊗ x` (`Evolution.swap_op_tmul`).
* `Evolution.swap_op_eq` — the gate as an operator: `SWAP.op = commIsometry` (as a continuous
  linear map). It transports the `commIsometry` algebra to the gate.
* `Evolution.swap_comp_self` — `SWAP` is an involution: `SWAP · SWAP = 1` (swapping twice is the
  identity).
* `pauliZGate_op_eq_rankOne_sub` — the **spectral decomposition of `Z` at the operator level**:
  `Z = |0⟩⟨0| - |1⟩⟨1|`, the qubit-space image of the concrete matrix identity `pauliZ =
  outerSelf(ket 0) - outerSelf(ket 1)` (Exercise 2.9). Uses
  `toEuclideanCLM_outerSelf_ket : toEuclideanCLM |i⟩⟨i| = |i⟩⟨i|` between the concrete outer product
  and the rank-one projector.
* `controlledZGate_swap_conj_op` — **the operator identity of Exercise 4.18:** conjugating the
  controlled-`Z` operator by the factor-swap leaves it unchanged, `SWAP · CZ · SWAP = CZ`. It gives
  the gate equality (via `Evolution.ext`) stated in `AxQM/NC/Ch4/Exercise4_18.lean`.

## Design notes

* **Why the SWAP-conjugation shape (N&C fidelity).** N&C Exercise 4.18 asks to show, as a circuit
  identity, that the controlled-`Z` gate is *symmetric* under interchanging its control and target
  qubits: the gate obtained by treating the second qubit as control equals the original.
  Interchanging the two qubits of a gate `U` is exactly conjugation by `SWAP` (`SWAP · U · SWAP`
  runs `U` with the two qubits swapped), so "controlled-`Z` is symmetric between control and
  target" is faithfully the equality `SWAP · CZ · SWAP = CZ` — equivalently, `CZ` commutes with
  `SWAP`. This is a full unitary identity (an equality of `Evolution`s), not an "on basis states"
  surrogate.
* **Proof.** With `CZ.op = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ Z` (`controlledZGate_op`), swap-conjugation of a
  tensor-product operator interchanges its factors (`TensorProduct.commIsometry_conj_mapL`, in
  `ToMathlib`), so `SWAP · CZ · SWAP = I ⊗ |0⟩⟨0| + Z ⊗ |1⟩⟨1|`. Substituting `I = |0⟩⟨0| + |1⟩⟨1|`
  (`sum_rankOne_qubitBasis_eq_one`) and `Z = |0⟩⟨0| - |1⟩⟨1|` (`pauliZGate_op_eq_rankOne_sub`) and
  expanding by bilinearity of `TensorProduct.mapL`, both sides equal the manifestly symmetric
  `|0⟩⟨0|⊗|0⟩⟨0| + |0⟩⟨0|⊗|1⟩⟨1| + |1⟩⟨1|⊗|0⟩⟨0| - |1⟩⟨1|⊗|1⟩⟨1|`, closed by `abel`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The SWAP gate -/

/-- **The `SWAP` gate** on `S ⊗ S` (Nielsen & Chuang §1.3.4): the closed-system `Evolution` that
exchanges the two factors of an identical-system composite, `SWAP(x ⊗ y) = y ⊗ x`. It is
`Evolution.ofLinearIsometryEquiv` of the factor-swap isometry `TensorProduct.commIsometry`, so it is
grounded in the `Evolution` primitive with unitarity inherited from that isometry. -/
def Evolution.swap : Evolution (S ⊗ S) :=
  Evolution.ofLinearIsometryEquiv (TensorProduct.commIsometry ℂ S.space S.space)

/-- **Action of the `SWAP` gate** on a product vector: `SWAP(x ⊗ y) = y ⊗ x`. -/
@[simp]
theorem Evolution.swap_op_tmul (x y : S.space) :
    (Evolution.swap (S := S)).op (x ⊗ₜ[ℂ] y) = y ⊗ₜ[ℂ] x := by
  rw [Evolution.swap]
  have h := Evolution.ofLinearIsometryEquiv_op_apply (S := S ⊗ S)
    (TensorProduct.commIsometry ℂ S.space S.space) (x ⊗ₜ[ℂ] y)
  rw [h]
  exact TensorProduct.comm_tmul ℂ S.space S.space x y

/-- **Action of the `SWAP` gate on a product pure state:** `SWAP(ψ ⊗ φ) = φ ⊗ ψ`. The
`evolvePure`-level companion of `Evolution.swap_op_tmul`, used to compute circuits built from
`SWAP` on computational-basis inputs one tensor factor at a time. -/
@[simp]
theorem Evolution.swap_evolvePure_tmul (ψ φ : PureState S) :
    (Evolution.swap (S := S)).evolvePure (ψ ⊗ φ) = φ ⊗ ψ := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, PureState.tmul_vec, PureState.tmul_vec, Evolution.swap_op_tmul]

/-- The underlying operator of the `SWAP` gate is the factor-swap `commIsometry`. The bridge from
the `Evolution` gate to the `commIsometry` algebra. -/
theorem Evolution.swap_op_eq :
    (Evolution.swap (S := S)).op
      = (TensorProduct.commIsometry ℂ S.space S.space :
          S.space ⊗[ℂ] S.space →L[ℂ] S.space ⊗[ℂ] S.space) := by
  ext z
  rw [Evolution.swap]
  have h := Evolution.ofLinearIsometryEquiv_op_apply (S := S ⊗ S)
    (TensorProduct.commIsometry ℂ S.space S.space) z
  rw [h]
  rfl

/-- **The `SWAP` gate is an involution:** `SWAP · SWAP = 1`. Swapping the two factors twice is the
identity, from the involutivity of `commIsometry` (`TensorProduct.commIsometry_comp_self`). -/
theorem Evolution.swap_comp_self :
    (Evolution.swap (S := S)).comp (Evolution.swap (S := S)) = Evolution.id := by
  apply Evolution.ext
  rw [Evolution.comp_op, Evolution.id_op, Evolution.swap_op_eq]
  exact TensorProduct.commIsometry_comp_self

/-! ### Spectral decomposition of the Pauli-`Z` gate -/

/-- **Bridge:** the concrete outer product `|i⟩⟨i|` (as a matrix) promoted through
`Matrix.toEuclideanCLM` is the rank-one projector `|i⟩⟨i|` on the qubit space:
`toEuclideanCLM (outerSelf (ket i)) = |i⟩⟨i|`. -/
theorem toEuclideanCLM_outerSelf_ket (i : Fin 2) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.outerSelf (Concrete.ket i))
      = InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec := by
  apply ContinuousLinearMap.coe_injective
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Concrete.outerSelf,
    ← InnerProductSpace.symm_toEuclideanLin_rankOne, LinearEquiv.apply_symm_apply]
  rfl

/-- **Spectral decomposition of the Pauli-`Z` gate at the operator level:**
`Z = |0⟩⟨0| - |1⟩⟨1|`. The qubit-space image of the concrete matrix identity
`Concrete.pauliZ = outerSelf(ket 0) - outerSelf(ket 1)` (Nielsen & Chuang Exercise 2.9),
transported through the `⋆`-algebra map `Matrix.toEuclideanCLM` (which respects subtraction) via
`toEuclideanCLM_outerSelf_ket`. -/
theorem pauliZGate_op_eq_rankOne_sub :
    pauliZGate.op
      = InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec
        - InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec := by
  rw [pauliZGate_op, Concrete.pauliZ_eq_outerSelf_sub, map_sub,
    toEuclideanCLM_outerSelf_ket, toEuclideanCLM_outerSelf_ket]
  rfl

/-! ### Symmetry of the controlled-`Z` gate -/

/-- **Operator form of Nielsen & Chuang Exercise 4.18** (controlled-`Z` is symmetric between control
and target): conjugating the controlled-`Z` operator by the factor-swap leaves it unchanged,
`SWAP · CZ · SWAP = CZ` at the level of operators. Interchanging the two qubits turns
`|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ Z` into `I ⊗ |0⟩⟨0| + Z ⊗ |1⟩⟨1|` (`TensorProduct.commIsometry_conj_mapL`),
and the two coincide once `I = |0⟩⟨0| + |1⟩⟨1|` and `Z = |0⟩⟨0| - |1⟩⟨1|` are expanded (both are the
symmetric operator `∑_{i,j} (-1)^{ij} |i⟩⟨i| ⊗ |j⟩⟨j|`). -/
theorem controlledZGate_swap_conj_op :
    (Evolution.swap (S := qubit)).op.comp
        (controlledZGate.op.comp (Evolution.swap (S := qubit)).op) = controlledZGate.op := by
  have h1 : (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec
      + InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
      = (1 : qubit.space →L[ℂ] qubit.space) := by
    have := sum_rankOne_qubitBasis_eq_one
    rwa [Fin.sum_univ_two] at this
  rw [Evolution.swap_op_eq, controlledZGate_op]
  -- Restate the composition at the raw tensor head `qubit.space ⊗[ℂ] qubit.space`, where the
  -- `commIsometry`/`mapL` composition algebra applies (the composite `(qubit ⊗ qubit).space` head
  -- would block the `add_comp`/conjugation rewrites by presenting a different, defeq, `.comp`).
  change (TensorProduct.commIsometry ℂ qubit.space qubit.space :
        qubit.space ⊗[ℂ] qubit.space →L[ℂ] qubit.space ⊗[ℂ] qubit.space).comp
      ((TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec) 1
        + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
            pauliZGate.op).comp
        (TensorProduct.commIsometry ℂ qubit.space qubit.space :
          qubit.space ⊗[ℂ] qubit.space →L[ℂ] qubit.space ⊗[ℂ] qubit.space))
    = TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec) 1
      + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
          pauliZGate.op
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    TensorProduct.commIsometry_conj_mapL, TensorProduct.commIsometry_conj_mapL,
    pauliZGate_op_eq_rankOne_sub, ← h1]
  simp only [TensorProduct.mapL_add_left, TensorProduct.mapL_add_right,
    TensorProduct.mapL_sub_left, TensorProduct.mapL_sub_right]
  abel

end AxQM
