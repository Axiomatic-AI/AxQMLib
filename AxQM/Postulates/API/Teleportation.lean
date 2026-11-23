/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledUnitary
import AxQM.Postulates.API.BellBasis
import AxQM.Postulates.API.Associator
import AxQM.Postulates.Measurement

/-!
# AxQM.Postulates.API — Pauli corrections and Bell-basis measurement

The two non-CNOT resources of Nielsen & Chuang **Problem 4.6** ("Universality with prior
entanglement"): the **single-qubit unitaries** used as teleportation corrections (the Pauli
byproduct gates) and the **Bell-basis measurement** of a qubit pair.  Together with the
four-qubit entangled resource state, these implement a CNOT by gate
teleportation and so form a universal set.

## What is formalised

* `pauliZGate` — the Pauli-`Z` gate as an `Evolution qubit`, obtained (like `pauliXGate`) by
  promoting `Concrete.pauliZ = !![1,0;0,-1]` through `Matrix.toEuclideanCLM`; unitarity is
  transported from `Concrete.pauliZ_mem_unitaryGroup`.  `pauliZGate_op_apply_qubitBasis` is the
  phase-flip action `Z|i⟩ = (-1)ⁱ |i⟩`.
* `pauliXGate_op_apply_qubitBasis` — the operator-level bit flip `X|i⟩ = |i ⊕ 1⟩`, the
  `Evolution.op` form of `pauliXGate_evolvePure_qubitBasis` (from `ControlledUnitary`).
* `pauliByproduct x y` — the **Pauli byproduct** correction `X^y Z^x` (`x, y : Fin 2`) as an
  `Evolution qubit`, i.e. a genuine *single-qubit unitary* (resource #1 of Problem 4.6): the
  correction applied to the teleported qubit for the Bell-measurement outcome `(x, y)`.
  `pauliByproduct_op_apply_qubitBasis` is its computational-basis action
  `X^y Z^x |j⟩ = (-1)^{x·j} |j ⊕ y⟩` — the phase `(-1)^{x·j}` from `Z^x` and the bit flip
  `j ↦ j ⊕ y` from `X^y`.
* `bellMeasurement` — the **Bell-basis measurement** of a qubit pair (resource #2 of Problem 4.6):
  the projective measurement `Measurement.ofOrthonormalBasis bellBasis` of `qubit ⊗ qubit`, with
  outcomes indexed by `Fin 2 × Fin 2` and operators the Bell projectors `|β_xy⟩⟨β_xy|`
  (`bellMeasurement_op`).
* `teleportation_identity` — the **single-qubit teleportation identity** (Nielsen & Chuang §1.3.7):
  for an arbitrary qubit state `|ψ⟩`, re-associating `|ψ⟩ ⊗ |Φ⁺⟩` and grouping the first two qubits,
  `|ψ⟩ ⊗ |Φ⁺⟩ = ½ Σ_{x,y} |β_xy⟩ ⊗ (X^y Z^x |ψ⟩)`.  A Bell measurement of the first pair then leaves
  the third qubit in `X^y Z^x |ψ⟩`, undone by the single-qubit correction `pauliByproduct x y`: the
  single-qubit special case of the Problem 4.6 gate-teleportation protocol.  Proved directly by
  expanding `|ψ⟩` over the computational basis.  `teleportation_identity_qubitBasis` is its
  specialisation to a basis input `|i⟩` (the concrete form N&C states first).
* `assoc_toIsometry_tmul_bellPhiPlus` / `bellBasisVec_tmul` — the raw tensor-distribution helpers
  the identity is assembled from (the associated `v ⊗ |Φ⁺⟩`; the expansion of `|β_xy⟩ ⊗ w`),
  building on the general `assoc_toIsometry_tmul_tmul` of `Postulates/API/Associator.lean`.

## Design notes

* **Corrections are single-qubit unitaries.**  Problem 4.6 allows only single-qubit unitaries as
  active operations (besides the Bell measurement and state preparation).  Packaging each Pauli
  byproduct `X^y Z^x` as an honest `Evolution qubit` records exactly this: the teleportation
  correction is an `Evolution` (Postulate 5), so it *is* an admissible
  single-qubit gate.  `pauliByproduct` is built from `Evolution.comp` of the `x`/`y`-selected
  Pauli gates (identity when the bit is `0`).
* **Byproduct convention.**  `X^y Z^x` (in this order) is the correction pairing with the Bell
  outcome `β_xy`; on `|j⟩` the `Z^x` factor is diagonal, giving `(-1)^{x·j}`, and `X^y` then flips
  `j ↦ j ⊕ y`.  This is the convention that makes the single-qubit teleportation
  identity `|ψ⟩ ⊗ |Φ⁺⟩ = ½ ∑_{x,y} |β_xy⟩ ⊗ (X^y Z^x |ψ⟩)` hold on the nose.
* **Tensor-head friction in the teleportation identity.**  The composite `(qubit ⊗ qubit).space` and
  the raw `qubit.space ⊗[ℂ] qubit.space` are definitionally equal but present different heads, and
  the `bellVec` / `bellBasisVec` summands live at the raw head while the outer tensors (through the
  associator and `bellBasisVec ⊗ ·`) sit at the composite head; so the tensor bilinearity lemmas
  (`tmul_add`, `add_tmul`, `smul_tmul'`) do not fire across the mismatch.  The distribution helpers
  restate the outer tensor at the raw head with a `change` before rewriting.  The identity
  is then a linear identity over the eight three-qubit computational basis vectors: both sides are
  fully distributed to `scalar • (|a⟩⊗|b⟩)⊗|c⟩` atoms, and a closing `change` re-elaborates those
  atoms with canonical instances (the atoms produced by the two construction paths are defeq but
  carry different instance arguments, which `module`'s atom-matching distinguishes) so `module`
  closes it.  `assoc_toIsometry_tmul_bellPhiPlus`'s own `map_smul`/`map_add` step keeps the
  associator's `ℂ`-linearity in term mode (`rw`/`simp` will not rewrite through the
  `LinearIsometryEquiv` coercion here).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-! ### The Pauli-`Z` gate -/

/-- The **Pauli-`Z` gate** `Z` (the phase flip) as a closed-system `Evolution` of the qubit:
its operator is the concrete matrix `Concrete.pauliZ = !![1,0;0,-1]` promoted through
`Matrix.toEuclideanCLM`, with unitarity transported from `Concrete.pauliZ_mem_unitaryGroup`. -/
def pauliZGate : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliZ
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) Concrete.pauliZ_mem_unitaryGroup

/-- The underlying operator of `pauliZGate` is `Matrix.toEuclideanCLM Concrete.pauliZ`. -/
@[simp]
theorem pauliZGate_op :
    pauliZGate.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliZ := rfl

/-- **The Pauli-`Z` gate phase-flips the computational basis:** `Z|i⟩ = (-1)ⁱ |i⟩`, i.e.
`pauliZGate.op` sends `|i⟩` to `(-1)ⁱ • |i⟩`. -/
theorem pauliZGate_op_apply_qubitBasis (i : Fin 2) :
    pauliZGate.op (qubitBasis i).vec = (-1 : ℂ) ^ (i : ℕ) • (qubitBasis i).vec := by
  rw [pauliZGate_op, qubitBasis_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliZ)
        (EuclideanSpace.single i 1)).ofLp
      = ((-1 : ℂ) ^ (i : ℕ) • (EuclideanSpace.single i 1 : EuclideanSpace ℂ (Fin 2))).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases i <;> fin_cases j <;>
      simp [Concrete.pauliZ, Matrix.mulVec, dotProduct, EuclideanSpace.single]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-- The Pauli-`X` gate action on the computational basis at operator level, `X|i⟩ = |i ⊕ 1⟩`
(the `Evolution.op` form of `pauliXGate_evolvePure_qubitBasis`). -/
theorem pauliXGate_op_apply_qubitBasis (i : Fin 2) :
    pauliXGate.op (qubitBasis i).vec = (qubitBasis (i + 1)).vec := by
  rw [← Evolution.evolvePure_vec]
  exact congrArg PureState.vec (pauliXGate_evolvePure_qubitBasis i)

/-! ### The Pauli byproduct correction -/

/-- The **Pauli byproduct** `X^y Z^x` (`x, y : Fin 2`) as an `Evolution qubit`: the single-qubit
unitary correction applied to the teleported qubit given a Bell measurement outcome `(x, y)`.  For
`y = 0` the `X` factor is the identity, for `y = 1` it is `pauliXGate`; likewise `x` selects
`pauliZGate`.  Being a value of `Evolution` (Postulate 5), it is manifestly an admissible
single-qubit gate — resource #1 of Problem 4.6. -/
def pauliByproduct (x y : Fin 2) : Evolution qubit :=
  (if y = 0 then Evolution.id else pauliXGate).comp (if x = 0 then Evolution.id else pauliZGate)

/-- **Computational-basis action of the Pauli byproduct:** `X^y Z^x |j⟩ = (-1)^{x·j} |j ⊕ y⟩`.
The `Z^x` factor contributes the phase `(-1)^{x·j}` and the `X^y` factor the bit flip
`j ↦ j ⊕ y`. -/
theorem pauliByproduct_op_apply_qubitBasis (x y j : Fin 2) :
    (pauliByproduct x y).op (qubitBasis j).vec
      = (-1 : ℂ) ^ ((x : ℕ) * (j : ℕ)) • (qubitBasis (j + y)).vec := by
  rw [pauliByproduct]
  fin_cases x <;> fin_cases y <;>
    simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, Evolution.comp_op,
      Evolution.id_op, ContinuousLinearMap.comp_apply, one_apply_eq_self,
      pauliXGate_op_apply_qubitBasis, pauliZGate_op_apply_qubitBasis, map_smul,
      Nat.zero_mul, Nat.one_mul, pow_zero, one_smul, add_zero]

/-! ### The Bell-basis measurement -/

/-- The **Bell-basis measurement** of a qubit pair (Problem 4.6 resource #2): the projective
measurement of `qubit ⊗ qubit` in the Bell basis, `Measurement.ofOrthonormalBasis bellBasis`, with
outcomes indexed by `Fin 2 × Fin 2`.  It is a genuine `Measurement` (Postulate 3). -/
def bellMeasurement : Measurement (Fin 2 × Fin 2) (qubit ⊗ qubit) :=
  Measurement.ofOrthonormalBasis bellBasis

/-- The Bell-measurement operator for outcome `(x, y)` is the Bell projector `|β_xy⟩⟨β_xy|`. -/
@[simp]
theorem bellMeasurement_op (p : Fin 2 × Fin 2) :
    bellMeasurement.op p = rankOne ℂ (bellBasisVec p.1 p.2) (bellBasisVec p.1 p.2) := by
  rw [bellMeasurement, Measurement.ofOrthonormalBasis_op, bellBasis_apply, bellState_vec]

/-- **The POVM elements of the Bell measurement (Nielsen & Chuang Exercise 4.33).**  The POVM
element for outcome `(x, y)` is the projector onto the Bell state,
`bellMeasurement.toPOVM.elements (x, y) = |β_xy⟩⟨β_xy|`.  Since each measurement operator is a unit
rank-one projector it equals its own POVM element, so the four Bell projectors are simultaneously
the measurement operators and the POVM elements — the answer N&C asks for. -/
theorem bellMeasurement_toPOVM_elements_eq_bellProjector (x y : Fin 2) :
    bellMeasurement.toPOVM.elements (x, y)
      = ((InnerProductSpace.rankOne ℂ) (bellState x y).vec) (bellState x y).vec := by
  rw [Measurement.toPOVM_elements]
  simp only [bellMeasurement_op]
  rw [InnerProductSpace.adjoint_rankOne_comp_self (bellBasisVec_norm x y), bellState_vec]

/-- **Measuring a Bell state in the Bell basis reads out which Bell state it is:** the Born-rule
probability of outcome `q` on `|β_xy⟩` is `1` if `q = (x, y)` and `0` otherwise.  (`bellMeasurement`
is the projective measurement in the Bell basis; `bornProb` is the Born rule, Postulate 3.)
The diagonal case `q = (x, y)` is deterministic because the Bell states are orthonormal
(`bellBasisVec_inner`). -/
theorem bellMeasurement_bornProb_bellState (x y : Fin 2) (q : Fin 2 × Fin 2) :
    bellMeasurement.bornProb ((bellState x y).toState) q = if q = (x, y) then 1 else 0 := by
  change bellMeasurement.toPOVM.toPMF (bellState x y).toState.op q = _
  rw [bellMeasurement, Measurement.toPOVM_ofOrthonormalBasis, PureState.toState_op,
    POVM.toPMF_rankOne_self, POVM.ofOrthonormalBasis_elements,
    ContinuousLinearMap.reApplyInnerSelf_apply, InnerProductSpace.rankOne_apply,
    inner_smul_left, bellBasis_apply, bellState_vec, bellState_vec]
  simp only [bellBasisVec_inner]
  split_ifs with h <;> simp

/-! ### The single-qubit teleportation identity -/

/-- Distribute the tensor `|β_xy⟩ ⊗ w` of a Bell vector with any vector `w`, pulling the Bell
normalisation and sign out to the raw tensor head:
`|β_xy⟩ ⊗ w = (√2)⁻¹ ((|0⟩⊗|y⟩)⊗w + (-1)ˣ (|1⟩⊗|ȳ⟩)⊗w)`.  The `change` restates `bellBasisVec`'s
`+`/`•` (which live at the raw `qubit.space ⊗ qubit.space` head) so `TensorProduct.add_tmul` and
`TensorProduct.smul_tmul'` fire on the outer tensor. -/
theorem bellBasisVec_tmul {S : QSystem} (x y : Fin 2) (w : S.space) :
    bellBasisVec x y ⊗ₜ[ℂ] w
      = (Real.sqrt 2 : ℂ)⁻¹ • (((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis y).vec) ⊗ₜ[ℂ] w
          + (-1 : ℂ) ^ (x : ℕ) •
            (((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis (y + 1)).vec) ⊗ₜ[ℂ] w)) := by
  change ((Real.sqrt 2 : ℂ)⁻¹ • ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis y).vec
      + (-1 : ℂ) ^ (x : ℕ) • ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis (y + 1)).vec))
      : qubit.space ⊗[ℂ] qubit.space) ⊗ₜ[ℂ] w = _
  rw [← TensorProduct.smul_tmul', TensorProduct.add_tmul, ← TensorProduct.smul_tmul']

/-- Apply the associator to `v ⊗ |Φ⁺⟩`, distributing the Bell normalisation and re-bracketing to
the left-nested `(v ⊗ ·) ⊗ ·` head: `assoc (v ⊗ |Φ⁺⟩) = (√2)⁻¹ ((v⊗|0⟩)⊗|0⟩ + (v⊗|1⟩)⊗|1⟩)`.
The `change` restates `|Φ⁺⟩`'s `+`/`•` (which live at the raw `qubit.space ⊗ qubit.space` head) so
`TensorProduct.tmul_add` fires on the outer tensor; each pure summand `(v⊗|k⟩)⊗|k⟩` is rewritten
back into `assoc (v ⊗ (|k⟩⊗|k⟩))` by `assoc_toIsometry_tmul_tmul`, and the associator's
`ℂ`-linearity (`map_smul`, `map_add`) then discharges the normalisation and the sum. -/
theorem assoc_toIsometry_tmul_bellPhiPlus (v : qubit.space) :
    (QSystem.assoc qubit qubit qubit).toIsometry (v ⊗ₜ[ℂ] bellPhiPlus.vec)
      = (Real.sqrt 2 : ℂ)⁻¹ • ((v ⊗ₜ[ℂ] (qubitBasis 0).vec) ⊗ₜ[ℂ] (qubitBasis 0).vec
          + (v ⊗ₜ[ℂ] (qubitBasis 1).vec) ⊗ₜ[ℂ] (qubitBasis 1).vec) := by
  have h1 : v ⊗ₜ[ℂ] bellPhiPlus.vec
      = (Real.sqrt 2 : ℂ)⁻¹ • (v ⊗ₜ[ℂ] ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec)
          + v ⊗ₜ[ℂ] ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec)) := by
    change v ⊗ₜ[ℂ] ((Real.sqrt 2 : ℂ)⁻¹ • ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec
        + (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec) : qubit.space ⊗[ℂ] qubit.space) = _
    rw [TensorProduct.tmul_smul, TensorProduct.tmul_add]
  rw [h1, ← assoc_toIsometry_tmul_tmul v (qubitBasis 0).vec (qubitBasis 0).vec,
    ← assoc_toIsometry_tmul_tmul v (qubitBasis 1).vec (qubitBasis 1).vec]
  exact (map_smul _ _ _).trans (congrArg _ (map_add _ _ _))

set_option maxHeartbeats 4000000 in
-- Distributing both sides over the eight three-qubit computational basis vectors and closing the
-- linear identity by `module` exceeds the default heartbeat budget.
/-- **The single-qubit teleportation identity** (Nielsen & Chuang §1.3.7): for an arbitrary qubit
state `|ψ⟩`, re-associating `|ψ⟩ ⊗ |Φ⁺⟩` (with `|Φ⁺⟩` the shared Bell pair) and grouping the first
two qubits gives
`|ψ⟩ ⊗ |Φ⁺⟩ = ½ Σ_{x,y} |β_xy⟩ ⊗ (X^y Z^x |ψ⟩)`.
Measuring the first pair in the Bell basis therefore leaves the third qubit in `X^y Z^x |ψ⟩`, which
the single-qubit Pauli byproduct correction `pauliByproduct x y` undoes — this is the mechanism of
quantum teleportation, and the single-qubit special case of the gate-teleportation protocol of
Problem 4.6.  Proved directly: expand `|ψ⟩ = Σ_i ⟨i|ψ⟩ |i⟩`, distribute both sides to the eight
computational three-qubit basis vectors, and close the resulting linear identity by `module`. -/
theorem teleportation_identity (v : qubit.space) :
    (QSystem.assoc qubit qubit qubit).toIsometry (v ⊗ₜ bellPhiPlus.vec)
      = (2 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2,
          bellBasisVec p.1 p.2 ⊗ₜ (pauliByproduct p.1 p.2).op v := by
  have hv : v = v.ofLp 0 • (qubitBasis 0).vec + v.ofLp 1 • (qubitBasis 1).vec := by
    have h := (EuclideanSpace.sum_single_ofLp_eq v).symm
    rw [Fin.sum_univ_two] at h
    simp only [] at h
    exact h
  rw [assoc_toIsometry_tmul_bellPhiPlus, Fintype.sum_prod_type]
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  simp only [Fin.sum_univ_two, TensorProduct.add_tmul, ← TensorProduct.smul_tmul',
    pauliByproduct_op_apply_qubitBasis, bellBasisVec_tmul, map_add, map_smul,
    TensorProduct.tmul_add, TensorProduct.tmul_smul, Fin.isValue, Fin.val_zero, Fin.val_one,
    Nat.mul_zero, Nat.mul_one, pow_zero, pow_one, one_smul, Fin.reduceAdd]
  generalize v.ofLp 0 = c₀
  generalize v.ofLp 1 = c₁
  generalize (qubitBasis 0).vec = a
  generalize (qubitBasis 1).vec = b
  -- A linear identity in the eight computational three-qubit basis vectors, weighted by the
  -- amplitudes `c₀, c₁` of `|ψ⟩`; the `change` re-elaborates the tensors with canonical instances
  -- so the atoms coincide across both sides, and `module` closes it.
  change (Real.sqrt 2 : ℂ)⁻¹ • (c₀ • a ⊗ₜ[ℂ] a ⊗ₜ[ℂ] a + c₁ • b ⊗ₜ[ℂ] a ⊗ₜ[ℂ] a +
        (c₀ • a ⊗ₜ[ℂ] b ⊗ₜ[ℂ] b + c₁ • b ⊗ₜ[ℂ] b ⊗ₜ[ℂ] b)) =
      (2 : ℂ)⁻¹ •
        (c₀ • (Real.sqrt 2 : ℂ)⁻¹ • (a ⊗ₜ[ℂ] a ⊗ₜ[ℂ] a + b ⊗ₜ[ℂ] b ⊗ₜ[ℂ] a) +
            c₁ • (1 : ℂ) • (Real.sqrt 2 : ℂ)⁻¹ • (a ⊗ₜ[ℂ] a ⊗ₜ[ℂ] b + b ⊗ₜ[ℂ] b ⊗ₜ[ℂ] b) +
            (c₀ • (Real.sqrt 2 : ℂ)⁻¹ • (a ⊗ₜ[ℂ] b ⊗ₜ[ℂ] b + b ⊗ₜ[ℂ] a ⊗ₜ[ℂ] b) +
              c₁ • (1 : ℂ) • (Real.sqrt 2 : ℂ)⁻¹ • (a ⊗ₜ[ℂ] b ⊗ₜ[ℂ] a + b ⊗ₜ[ℂ] a ⊗ₜ[ℂ] a)) +
          (c₀ • (Real.sqrt 2 : ℂ)⁻¹ • (a ⊗ₜ[ℂ] a ⊗ₜ[ℂ] a + (-1 : ℂ) • b ⊗ₜ[ℂ] b ⊗ₜ[ℂ] a) +
              c₁ • (-1 : ℂ) • (Real.sqrt 2 : ℂ)⁻¹ •
                (a ⊗ₜ[ℂ] a ⊗ₜ[ℂ] b + (-1 : ℂ) • b ⊗ₜ[ℂ] b ⊗ₜ[ℂ] b) +
            (c₀ • (Real.sqrt 2 : ℂ)⁻¹ • (a ⊗ₜ[ℂ] b ⊗ₜ[ℂ] b + (-1 : ℂ) • b ⊗ₜ[ℂ] a ⊗ₜ[ℂ] b) +
              c₁ • (-1 : ℂ) • (Real.sqrt 2 : ℂ)⁻¹ •
                (a ⊗ₜ[ℂ] b ⊗ₜ[ℂ] a + (-1 : ℂ) • b ⊗ₜ[ℂ] a ⊗ₜ[ℂ] a))))
  simp only [smul_smul]
  module

/-- **Per-basis single-qubit teleportation identity:** the `teleportation_identity` for a
computational-basis input `|i⟩`, `assoc (|i⟩ ⊗ |Φ⁺⟩) = ½ Σ_{x,y} |β_xy⟩ ⊗ (X^y Z^x |i⟩)` — the
concrete form in which N&C §1.3.7 first presents teleportation.  A direct specialisation of
`teleportation_identity` at `v := |i⟩`. -/
theorem teleportation_identity_qubitBasis (i : Fin 2) :
    (QSystem.assoc qubit qubit qubit).toIsometry ((qubitBasis i).vec ⊗ₜ bellPhiPlus.vec)
      = (2 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2,
          bellBasisVec p.1 p.2 ⊗ₜ (pauliByproduct p.1 p.2).op (qubitBasis i).vec :=
  teleportation_identity (qubitBasis i).vec

end AxQM
