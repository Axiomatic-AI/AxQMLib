/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Teleportation
import AxQM.Postulates.API.Fredkin
import AxQM.Postulates.API.CnotXBasis
import AxQM.Postulates.API.CnotPauliPropagation
import AxQM.Postulates.API.MeasureObservable
import AxQM.Postulates.API.KitaevPhaseEstimation
import AxQM.Postulates.API.MeasurementOperation

/-!
# AxQM — the measured-swap circuit branch decompositions (N&C Exercise 10.65)

The core of Nielsen & Chuang **Exercise 10.65**: replacing a controlled-`NOT` in a
qubit swap by a *measurement* and a *classically-controlled single-qubit correction*.  N&C's two
alternative circuits, applied to an unknown input `|ψ⟩ ⊗ |0⟩`, produce — *before* the
measurement — a state of the two-branch form

  `(√2)⁻¹ (|0⟩ ⊗ |ψ⟩ + |1⟩ ⊗ C|ψ⟩)`,

with the target (right) qubit holding a single-qubit correction `C` of `|ψ⟩` on the `|1⟩`
branch (`C = Z` for the first circuit, `C = X` for the second).  Measuring the control (left)
qubit and obtaining outcome `m` leaves the target in `C^m|ψ⟩`, which a classically-controlled
`C^m` undoes — moving `|ψ⟩` onto the second qubit exactly as N&C's two-`CNOT` swap does.

This file records the two branch decompositions as vector identities (the algebraic heart, in the
same spirit as `teleportation_identity`).  The measurement/collapse assembly is in
`AxQM/NC/Ch10/Exercise10_65.lean`.

## What is formalised

* `hadamardLeft_cnot_ketZero_branch` — **circuit 1's branch decomposition**: applying `CNOT`
  (control = qubit 1) and then a Hadamard to qubit 1, to `|ψ⟩ ⊗ |0⟩`, gives
  `(√2)⁻¹ (|0⟩⊗|ψ⟩ + |1⟩⊗Z|ψ⟩)`.  The `|1⟩`-branch correction is `Z`.
* `reversedCnot_hadamardRight_ketZero_branch` — **circuit 2's branch decomposition**: applying a
  Hadamard to qubit 2 and then the reversed `CNOT` (control = qubit 2), to `|ψ⟩ ⊗ |0⟩`, gives
  `(√2)⁻¹ (|0⟩⊗|ψ⟩ + |1⟩⊗X|ψ⟩)`.  The `|1⟩`-branch correction is `X`.
* `qubit_vec_eq_ofLp_smul` — the reusable computational-basis expansion of an arbitrary qubit
  vector `v = v.ofLp 0 • |0⟩ + v.ofLp 1 • |1⟩` (shared by both proofs).
* `reversedCnotGate_op_qubitBasisVec_tmul` — the (`.op`/`.vec`) reversed-`CNOT`
  truth table `reversedCNOT (|a⟩⊗|b⟩) = |a⊕b⟩⊗|b⟩`, the analogue of
  `cnotGate_op_qubitBasisVec_tmul`.

## Design notes

* **Arbitrary input.**  Both identities hold for an *arbitrary* qubit vector `v` (the unknown
  `|ψ⟩`), not just a computational-basis input — the fidelity point of the exercise (the state
  being moved is unknown).  Each is proved by expanding `v = v₀|0⟩ + v₁|1⟩`, pushing the
  gate operators through the superposition, and closing the resulting linear identity in the
  four two-qubit basis tensors with `module`.
* **Instance-diamond friction.**  The gate operators have domain `(qubit ⊗ qubit).space` while the
  distributed input lives at the raw `qubit.space ⊗[ℂ] qubit.space` head; these are defeq but
  present different `Add`/`SMul` instances, so `simp`/`rw` will not fire `map_add`/`map_smul` on the
  operators.  The proofs use `erw` for exactly those operator-distribution steps (as elsewhere in
  the library), then the aligned per-basis actions (`cnotGate_op_qubitBasisVec_tmul` /
  `reversedCnotGate_op_qubitBasisVec_tmul`, `Evolution.onLeft_op_tmul`, and the Hadamard vector
  actions `hadamardGate_op_qubitBasisVec_zero`/`_one`) fire by `rw`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **Computational-basis decomposition of an unknown qubit vector:**
`v = ⟨0|v⟩ |0⟩ + ⟨1|v⟩ |1⟩`, the amplitudes read off as the `EuclideanSpace` coordinates
`v.ofLp 0`, `v.ofLp 1`.  The unconditional (no-normalization) expansion used to reduce a
statement about an arbitrary `|ψ⟩` to the two computational-basis cases. -/
theorem qubit_vec_eq_ofLp_smul (v : qubit.space) :
    v = v.ofLp 0 • (qubitBasis 0).vec + v.ofLp 1 • (qubitBasis 1).vec := by
  have h := (EuclideanSpace.sum_single_ofLp_eq (v : EuclideanSpace ℂ (Fin 2))).symm
  rw [Fin.sum_univ_two] at h
  simp only [qubitBasis_vec]
  exact (h : v = v.ofLp 0 • EuclideanSpace.single 0 1 + v.ofLp 1 • EuclideanSpace.single 1 1)

/-- **The reversed-`CNOT` truth table at the operator/vector level:**
`reversedCNOT (|a⟩ ⊗ |b⟩) = |a ⊕ b⟩ ⊗ |b⟩` (`a + b` in `Fin 2`) — the
`Evolution.op`/`PureState.vec` form of `reversedCnotGate_evolvePure_qubitBasis`, the
analogue of `cnotGate_op_qubitBasisVec_tmul`. -/
theorem reversedCnotGate_op_qubitBasisVec_tmul (a b : Fin 2) :
    reversedCnotGate.op ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
      = (qubitBasis (a + b)).vec ⊗ₜ[ℂ] (qubitBasis b).vec := by
  rw [← PureState.tmul_vec, ← Evolution.evolvePure_vec, reversedCnotGate_evolvePure_qubitBasis,
    PureState.tmul_vec]

/-- **Circuit 1's branch decomposition** (N&C Exercise 10.65, first circuit): applying `CNOT` with
control qubit 1 and then a Hadamard on qubit 1, to the input `|ψ⟩ ⊗ |0⟩`, produces

  `(H ⊗ 1) · CNOT · (|ψ⟩ ⊗ |0⟩) = (√2)⁻¹ (|0⟩ ⊗ |ψ⟩ + |1⟩ ⊗ Z|ψ⟩)`.

Measuring qubit 1 in the computational basis therefore leaves qubit 2 in `Z^m |ψ⟩`, which a
classically-controlled `Z` correction undoes — the first measured-swap circuit. -/
theorem hadamardLeft_cnot_ketZero_branch (v : qubit.space) :
    (hadamardGate.onLeft qubit).op (cnotGate.op (v ⊗ₜ[ℂ] (qubitBasis 0).vec))
      = Concrete.invSqrt2 •
        ((qubitBasis 0).vec ⊗ₜ[ℂ] v + (qubitBasis 1).vec ⊗ₜ[ℂ] pauliZGate.op v) := by
  have hv := qubit_vec_eq_ofLp_smul v
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  simp only [TensorProduct.add_tmul, ← TensorProduct.smul_tmul', map_add, map_smul,
    pauliZGate_op_apply_qubitBasis, Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul]
  erw [map_add, map_smul, map_smul]
  rw [cnotGate_op_qubitBasisVec_tmul, cnotGate_op_qubitBasisVec_tmul]
  simp only [Fin.isValue, add_zero, zero_add]
  erw [map_add, map_smul, map_smul]
  rw [Evolution.onLeft_op_tmul, Evolution.onLeft_op_tmul,
    hadamardGate_op_qubitBasisVec_zero, hadamardGate_op_qubitBasisVec_one]
  -- Distribute all tensors to bare basis atoms, then re-elaborate them at canonical instances
  -- (the operator outputs and the RHS present the same tensor at defeq-but-distinct heads, which
  -- `module`'s atom matching would otherwise separate) and close the linear identity.
  simp only [← TensorProduct.smul_tmul', TensorProduct.add_tmul, TensorProduct.sub_tmul,
    TensorProduct.tmul_add, TensorProduct.tmul_smul, smul_add, smul_sub, smul_smul]
  generalize (qubitBasis 0).vec = a
  generalize (qubitBasis 1).vec = b
  generalize v.ofLp 0 = c₀
  generalize v.ofLp 1 = c₁
  generalize (Concrete.invSqrt2 : ℂ) = s
  change c₀ • (s • a ⊗ₜ[ℂ] a + s • b ⊗ₜ[ℂ] a)
        + c₁ • (s • a ⊗ₜ[ℂ] b - s • b ⊗ₜ[ℂ] b)
      = (s * c₀) • a ⊗ₜ[ℂ] a + (s * c₁) • a ⊗ₜ[ℂ] b
        + ((s * c₀) • b ⊗ₜ[ℂ] a + (s * (c₁ * -1)) • b ⊗ₜ[ℂ] b)
  module

/-- **Circuit 2's branch decomposition** (N&C Exercise 10.65, second circuit): applying a Hadamard
to qubit 2 and then the reversed `CNOT` (control = qubit 2), to `|ψ⟩ ⊗ |0⟩`, produces

  `reversedCNOT · (1 ⊗ H) · (|ψ⟩⊗|0⟩) = (√2)⁻¹ (|0⟩⊗|ψ⟩ + |1⟩⊗X|ψ⟩)`.

Measuring qubit 1 in the computational basis therefore leaves qubit 2 in `X^m |ψ⟩`, which a
classically-controlled `X` correction undoes — the second measured-swap circuit. -/
theorem reversedCnot_hadamardRight_ketZero_branch (v : qubit.space) :
    reversedCnotGate.op ((hadamardGate.onRight qubit).op (v ⊗ₜ[ℂ] (qubitBasis 0).vec))
      = Concrete.invSqrt2 •
        ((qubitBasis 0).vec ⊗ₜ[ℂ] v + (qubitBasis 1).vec ⊗ₜ[ℂ] pauliXGate.op v) := by
  have hv := qubit_vec_eq_ofLp_smul v
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  simp only [TensorProduct.add_tmul, ← TensorProduct.smul_tmul', map_add, map_smul,
    pauliXGate_op_apply_qubitBasis, Fin.isValue, Fin.reduceAdd]
  erw [map_add, map_smul, map_smul]
  rw [Evolution.onRight_op_tmul, Evolution.onRight_op_tmul, hadamardGate_op_qubitBasisVec_zero]
  simp only [TensorProduct.tmul_smul, TensorProduct.tmul_add]
  erw [map_add, map_smul, map_smul, map_smul, map_smul, map_add, map_add]
  -- Reduce each reversed-CNOT on the computational basis, then distribute to bare atoms and close
  -- as in the first circuit (re-elaborating the tensors at canonical instances via `change`).
  simp only [reversedCnotGate_op_qubitBasisVec_tmul, Fin.reduceAdd, smul_add, smul_smul]
  generalize (qubitBasis 0).vec = a
  generalize (qubitBasis 1).vec = b
  generalize v.ofLp 0 = c₀
  generalize v.ofLp 1 = c₁
  generalize (Concrete.invSqrt2 : ℂ) = s
  change (c₀ * s) • a ⊗ₜ[ℂ] a + (c₀ * s) • b ⊗ₜ[ℂ] b
        + ((c₁ * s) • b ⊗ₜ[ℂ] a + (c₁ * s) • a ⊗ₜ[ℂ] b)
      = (s * c₀) • a ⊗ₜ[ℂ] a + (s * c₁) • a ⊗ₜ[ℂ] b
        + ((s * c₀) • b ⊗ₜ[ℂ] b + (s * c₁) • b ⊗ₜ[ℂ] a)
  module

/-- **The two-`CNOT` swap into `|0⟩` at the vector level:** `reversedCNOT · CNOT · (v ⊗ |0⟩) =
|0⟩ ⊗ v` for an arbitrary qubit vector `v`.  `CNOT` copies `v = v₀|0⟩ + v₁|1⟩` into
`v₀|00⟩ + v₁|11⟩`; the reversed `CNOT` uncopies the control, leaving `v₀|00⟩ + v₁|01⟩ = |0⟩ ⊗ v`.
The core of the reference two-`CNOT` swap `swapViaCnots` of N&C Exercise 10.65,
proved by expanding `v` over the computational basis and applying the two `CNOT` truth tables. -/
theorem reversedCnotGate_op_cnotGate_op_qubitBasisVec_zero (v : qubit.space) :
    reversedCnotGate.op (cnotGate.op (v ⊗ₜ[ℂ] (qubitBasis 0).vec))
      = (qubitBasis 0).vec ⊗ₜ[ℂ] v := by
  conv_lhs => rw [qubit_vec_eq_ofLp_smul v]
  conv_rhs => rw [qubit_vec_eq_ofLp_smul v]
  simp only [TensorProduct.add_tmul, ← TensorProduct.smul_tmul']
  erw [map_add, map_smul, map_smul]
  rw [cnotGate_op_qubitBasisVec_tmul, cnotGate_op_qubitBasisVec_tmul]
  simp only [Fin.isValue, Fin.reduceAdd]
  erw [map_add, map_smul, map_smul]
  rw [reversedCnotGate_op_qubitBasisVec_tmul, reversedCnotGate_op_qubitBasisVec_tmul]
  simp only [Fin.isValue, Fin.reduceAdd, TensorProduct.tmul_add, TensorProduct.tmul_smul]
  generalize (qubitBasis 0).vec = a
  generalize (qubitBasis 1).vec = b
  generalize v.ofLp 0 = c₀
  generalize v.ofLp 1 = c₁
  change c₀ • a ⊗ₜ[ℂ] a + c₁ • a ⊗ₜ[ℂ] b = c₀ • a ⊗ₜ[ℂ] a + c₁ • a ⊗ₜ[ℂ] b
  module

/-! ### The two measured-swap circuits as evolutions -/

/-- **`Z` is an involution as a gate:** `Z · Z = 1`.  From the concrete matrix involution
`Concrete.pauliZ_mul_self` (`pauliZ · pauliZ = 1`) carried through the `⋆`-algebra map
`Matrix.toEuclideanCLM` — the `Z`-analogue of `pauliXGate_comp_pauliXGate`.  Used to undo the `|1⟩`
branch correction of the first measured-swap circuit (`Z² = 1`). -/
theorem pauliZGate_comp_pauliZGate : pauliZGate.comp pauliZGate = Evolution.id := by
  apply Evolution.ext
  rw [Evolution.comp_op, Evolution.id_op]
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliZ).comp
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliZ) = 1
  rw [← ContinuousLinearMap.mul_def, ← map_mul, Concrete.pauliZ_mul_self, map_one]

/-- **The first measured-swap circuit** of N&C Exercise 10.65: a `CNOT` (control = qubit 1) followed
by a Hadamard on qubit 1, `(H ⊗ 1) · CNOT`.  Feeding `|ψ⟩ ⊗ |0⟩` and measuring qubit 1 leaves qubit
2 in `Z^m|ψ⟩` (`m` the outcome), undone by a classically-controlled `Z`. -/
def measuredSwapCircuit1 : Evolution (qubit ⊗ qubit) :=
  (hadamardGate.onLeft qubit).comp cnotGate

/-- **The second measured-swap circuit** of N&C Exercise 10.65: a Hadamard on qubit 2 followed by
the reversed `CNOT` (control = qubit 2), `reversedCNOT · (1 ⊗ H)`.  Feeding `|ψ⟩ ⊗ |0⟩` and
measuring qubit 1 leaves qubit 2 in `X^m|ψ⟩`, undone by a classically-controlled `X`. -/
def measuredSwapCircuit2 : Evolution (qubit ⊗ qubit) :=
  reversedCnotGate.comp (hadamardGate.onRight qubit)

/-- **First circuit, pre-measurement state (vector form).**  Applying `measuredSwapCircuit1` to
`|ψ⟩ ⊗ |0⟩` yields the two-branch state `(√2)⁻¹(|0⟩ ⊗ |ψ⟩ + |1⟩ ⊗ Z|ψ⟩)`.  The `evolvePure`/`.vec`
packaging of `hadamardLeft_cnot_ketZero_branch`, feeding the control-measurement engine below. -/
theorem measuredSwapCircuit1_evolvePure_ketZero_vec (ψ : PureState qubit) :
    (measuredSwapCircuit1.evolvePure (ψ.tmul (qubitBasis 0))).vec
      = Concrete.invSqrt2 • ((qubitBasis 0).vec ⊗ₜ[ℂ] ψ.vec
          + (qubitBasis 1).vec ⊗ₜ[ℂ] pauliZGate.op ψ.vec) := by
  rw [Evolution.evolvePure_vec]
  simp only [measuredSwapCircuit1, Evolution.comp_op, PureState.tmul_vec]
  have hcomp : ((hadamardGate.onLeft qubit).op ∘SL cnotGate.op) (ψ.vec ⊗ₜ[ℂ] (qubitBasis 0).vec)
      = (hadamardGate.onLeft qubit).op (cnotGate.op (ψ.vec ⊗ₜ[ℂ] (qubitBasis 0).vec)) :=
    ContinuousLinearMap.comp_apply _ _ _
  exact hcomp.trans (hadamardLeft_cnot_ketZero_branch ψ.vec)

/-- **Second circuit, pre-measurement state (vector form).**  Applying `measuredSwapCircuit2` to
`|ψ⟩ ⊗ |0⟩` yields the two-branch state `(√2)⁻¹(|0⟩ ⊗ |ψ⟩ + |1⟩ ⊗ X|ψ⟩)`.  The `evolvePure`/`.vec`
packaging of `reversedCnot_hadamardRight_ketZero_branch`. -/
theorem measuredSwapCircuit2_evolvePure_ketZero_vec (ψ : PureState qubit) :
    (measuredSwapCircuit2.evolvePure (ψ.tmul (qubitBasis 0))).vec
      = Concrete.invSqrt2 • ((qubitBasis 0).vec ⊗ₜ[ℂ] ψ.vec
          + (qubitBasis 1).vec ⊗ₜ[ℂ] pauliXGate.op ψ.vec) := by
  rw [Evolution.evolvePure_vec]
  simp only [measuredSwapCircuit2, Evolution.comp_op, PureState.tmul_vec]
  have hcomp : (reversedCnotGate.op ∘SL (hadamardGate.onRight qubit).op)
      (ψ.vec ⊗ₜ[ℂ] (qubitBasis 0).vec)
      = reversedCnotGate.op ((hadamardGate.onRight qubit).op (ψ.vec ⊗ₜ[ℂ] (qubitBasis 0).vec)) :=
    ContinuousLinearMap.comp_apply _ _ _
  exact hcomp.trans (reversedCnot_hadamardRight_ketZero_branch ψ.vec)

/-! ### The control-measurement two-branch collapse engine

For a two-branch state `(√2)⁻¹(|0⟩ ⊗ |φ₀⟩ + |1⟩ ⊗ |φ₁⟩)` on `qubit ⊗ S` with unit-vector branches
`|φ₀⟩`, `|φ₁⟩`, measuring the control qubit in the computational basis (`controlMeasurement S`)
gives each outcome `m ∈ {0,1}` with probability `½` and collapses the target onto `|φ_m⟩`.  This is
the measurement half of Exercise 10.65: applied to the pre-measurement states above (`φ₀ = |ψ⟩` and
`φ₁ = C|ψ⟩` the correction), it says the control reads `m` and the target holds `C^m|ψ⟩`.

The branch amplitudes and the control projector `Mₘ = |m⟩⟨m| ⊗ 1` live at the raw tensor head
`qubit.space ⊗[ℂ] S.space`, while the norms / rank-one projectors live at the composite
`(qubit ⊗ S).space` head; these are defeq but present different `Add`/`SMul` instances (the diamond
noted on the branch identities above), so the operator action is stated at the raw head and each
consumer bridges to the composite head once with a `change` (as in Kitaev's Born-rule lemma). -/

/-- **Control measurement on a two-branch state (operator action).**  The control projector
`Mₘ = |m⟩⟨m| ⊗ 1` extracts the `m`-branch of `(√2)⁻¹(|0⟩ ⊗ |φ₀⟩ + |1⟩ ⊗ |φ₁⟩)`, giving
`(√2)⁻¹ |m⟩ ⊗ |φ_m⟩`: the orthogonality `⟨m|j⟩ = δₘⱼ` kills the other branch.  Stated at the raw
tensor head `qubit.space ⊗[ℂ] S.space` (via the `mapL` form `controlMeasurement_op`), so every
step distributes and cancels with the raw `Add`/`SMul` instances. -/
theorem controlMeasurement_op_invSqrt2_branch {S : QSystem}
    (φ : Fin 2 → PureState S) (m : Fin 2) :
    (controlMeasurement S).op m
        (Concrete.invSqrt2 • ((qubitBasis 0).vec ⊗ₜ[ℂ] (φ 0).vec
          + (qubitBasis 1).vec ⊗ₜ[ℂ] (φ 1).vec))
      = (Concrete.invSqrt2 • ((qubitBasis m).vec ⊗ₜ[ℂ] (φ m).vec) :
          qubit.space ⊗[ℂ] S.space) := by
  rw [controlMeasurement_op]
  change (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis m).vec (qubitBasis m).vec)
        (1 : S.space →L[ℂ] S.space))
      (Concrete.invSqrt2 • ((qubitBasis 0).vec ⊗ₜ[ℂ] (φ 0).vec
        + (qubitBasis 1).vec ⊗ₜ[ℂ] (φ 1).vec)) = _
  rw [map_smul, map_add, TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
    one_apply_eq_self, one_apply_eq_self]
  fin_cases m <;>
    simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue, InnerProductSpace.rankOne_apply,
      qubitBasis_inner_qubitBasis, ↓reduceIte, Fin.reduceEq, one_smul, zero_smul,
      TensorProduct.zero_tmul, add_zero, zero_add]

/-- **Born probability of the control measurement on a two-branch state: `½`.**  For a pure state
`Φ` with `|Φ⟩ = (√2)⁻¹(|0⟩ ⊗ |φ₀⟩ + |1⟩ ⊗ |φ₁⟩)` (unit branches), each control outcome `m` occurs
with probability `‖Mₘ|Φ⟩‖² = ‖(√2)⁻¹‖² · ‖|m⟩ ⊗ |φ_m⟩‖² = ½`. -/
theorem controlMeasurement_bornProb_invSqrt2_branch {S : QSystem} (Φ : PureState (qubit ⊗ S))
    (φ : Fin 2 → PureState S)
    (h : Φ.vec = Concrete.invSqrt2 • ((qubitBasis 0).vec ⊗ₜ[ℂ] (φ 0).vec
          + (qubitBasis 1).vec ⊗ₜ[ℂ] (φ 1).vec))
    (m : Fin 2) : (controlMeasurement S).bornProb Φ.toState m = 1 / 2 := by
  rw [Measurement.bornProb_toState_eq_normSq, h, controlMeasurement_op_invSqrt2_branch]
  change ‖(Concrete.invSqrt2 • ((qubitBasis m).vec ⊗ₜ[ℂ] (φ m).vec) : qubit.space ⊗[ℂ] S.space)‖ ^ 2
      = 1 / 2
  rw [norm_smul, TensorProduct.norm_tmul, (qubitBasis m).normalized, (φ m).normalized, mul_one,
    mul_one, Concrete.norm_invSqrt2_sq]
  norm_num

/-- **Post-measurement state of the control measurement on a two-branch state: `|m⟩ ⊗ |φ_m⟩`.**  For
a pure `Φ` with `|Φ⟩ = (√2)⁻¹(|0⟩ ⊗ |φ₀⟩ + |1⟩ ⊗ |φ₁⟩)`, obtaining control outcome `m` collapses the
state to the product `|m⟩ ⊗ |φ_m⟩`: the projected branch `Mₘ|Φ⟩ = (√2)⁻¹ |m⟩ ⊗ |φ_m⟩` renormalizes
by its Born weight `½` (the `‖(√2)⁻¹‖²` and `½⁻¹` cancel), leaving the unit product state. -/
theorem controlMeasurement_postMeasurement_invSqrt2_branch {S : QSystem}
    (Φ : PureState (qubit ⊗ S)) (φ : Fin 2 → PureState S)
    (h : Φ.vec = Concrete.invSqrt2 • ((qubitBasis 0).vec ⊗ₜ[ℂ] (φ 0).vec
          + (qubitBasis 1).vec ⊗ₜ[ℂ] (φ 1).vec))
    (m : Fin 2) (hp : (controlMeasurement S).bornProb Φ.toState m ≠ 0) :
    (controlMeasurement S).postMeasurement Φ.toState m hp
      = ((qubitBasis m).tmul (φ m)).toState := by
  have hconj : (starRingEnd ℂ) Concrete.invSqrt2 = Concrete.invSqrt2 := by
    rw [show Concrete.invSqrt2 = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ from rfl, map_inv₀, Complex.conj_ofReal]
  have hpost : ContinuousLinearMap.postOp (controlMeasurement S).op Φ.toState.op m
      = InnerProductSpace.rankOne ℂ ((controlMeasurement S).op m Φ.vec)
          ((controlMeasurement S).op m Φ.vec) := by
    simp only [ContinuousLinearMap.postOp, PureState.toState_op, InnerProductSpace.rankOne_comp,
      ContinuousLinearMap.adjoint_adjoint, InnerProductSpace.comp_rankOne]
  apply State.ext
  rw [Measurement.postMeasurement_op_eq_bornProb_smul_opElement,
    controlMeasurement_bornProb_invSqrt2_branch Φ φ h m, Measurement.opElement_eq_postOp, hpost, h,
    controlMeasurement_op_invSqrt2_branch, PureState.toState_op, PureState.tmul_vec]
  erw [InnerProductSpace.rankOne_smul_smul_self]
  rw [hconj, Concrete.invSqrt2_mul_self, smul_smul,
    show ((1 / 2 : ℝ) : ℂ)⁻¹ * 2⁻¹ = 1 by push_cast; norm_num, one_smul]

end AxQM
