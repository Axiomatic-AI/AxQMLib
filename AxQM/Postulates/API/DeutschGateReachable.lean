/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlBranchExt
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.DeutschGate
import AxQM.Postulates.API.HadamardRotation

/-!
# AxQM.Postulates.API — reachability of the Deutsch gate (density of `C²(R_x(β))`)

The universality half of Nielsen & Chuang, Exercise 4.44. The three-qubit Deutsch gate is
`G = C²(iR_x(πα))` (`deutschGate`, `AxQM/NC/Ch4/Exercise4_44.lean`, defined as
`ccontrolledUnitary (iRxGate (πα))`); its analytic engine — that iterating the single-qubit target
`iR_x(πα)` densely fills every `x`-rotation when `α` is irrational — is the concrete matrix fact
`Concrete.rotX_mem_closure_cyclic_iRx` (Exercise 4.44). This file **lifts that density from matrices
to the gate**: iterating the Deutsch gate itself densely reaches every doubly-controlled
`x`-rotation `C²(R_x(β))`. This is the first genuinely *reachability* statement about `G` and the
foundation of the universality argument; the second rotation axis and single-qubit universality
follow in `AxQM/Postulates/API/DeutschGatePhaseGate.lean`.

The gate is written here in its unfolded form `ccontrolledUnitary (iRxGate (Real.pi * α))`
(definitionally `deutschGate α`); the lemma `ccontrolledUnitary_iRxGate_pow_op_mem` names the gate
in that form.

## What is formalised

* `controlledOp A` / `ccontrolledOp A` — the operator-level (unitarity-free) single- and
  doubly-controlled embeddings, `controlledOp A = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ A` as a raw function of a
  target *operator* `A`. They agree with the gate operators (`controlledUnitary_op_eq`,
  `ccontrolledUnitary_op_eq`) and are **continuous** in `A` (`continuous_controlledOp`,
  `continuous_ccontrolledOp`), since `A ↦ |1⟩⟨1| ⊗ A` is `ℂ`-linear between finite-dimensional
  operator spaces. Continuity carries a density statement about the target up to the gate.
* `controlledUnitary_one`, `ccontrolledUnitary_pow` — the algebraic backbone: the controlled
  construction is a monoid homomorphism (`C(1) = 1`, `C²` respects powers via
  `controlledUnitary_comp`), so iterating `G` is `C²` of the iterated target.
* `deutschReachableOps α` — the **reachable operator set**: the operators of the integer iterates of
  the Deutsch gate on its target, in the closed form `{C²(iⁿ · R_x(nπα)) : n ∈ ℤ}` (the
  doubly-controlled cyclic subgroup `⟨iR_x(πα)⟩`); `ccontrolledUnitary_iRxGate_pow_op_mem` records
  that its non-negative members are exactly the forward gate powers `(G^k).op`.
* `ccontrolledUnitary_rotXGate_op_mem_closure_deutschReachableOps` — **the density lift** (α
  irrational): every doubly-controlled `x`-rotation `C²(R_x(β))` lies in the closure of
  `deutschReachableOps α`, the physics incarnation of `Concrete.rotX_mem_closure_cyclic_iRx`.

## Design notes

* **Why the operator-level `controlledOp`.** The reachable orbit `{iⁿ · R_x(nπα)}` is a set of raw
  matrices, and the density transfer is a continuity argument, which needs a continuous *function*
  of a raw operator. `controlledOp`/`ccontrolledOp` provide exactly that and coincide with
  `(controlledUnitary _).op` / `(ccontrolledUnitary _).op` by `rfl`, so no content is lost.
* **Hypothesis.** It is exactly `Irrational α`. The reachable set is the cyclic subgroup
  `⟨iR_x(πα)⟩` doubly-controlled onto the target (its integer iterates), matching the concrete
  core's `ℤ`-closed form; `ccontrolledUnitary_iRxGate_pow_op_mem` connects it to the actual gate.
  Density is stated for the operators of the gate and proved outright.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### Operator-level controlled embeddings and their continuity -/

/-- **The single-controlled embedding at the operator level**, `controlledOp A = |0⟩⟨0| ⊗ I +
|1⟩⟨1| ⊗ A`, as a raw function of a target *operator* `A` (no unitarity required). It is the
operator field of `controlledUnitary` (`controlledUnitary_op_eq`), extended to non-unitary `A` so
it can enter continuity arguments. -/
def controlledOp (A : S.space →L[ℂ] S.space) :
    (qubit ⊗ S).space →L[ℂ] (qubit ⊗ S).space :=
  TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
      (1 : S.space →L[ℂ] S.space)
    + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec) A

/-- `controlledOp` is the operator of `controlledUnitary`: `(controlledUnitary U).op =
controlledOp U.op`. -/
theorem controlledUnitary_op_eq (U : Evolution S) :
    (controlledUnitary U).op = controlledOp U.op := rfl

/-- **The single-controlled embedding is continuous in its target operator.** The constant branch
`|0⟩⟨0| ⊗ I` is fixed and the active branch `A ↦ |1⟩⟨1| ⊗ A = TensorProduct.mapL |1⟩⟨1| A` is
continuous by `Continuous.mapL` (the tensor map is continuous in each slot), constant in the first
slot and the identity in the second. -/
theorem continuous_controlledOp :
    Continuous fun A : S.space →L[ℂ] S.space => controlledOp A := by
  simp only [controlledOp]
  exact continuous_const.add (Continuous.mapL continuous_const continuous_id)

/-- **The doubly-controlled embedding at the operator level**, `ccontrolledOp A =
controlledOp (controlledOp A)`, the `C²`-block-embedding of a target operator `A`. It is the
operator of `ccontrolledUnitary` (`ccontrolledUnitary_op_eq`). -/
def ccontrolledOp (A : qubit.space →L[ℂ] qubit.space) :
    (qubit ⊗ (qubit ⊗ qubit)).space →L[ℂ] (qubit ⊗ (qubit ⊗ qubit)).space :=
  controlledOp (S := qubit ⊗ qubit) (controlledOp (S := qubit) A)

/-- `ccontrolledOp` is the operator of `ccontrolledUnitary`. -/
theorem ccontrolledUnitary_op_eq (U : Evolution qubit) :
    (ccontrolledUnitary U).op = ccontrolledOp U.op := rfl

/-- **The doubly-controlled embedding is continuous in its target operator.** -/
theorem continuous_ccontrolledOp :
    Continuous fun A : qubit.space →L[ℂ] qubit.space => ccontrolledOp A :=
  continuous_controlledOp.comp continuous_controlledOp

/-! ### The controlled construction is a monoid homomorphism -/

/-- **The controlled gate of the identity is the identity:** `C(1) = 1`. Reuses the structural lemma
`controlledUnitary_id` (`C(Evolution.id) = Evolution.id`, `Postulates/API/ControlBranchExt`),
bridged to the monoid unit by `Evolution.one_def` (`(1 : Evolution S) = Evolution.id`). -/
theorem controlledUnitary_one : controlledUnitary (1 : Evolution S) = 1 := by
  simp only [Evolution.one_def, controlledUnitary_id]

/-- **The single-controlled construction is multiplicative:** `C(U · V) = C(U) · C(V)`. Immediate
from `controlledUnitary_comp`. The single-controlled analogue of `ccontrolledUnitary_mul`. -/
theorem controlledUnitary_mul (U V : Evolution S) :
    controlledUnitary (U * V) = controlledUnitary U * controlledUnitary V := by
  simp only [Evolution.mul_def, ← controlledUnitary_comp]

/-- **The single-controlled construction respects powers:** `C(Uᵏ) = C(U)ᵏ`. So iterating the
once-controlled Deutsch gate `k` times is the controlled `k`-th power of its target. -/
theorem controlledUnitary_pow (U : Evolution S) (k : ℕ) :
    controlledUnitary (U ^ k) = controlledUnitary U ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, controlledUnitary_one]
  | succ n ih => rw [pow_succ, pow_succ, controlledUnitary_mul, ih]

/-- **The doubly-controlled gate of the identity is the identity:** `C²(1) = 1`. -/
theorem ccontrolledUnitary_one : ccontrolledUnitary (1 : Evolution qubit) = 1 := by
  rw [ccontrolledUnitary, controlledUnitary_one, controlledUnitary_one]

/-- **The doubly-controlled construction is multiplicative:** `C²(U · V) = C²(U) · C²(V)`. Immediate
from `controlledUnitary_comp` applied twice. -/
theorem ccontrolledUnitary_mul (U V : Evolution qubit) :
    ccontrolledUnitary (U * V) = ccontrolledUnitary U * ccontrolledUnitary V := by
  simp only [ccontrolledUnitary, Evolution.mul_def, ← controlledUnitary_comp]

/-- **The doubly-controlled construction respects powers:** `C²(Uᵏ) = C²(U)ᵏ`. So iterating the
Deutsch gate `C²(iR_x(πα))` `k` times is the doubly-controlled `k`-th power of its target. -/
theorem ccontrolledUnitary_pow (U : Evolution qubit) (k : ℕ) :
    ccontrolledUnitary (U ^ k) = ccontrolledUnitary U ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, ccontrolledUnitary_one]
  | succ n ih => rw [pow_succ, pow_succ, ccontrolledUnitary_mul, ih]

/-! ### The reachable operator set of the Deutsch gate, and its density -/

/-- **The reachable operator set of the Deutsch gate.** The operators of the integer iterates of the
Deutsch gate `G = C²(iR_x(πα))` on its target, written in the closed form of the cyclic subgroup
`⟨iR_x(πα)⟩ = {iⁿ · R_x(nπα) : n ∈ ℤ}` doubly-controlled onto the three-qubit system. The
non-negative iterates are the forward gate powers `(G^k).op`
(`ccontrolledUnitary_iRxGate_pow_op_mem`). -/
def deutschReachableOps (α : ℝ) :
    Set ((qubit ⊗ (qubit ⊗ qubit)).space →L[ℂ] (qubit ⊗ (qubit ⊗ qubit)).space) :=
  Set.range fun n : ℤ => ccontrolledOp
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
      (Complex.I ^ n • Concrete.rotX (n • (Real.pi * α))))

/-- **The `k`-th power of the Deutsch gate is the doubly-controlled `iᵏ · R_x(kπα)`.** Combining
`ccontrolledUnitary_pow` (iterating `G` is `C²` of the iterated target), `Evolution.op_pow`, and the
concrete `Concrete.iRxMat_pow` (`(iR_x(θ))ᵏ = iᵏ · R_x(kθ)`) through `Matrix.toEuclideanCLM`. -/
theorem ccontrolledUnitary_iRxGate_pow_op (α : ℝ) (k : ℕ) :
    ((ccontrolledUnitary (iRxGate (Real.pi * α))) ^ k).op
      = ccontrolledOp (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
          (Complex.I ^ k • Concrete.rotX (↑k * (Real.pi * α)))) := by
  rw [← ccontrolledUnitary_pow, ccontrolledUnitary_op_eq, Evolution.op_pow, iRxGate_op]
  congr 1
  rw [← Concrete.iRxMat_pow]
  exact (map_pow (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))
    (Concrete.iRxMat (Real.pi * α)) k).symm

/-- **The forward Deutsch-gate iterates are reachable:** `(G^k).op ∈ deutschReachableOps α`. Grounds
the reachable operator set in the actual gate `G = C²(iR_x(πα))`: its members are the operators
obtained by iterating `G`. -/
theorem ccontrolledUnitary_iRxGate_pow_op_mem (α : ℝ) (k : ℕ) :
    ((ccontrolledUnitary (iRxGate (Real.pi * α))) ^ k).op ∈ deutschReachableOps α := by
  refine ⟨(k : ℤ), ?_⟩
  rw [ccontrolledUnitary_iRxGate_pow_op]
  simp only [zpow_natCast, zsmul_eq_mul, Int.cast_natCast]

/-- **The density lift (Nielsen & Chuang, Exercise 4.44).** When `α` is irrational, every
doubly-controlled `x`-rotation `C²(R_x(β))` lies in the closure of the reachable operator set of the
Deutsch gate: iterating `G = C²(iR_x(πα))` approximates `C²(R_x(β))` to arbitrary accuracy, for
every angle `β`.

This is the physics incarnation of the concrete density core
`Concrete.rotX_mem_closure_cyclic_iRx` (`R_x(β) ∈ closure ⟨iR_x(πα)⟩`): the doubly-controlled
embedding `ccontrolledOp ∘ Matrix.toEuclideanCLM` is continuous, so it carries the matrix closure
into the operator closure (`image_closure_subset_closure_image`), sending the concrete orbit onto
`deutschReachableOps α` and the target `R_x(β)` onto `(ccontrolledUnitary (rotXGate β)).op`. -/
theorem ccontrolledUnitary_rotXGate_op_mem_closure_deutschReachableOps
    {α : ℝ} (hα : Irrational α) (β : ℝ) :
    (ccontrolledUnitary (rotXGate β)).op ∈ closure (deutschReachableOps α) := by
  have hcont : Continuous fun M : Matrix (Fin 2) (Fin 2) ℂ =>
      ccontrolledOp (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) M) :=
    continuous_ccontrolledOp.comp Matrix.continuous_toEuclideanCLM
  have hx := image_closure_subset_closure_image hcont
    (Set.mem_image_of_mem _ (Concrete.rotX_mem_closure_cyclic_iRx hα β))
  rw [← Set.range_comp] at hx
  rw [ccontrolledUnitary_op_eq, rotXGate_op]
  exact hx

end AxQM
