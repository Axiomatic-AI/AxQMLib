/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DeutschGateDensity
import AxQM.Concrete.AxisAngleGateValues
import AxQM.Concrete.Pauli
import AxQM.Concrete.SqrtSwapCNOT
import ToMathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Topology.Instances.Matrix

/-!
# Concrete: the once-controlled Deutsch gate reaches `S` and `CNOT` (matrix level, N&C Ex 4.44)

Every statement is about matrices: the `2 × 2` rotations/gates (`rotX`, `sMatrix`, `pauliX`),
Mathlib's Kronecker product `⊗ₖ`, and `twoQubitCNOT`.

## Matrix-level reachability

The universality of the Deutsch gate `G = C²(iR_x(πα))` (Nielsen & Chuang, Exercise 4.44) is
assembled — following Exercise 4.43 — from a **matrix-level** development: any register unitary
decomposes into single-qubit gates and `CNOT`/`Toffoli`
(`Concrete/UnitaryToffoliSingleQubitProduct`, `Concrete/FourGateUniversality`), all stated over raw
matrices. To feed that assembly the gate set `G` reaches, the reachability facts must therefore also
live at the **matrix** level.

The analytic core `Concrete/DeutschGateDensity.lean` already supplies the single-qubit content as
raw `2 × 2` matrix closure facts about the cyclic orbit `⟨iR_x(πα)⟩ = {iⁿ · R_x(nπα) : n ∈ ℤ}`
(`deutschTargetOrbit`): every `R_x(β)`, the scalar `i · I` and the Pauli `X` all lie in its closure
when `α` is irrational. This file lifts the *scalar* and *Pauli-`X`* members through the concrete
**once-controlled** matrix construction `controlledMat`, exactly as
`Postulates/API/DeutschGatePhaseGate.lean` / `DeutschGateReversible.lean` do at the operator level
(with `controlledOp`), obtaining the matrix versions of the statements of those files.

## The construction and results

* `controlledMat g` — the once-controlled gate `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ g` on `Fin 2 × τ` (qubit `1`
  the control, the `τ`-system the target). It is a continuous monoid homomorphism in `g`
  (`controlledMat_one`, `controlledMat_mul`, `continuous_controlledMat`).
* `deutschControlledReachableMats α` — the once-controlled Deutsch iterates `{C(iⁿ R_x(nπα))}`, the
  image of the cyclic orbit under `controlledMat`; its forward members are the gate powers
  (`controlledMat_iRxMat_pow_mem`).
* `sMatrixKron_mem_closure_deutschControlledReachableMats` — **the phase gate `S`** (`α`
  irrational): `S ⊗ 1` lies in the closure of the once-controlled iterates. The mechanism is
  `controlledMat (i · I) = S ⊗ 1` — the controlled global phase `i · I` on the target becomes the
  phase gate `S` on the control — together with `i · I ∈ closure ⟨iR_x(πα)⟩`
  (`iScalar_mem_closure_cyclic_iRx`) and continuity of `controlledMat`.
* `twoQubitCNOT_mem_closure_deutschControlledReachableMats` — **the reversible gate `CNOT`** (`α`
  irrational): `CNOT` lies in the closure of the once-controlled iterates, via
  `controlledMat pauliX = CNOT` and `X ∈ closure ⟨iR_x(πα)⟩` (`pauliX_mem_closure_cyclic_iRx`).

These are the once-controlled gates the §4.5 assembly needs from `G`. The doubly-controlled
gates (`C²(R_x(β))`, `Toffoli`) are treated in `Concrete/DeutschDoublyControlledReachable.lean`.
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

/-! ### The once-controlled matrix construction -/

/-- **The once-controlled gate at the matrix level.** For a target operator `g : Matrix τ τ ℂ`,
`controlledMat g = |0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ g` on `Fin 2 × τ` — the qubit `1` is the control and the
`τ`-system the target: `g` fires exactly on the `|1⟩` control block. The `|0⟩⟨0|`, `|1⟩⟨1|` control
projectors are the diagonal matrices `diag(1, 0)`, `diag(0, 1)`. This is the raw-matrix analogue of
the operator-level `controlledOp` (`Postulates/API/DeutschGateReachable.lean`); it is used to carry
matrix closure facts about a target through the controlled embedding. -/
noncomputable def controlledMat (g : Matrix τ τ ℂ) : Matrix (Fin 2 × τ) (Fin 2 × τ) ℂ :=
  Matrix.diagonal (![1, 0] : Fin 2 → ℂ) ⊗ₖ (1 : Matrix τ τ ℂ)
    + Matrix.diagonal (![0, 1] : Fin 2 → ℂ) ⊗ₖ g

/-- The two control projectors sum to the identity: `diag(1,0) + diag(0,1) = 1`. -/
private theorem diag_add_diag_eq_one :
    Matrix.diagonal (![1, 0] : Fin 2 → ℂ) + Matrix.diagonal (![0, 1] : Fin 2 → ℂ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [Fintype τ] in
/-- **`controlledMat` sends the identity to the identity:** `controlledMat 1 = 1`. The two control
projectors sum to `1`, and `1 ⊗ 1 = 1`. -/
theorem controlledMat_one : controlledMat (1 : Matrix τ τ ℂ) = 1 := by
  rw [controlledMat, ← Matrix.add_kronecker, diag_add_diag_eq_one, Matrix.one_kronecker_one]

/-- **`controlledMat` is multiplicative:** `controlledMat a * controlledMat b = controlledMat (a*b)`
— the control projectors are orthogonal idempotents (`diag(1,0)·diag(0,1) = 0`), so the cross terms
vanish and only the two block-diagonal terms survive. -/
theorem controlledMat_mul (a b : Matrix τ τ ℂ) :
    controlledMat a * controlledMat b = controlledMat (a * b) := by
  have h00 : Matrix.diagonal (![1, 0] : Fin 2 → ℂ) * Matrix.diagonal (![1, 0] : Fin 2 → ℂ)
      = Matrix.diagonal (![1, 0] : Fin 2 → ℂ) := by
    rw [Matrix.diagonal_mul_diagonal]; congr 1; ext i; fin_cases i <;> simp
  have h11 : Matrix.diagonal (![0, 1] : Fin 2 → ℂ) * Matrix.diagonal (![0, 1] : Fin 2 → ℂ)
      = Matrix.diagonal (![0, 1] : Fin 2 → ℂ) := by
    rw [Matrix.diagonal_mul_diagonal]; congr 1; ext i; fin_cases i <;> simp
  have h01 : Matrix.diagonal (![1, 0] : Fin 2 → ℂ) * Matrix.diagonal (![0, 1] : Fin 2 → ℂ)
      = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have h10 : Matrix.diagonal (![0, 1] : Fin 2 → ℂ) * Matrix.diagonal (![1, 0] : Fin 2 → ℂ)
      = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  simp only [controlledMat, Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_kronecker_mul,
    h00, h01, h10, h11, Matrix.zero_kronecker, one_mul, add_zero, zero_add]

omit [Fintype τ] in
/-- **`controlledMat` is continuous** in its target block: each matrix entry is either the constant
`0` or a constant times a single entry of `g`. -/
theorem continuous_controlledMat :
    Continuous fun g : Matrix τ τ ℂ => controlledMat g := by
  refine continuous_const.add ?_
  apply continuous_matrix
  rintro ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.kronecker_apply]
  exact continuous_const.mul ((continuous_apply _).comp (continuous_apply _))

/-! ### The reachable once-controlled operator set of the Deutsch gate -/

/-- **The Deutsch target orbit** `⟨iR_x(πα)⟩ = {iⁿ · R_x(nπα) : n ∈ ℤ}` — the cyclic subgroup
generated by the Deutsch target `iR_x(πα)`, as a set of raw `2 × 2` matrices. Its closure holds
every `x`-rotation, the scalar `i · I`, and the Pauli `X` (`Concrete/DeutschGateDensity.lean`). -/
noncomputable def deutschTargetOrbit (α : ℝ) : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  Set.range fun n : ℤ => Complex.I ^ n • rotX (n • (Real.pi * α))

/-- **The `k`-th power of the Deutsch target lies in its cyclic orbit:**
`(iR_x(πα))^k ∈ deutschTargetOrbit α`. The forward (`n = k ≥ 0`) member of the closed-form `ℤ`-orbit
`{iⁿ R_x(nπα)}`: since `(iR_x(πα))^k = iᵏ R_x(kπα)` (`iRxMat_pow`), it is the `n = k` term. Shared
the once- and doubly-controlled reachable-set groundings (`controlledMat_iRxMat_pow_mem`,
`ccontrolledMat_iRxMat_pow_mem`), each of which is this membership pushed through a controlled
embedding via `Set.mem_image_of_mem`. -/
theorem iRxMat_pow_mem_deutschTargetOrbit (α : ℝ) (k : ℕ) :
    iRxMat (Real.pi * α) ^ k ∈ deutschTargetOrbit α := by
  refine ⟨(k : ℤ), ?_⟩
  rw [iRxMat_pow]
  simp only [zpow_natCast, zsmul_eq_mul, Int.cast_natCast]

/-- **The once-controlled reachable set of the Deutsch gate.** The once-controlled Deutsch iterates
`{C(iⁿ R_x(nπα))}`, i.e. the image of the target orbit `⟨iR_x(πα)⟩` under `controlledMat`. Its
forward members are the actual gate powers (`controlledMat_iRxMat_pow_mem`). -/
noncomputable def deutschControlledReachableMats (α : ℝ) :
    Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  controlledMat '' deutschTargetOrbit α

/-- **The `k`-th once-controlled gate power is reachable:** `controlledMat ((iR_x(πα))^k)` lies in
`deutschControlledReachableMats α`. Grounds the reachable set in the actual once-controlled gate:
its members are obtained by iterating the once-controlled Deutsch gate on its target. -/
theorem controlledMat_iRxMat_pow_mem (α : ℝ) (k : ℕ) :
    controlledMat (iRxMat (Real.pi * α) ^ k) ∈ deutschControlledReachableMats α :=
  Set.mem_image_of_mem _ (iRxMat_pow_mem_deutschTargetOrbit α k)

/-! ### The phase gate `S` from the once-controlled Deutsch gate -/

/-- **The controlled global phase `i · I` is the phase gate `S` on the control:**
`controlledMat (i · I) = S ⊗ 1`. Applying `i · I` to the target conditioned on the `|1⟩` control
scales that block by `i`, so the control acquires the diagonal `diag(1, i) = S` and the target is
untouched. -/
theorem controlledMat_iScalar_eq_sMatrix_kronecker :
    controlledMat (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = sMatrix ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [controlledMat, Matrix.kronecker_smul, ← Matrix.smul_kronecker, ← Matrix.add_kronecker]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sMatrix, Matrix.add_apply, Matrix.smul_apply]

/-- **The phase gate `S` is reachable from the once-controlled Deutsch gate** (Nielsen & Chuang,
Exercise 4.44, matrix level). When `α` is irrational, `S ⊗ 1` lies in the closure of the
once-controlled Deutsch iterates `deutschControlledReachableMats α`.

The controlled global phase `C(i · I) = S ⊗ 1` (`controlledMat_iScalar_eq_sMatrix_kronecker`) — the
accumulated phase `i` on the target becomes the phase gate `S` on the control — and `i · I` is a
closure limit of the cyclic orbit `⟨iR_x(πα)⟩` (`iScalar_mem_closure_cyclic_iRx`). Continuity of
`controlledMat` carries the second fact through the controlled embedding
(`image_closure_subset_closure_image`). This is the matrix incarnation of the operator-level
`sGate_onLeft_op_mem_closure_deutschControlledReachableOps`
(`Postulates/API/DeutschGatePhaseGate.lean`). -/
theorem sMatrixKron_mem_closure_deutschControlledReachableMats {α : ℝ} (hα : Irrational α) :
    sMatrix ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ closure (deutschControlledReachableMats α) := by
  rw [← controlledMat_iScalar_eq_sMatrix_kronecker]
  exact image_closure_subset_closure_image continuous_controlledMat
    (Set.mem_image_of_mem _ (iScalar_mem_closure_cyclic_iRx hα))

/-! ### The reversible gate `CNOT` from the once-controlled Deutsch gate -/

/-- **The once-controlled Pauli `X` is `CNOT`:** `controlledMat pauliX = twoQubitCNOT`. Flipping the
target with `X` conditioned on the `|1⟩` control is exactly `|a, b⟩ ↦ |a, a + b⟩`. -/
theorem controlledMat_pauliX_eq_twoQubitCNOT :
    controlledMat pauliX = twoQubitCNOT := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [controlledMat, Matrix.add_apply, Matrix.kronecker_apply, twoQubitCNOT_apply,
    Matrix.diagonal_apply, Matrix.one_apply, pauliX, Prod.mk.injEq]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp

/-- **The reversible gate `CNOT` is reachable from the once-controlled Deutsch gate** (Nielsen &
Chuang, Exercise 4.44, matrix level). When `α` is irrational, `twoQubitCNOT` lies in the closure of
the once-controlled Deutsch iterates `deutschControlledReachableMats α`.

The once-controlled Pauli `X` is `CNOT` (`controlledMat_pauliX_eq_twoQubitCNOT`), and `X` is a
closure limit of the cyclic orbit `⟨iR_x(πα)⟩` (`pauliX_mem_closure_cyclic_iRx`, `X = i · R_x(π)`).
Continuity of `controlledMat` carries the density through. This is the matrix incarnation of the
operator-level `cnotGate_op_mem_closure_deutschControlledReachableOps`
(`Postulates/API/DeutschGateReversible.lean`). -/
theorem twoQubitCNOT_mem_closure_deutschControlledReachableMats {α : ℝ} (hα : Irrational α) :
    twoQubitCNOT ∈ closure (deutschControlledReachableMats α) := by
  rw [← controlledMat_pauliX_eq_twoQubitCNOT]
  exact image_closure_subset_closure_image continuous_controlledMat
    (Set.mem_image_of_mem _ (pauliX_mem_closure_cyclic_iRx hα))

end AxQM.Concrete
