/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledUnitaryDecomposition

/-!
# AxQM.Postulates.API — the dual-rail single-photon qubit

The **dual-rail representation** of a logical qubit into two optical modes
(Nielsen & Chuang §7.4.2): a single photon shared between two modes, with the logical basis

* `dualRailZero` — `|0_L⟩ = |01⟩`, the photon in the second mode, and
* `dualRailOne`  — `|1_L⟩ = |10⟩`, the photon in the first mode,

both pure states of the composite system `qubit ⊗ qubit` (each mode truncated to its
vacuum/one-photon subspace, a `qubit`). A general logical state `c₀|01⟩ + c₁|10⟩` is the pure
state `dualRail c₀ c₁`, the model on which the optical gates of §7.4.2 act.

* `dualRailZero` / `dualRailOne` — the logical basis states `|01⟩` / `|10⟩`, the products
  `|0⟩ ⊗ |1⟩` / `|1⟩ ⊗ |0⟩`.
* `dualRailZero_inner_dualRailOne` — orthogonality `⟨01|10⟩ = 0` (the codewords are distinct).
* `dualRailVec c₀ c₁` — the (unnormalised) superposition vector `c₀·|01⟩ + c₁·|10⟩` in the
  two-qubit state space `qubit.space ⊗[ℂ] qubit.space`.
* `norm_dualRailVec` — `‖c₀·|01⟩ + c₁·|10⟩‖ = 1` when `‖c₀‖² + ‖c₁‖² = 1`; the codewords are
  orthonormal, so the norm is the amplitude norm.
* `dualRail c₀ c₁ h` — the normalised logical state `c₀|01⟩ + c₁|10⟩` on `qubit ⊗ qubit`.
* `phaseShiftGate_onRight_op_qubitBasis` — a phase shifter `P(α)` on the *second* mode multiplies
  the two-mode basis state `|a b⟩` by `[1, e^{iα}]_b`, i.e. it fires only when the photon is in
  that mode (`b = 1`).
* `phaseShiftGate_onRight_op_dualRailVec` — the induced action on a dual-rail superposition:
  `P(α)` on the second mode sends `c₀|01⟩ + c₁|10⟩` to `e^{iα}c₀|01⟩ + c₁|10⟩` (only the `|01⟩`
  component, whose photon is in that mode, picks up the phase). It is used for the
  phase-shift optical circuits of Exercises 7.7–7.10.

## Design notes

The two modes of the dual rail are the left and right factors of `qubit ⊗ qubit`; a phase shifter
localised to one mode is `(phaseShiftGate α).onRight qubit = 1 ⊗ P(α)`, acting nontrivially only on
the factor holding the photon. With the convention `|01⟩ = |0⟩ ⊗ |1⟩` (photon in the *second*
mode), that phase shifter hits the `|01⟩` codeword — matching Exercise 7.7's "phase shift on the
`|01⟩` mode".

The operator lemmas are
proved through `evolvePure` (`Evolution.onRight_evolvePure`) so the scalar factors stay on the
single-qubit state space, mirroring `phase1_op`/`phase3_op`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- The dual-rail **logical zero** `|0_L⟩ = |01⟩`, the product pure state `|0⟩ ⊗ |1⟩` of
`qubit ⊗ qubit`: a single photon in the second mode. -/
def dualRailZero : PureState (qubit ⊗ qubit) := qubitBasis 0 ⊗ qubitBasis 1

/-- The dual-rail **logical one** `|1_L⟩ = |10⟩`, the product pure state `|1⟩ ⊗ |0⟩` of
`qubit ⊗ qubit`: a single photon in the first mode. -/
def dualRailOne : PureState (qubit ⊗ qubit) := qubitBasis 1 ⊗ qubitBasis 0

@[simp]
theorem dualRailZero_vec : dualRailZero.vec = (qubitBasis 0 ⊗ qubitBasis 1).vec := rfl

@[simp]
theorem dualRailOne_vec : dualRailOne.vec = (qubitBasis 1 ⊗ qubitBasis 0).vec := rfl

/-- **Orthogonality of the dual-rail codewords:** `⟨01|10⟩ = 0`. Since `|01⟩ = |0⟩ ⊗ |1⟩` and
`|10⟩ = |1⟩ ⊗ |0⟩` and the single-qubit basis is orthonormal, the tensor inner product factors as
`⟨0|1⟩⟨1|0⟩ = 0`. -/
theorem dualRailZero_inner_dualRailOne :
    (inner ℂ dualRailZero.vec dualRailOne.vec : ℂ) = 0 := by
  rw [dualRailZero_vec, dualRailOne_vec, qubitBasis_tmul_inner]
  norm_num

/-- The **dual-rail superposition vector** `c₀·|01⟩ + c₁·|10⟩` in the two-qubit state space
`qubit.space ⊗[ℂ] qubit.space`. Its norm is the amplitude norm (`norm_dualRailVec`); the
normalised logical state is `dualRail`. -/
def dualRailVec (c0 c1 : ℂ) : (qubit ⊗ qubit).space :=
  c0 • dualRailZero.vec + c1 • dualRailOne.vec

/-- **The dual-rail superposition is normalised** when its amplitudes are:
`‖c₀·|01⟩ + c₁·|10⟩‖ = 1` given `‖c₀‖² + ‖c₁‖² = 1`. The codewords `|01⟩`, `|10⟩` are unit vectors
(they are `PureState.vec`) and orthogonal (`dualRailZero_inner_dualRailOne`), so by the Pythagorean
identity `‖·‖² = ‖c₀‖²·1 + 2·0 + ‖c₁‖²·1 = 1`. -/
theorem norm_dualRailVec (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    ‖dualRailVec c0 c1‖ = 1 := by
  have hsq : ‖dualRailVec c0 c1‖ ^ 2 = 1 := by
    rw [dualRailVec, norm_add_sq (𝕜 := ℂ), norm_smul, norm_smul, dualRailZero.normalized,
      dualRailOne.normalized, inner_smul_left, inner_smul_right, dualRailZero_inner_dualRailOne]
    simp only [mul_one, mul_zero, map_zero, add_zero]
    linarith [h]
  nlinarith [norm_nonneg (dualRailVec c0 c1), hsq]

/-- The **dual-rail logical state** `c₀|01⟩ + c₁|10⟩` as a `PureState (qubit ⊗ qubit)`, for
amplitudes with `‖c₀‖² + ‖c₁‖² = 1`. The general single-photon qubit encoded in two optical modes
(Nielsen & Chuang §7.4.2); the optical gates of §7.4.2 are the unitaries acting on it. -/
def dualRail (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) : PureState (qubit ⊗ qubit) where
  vec := dualRailVec c0 c1
  normalized := norm_dualRailVec c0 c1 h

@[simp]
theorem dualRail_vec (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    (dualRail c0 c1 h).vec = dualRailVec c0 c1 := rfl

/-- **A phase shifter on the second mode acts by `[1, e^{iα}]` on that mode's occupation:**
`(1 ⊗ P(α))|a b⟩ = [1, e^{iα}]_b · |a b⟩`. The phase shifter `(phaseShiftGate α).onRight qubit`
leaves the first factor alone and applies `P(α) = diag(1, e^{iα})` to the second, so the two-mode
basis state `|a⟩ ⊗ |b⟩` picks up `1` when `b = 0` (no photon in that mode) and `e^{iα}` when
`b = 1`. Proved through `Evolution.onRight_evolvePure`, mirroring `phase3_op`. -/
theorem phaseShiftGate_onRight_op_qubitBasis (α : ℝ) (a b : Fin 2) :
    ((phaseShiftGate α).onRight qubit).op ((qubitBasis a ⊗ qubitBasis b).vec)
      = ![(1 : ℂ), Complex.exp ((α : ℂ) * Complex.I)] b • ((qubitBasis a ⊗ qubitBasis b).vec) := by
  rw [← Evolution.evolvePure_vec, Evolution.onRight_evolvePure]
  simp only [PureState.tmul_vec, Evolution.evolvePure_vec, phaseShiftGate_op_apply_qubitBasis]
  exact TensorProduct.tmul_smul _ _ _

/-- **A phase shifter on the second mode multiplies the `|01⟩` amplitude by `e^{iα}`:**
`(1 ⊗ P(α))(c₀|01⟩ + c₁|10⟩) = e^{iα}c₀|01⟩ + c₁|10⟩`. Only the `|01⟩` codeword — whose photon
sits in the phase-shifted (second) mode — acquires the phase; the `|10⟩` codeword is untouched.
The operator form of the dual-rail phase gate `diag(e^{iα}, 1)` (Exercise 7.7's `diag(e^{iπ}, 1)`
at `α = π`). -/
theorem phaseShiftGate_onRight_op_dualRailVec (α : ℝ) (c0 c1 : ℂ) :
    ((phaseShiftGate α).onRight qubit).op (dualRailVec c0 c1)
      = dualRailVec (Complex.exp ((α : ℂ) * Complex.I) * c0) c1 := by
  rw [dualRailVec, dualRailVec, dualRailZero_vec, dualRailOne_vec, map_add, map_smul, map_smul,
    phaseShiftGate_onRight_op_qubitBasis, phaseShiftGate_onRight_op_qubitBasis]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, one_smul, smul_smul]
  rw [mul_comm c0]

end AxQM
