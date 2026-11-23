/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledUnitary
import AxQM.Postulates.API.PhasedPlus

/-!
# A controlled gate rotates a phased-plus control wire (N&C Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) peels the head control wire's Figure 5.1
gates off `qftTowerEvolution (n+1)`: a Hadamard puts the head wire into the phased-plus state
`|+_α⟩ = (|0⟩ + e^{iα}|1⟩)/√2`, and then a *cascade of controlled-`Rₖ` phase gates* — controlled on
the head wire — acts on it. Each such gate is `controlledUnitary W` for a diagonal phase gate `W`;
on a computational-basis target it multiplies the target by a scalar phase `e^{iβ}`. This file
supplies the single-gate fact that powers that peel: a controlled gate whose inner gate acts on the
target as a **scalar phase** `e^{iβ}` simply **advances the control's phased-plus angle** by `β`.

## What is formalised

* `controlledUnitary_evolvePure_qubitPhasePlus` — for a control in the phased-plus state `|+_α⟩` and
  a target `φ` on which the inner gate `W` acts as a scalar phase, `(W|φ⟩ = e^{iβ}|φ⟩`),

    `C(W) (|+_α⟩ ⊗ φ) = |+_{α+β}⟩ ⊗ φ`.

  The `|0⟩` branch of the control is untouched and the `|1⟩` branch picks up the extra phase
  `e^{iβ}` from the target gate, so the two branches recombine into a phased-plus state with its
  relative phase advanced from `α` to `α + β`, the target `φ` returned unchanged. (A controlled gate
  whose target action is a genuine scalar phase feeds that phase back onto the control — the
  interferometric "phase kickback" that drives phase estimation and the QFT alike.)

It is proved from the phased-plus state `qubitPhasePlus` (in `AxQM/Postulates/API/PhasedPlus.lean`)
and the controlled-gate basis actions `controlledUnitary_evolvePure_ket{Zero,One}` (in
`AxQM/Postulates/API/ControlledUnitary.lean`). It is used in `AxQM/Core/QtowerHeadPhaseControl.lean`
for the action of the tower's head cascade.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **A controlled gate rotates a phased-plus control wire.** If the inner gate `W` acts on the
target state `φ` as the scalar phase `e^{iβ}` — `(W.evolvePure φ).vec = e^{iβ} • φ.vec` — then the
controlled gate `C(W)` sends the phased-plus control state `|+_α⟩` tensored with `φ` to the
phased-plus state with angle advanced by `β`, the target returned unchanged:

  `C(W) (|+_α⟩ ⊗ φ) = |+_{α+β}⟩ ⊗ φ`.

The `|0⟩` branch of the control is fixed (`controlledUnitary_evolvePure_ketZero`) and the `|1⟩`
branch picks up `e^{iβ}` from the target gate (`controlledUnitary_evolvePure_ketOne` and the
scalar-phase hypothesis), so the two recombine into `|+_{α+β}⟩ = (|0⟩ + e^{i(α+β)}|1⟩)/√2` — the
phase kicked back onto the control. -/
theorem controlledUnitary_evolvePure_qubitPhasePlus {S : QSystem} (W : Evolution S)
    (φ : PureState S) (α β : ℝ)
    (hW : (W.evolvePure φ).vec = Complex.exp ((β : ℂ) * Complex.I) • φ.vec) :
    (controlledUnitary W).evolvePure ((qubitPhasePlus α).tmul φ)
      = (qubitPhasePlus (α + β)).tmul φ := by
  -- The target phase `e^{iβ}` and the control phase `e^{iα}` merge into `e^{i(α+β)}`.
  have hexp : Complex.exp ((α : ℂ) * Complex.I) * Complex.exp ((β : ℂ) * Complex.I)
      = Complex.exp (((α + β : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  -- The scalar-phase hypothesis at the operator level (`W.op x = (W.evolvePure x).vec`).
  have hW' : W.op φ.vec = Complex.exp ((β : ℂ) * Complex.I) • φ.vec := hW
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec, qubitPhasePlus_vec]
  -- Unfold `C(W).op` to `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ W` so the tensor-map linearity lemmas fire. A
  -- `change` (defeq to `controlledUnitary_op`'s rfl RHS) is needed, not `rw [controlledUnitary_op]`
  -- — whose rewrite leaves ill-resolved instances on which `add_apply` fails to match — the same
  -- `change` idiom the sibling `controlledUnitary_evolvePure_ket{Zero,One}` proofs use.
  change (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
        (1 : S.space →L[ℂ] S.space)
      + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec) W.op)
      ((Concrete.invSqrt2 • ((qubitBasis 0).vec
          + Complex.exp ((α : ℂ) * Complex.I) • (qubitBasis 1).vec)) ⊗ₜ[ℂ] φ.vec)
      = (Concrete.invSqrt2 • ((qubitBasis 0).vec
          + Complex.exp (((α + β : ℝ) : ℂ) * Complex.I) • (qubitBasis 1).vec)) ⊗ₜ[ℂ] φ.vec
  simp only [map_add, map_smul, add_apply, TensorProduct.mapL_tmul,
    InnerProductSpace.rankOne_apply, one_apply_eq_self, qubitBasis_inner_qubitBasis,
    hW']
  -- Reduce the branch inner products, collapse the killed branches, gather the scalars.
  simp only [Fin.isValue, ↓reduceIte, zero_ne_one, one_ne_zero, zero_smul, smul_zero, add_zero,
    zero_add, one_smul, TensorProduct.tmul_smul, smul_smul, TensorProduct.smul_tmul']
  -- Combine the control phase `e^{iα}` and the kicked-back target phase `e^{iβ}` into `e^{i(α+β)}`,
  -- then distribute the phased-plus output over its two branches.
  rw [show
      Complex.exp ((β : ℂ) * Complex.I) * (Concrete.invSqrt2 * Complex.exp ((α : ℂ) * Complex.I))
        = Concrete.invSqrt2 * Complex.exp (((α + β : ℝ) : ℂ) * Complex.I) from by rw [← hexp]; ring,
    smul_add, TensorProduct.add_tmul, smul_smul]

end AxQM
