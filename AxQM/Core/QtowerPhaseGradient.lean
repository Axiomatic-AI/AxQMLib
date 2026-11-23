/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QtowerHadamardLayer
import AxQM.Postulates.API.PhasedPlus
import AxQM.Postulates.API.KitaevPhaseEstimation

/-!
# The phase-gradient superposition (N&C §5.2, Figure 5.2) — the output of the controlled powers

The second stage of the phase-estimation circuit (N&C Figure 5.2) is the sequence of controlled
powers `seqCtrlPow U t`. Run on the equal superposition `|+⟩^{⊗t} ⊗ |u⟩` produced by the Hadamard
layer (`AxQM/Core/QtowerHadamardLayer.lean`), when `|u⟩` is an **eigenstate** `U|u⟩ = e^{iθ}|u⟩`
it produces the **phase gradient**: each control wire `w` (of weight `2^w`) picks up the phase
`e^{i·2^w·θ}` on its `|1⟩` branch, so the register becomes the product of phased-plus states

  `⊗_w (|0⟩ + e^{i·2^w·θ}|1⟩)/√2  ⊗  |u⟩ = (1/√2ᵗ) ∑_b e^{iθ·⟦b⟧} |b⟩ ⊗ |u⟩`,

the linear-in-`⟦b⟧` phase that the final inverse QFT reads off as the eigenphase `θ/2π`. This is the
"before inverse QFT" state of phase estimation.

## What is formalised

* `qtowerPhaseGrad θ t u` — the **phase-gradient register** `⊗_w |+_{2^w·θ}⟩ ⊗ |u⟩` on `qtower t S`:
  each control wire in the phased-plus state `qubitPhasePlus (2^w·θ)` (outermost wire the most
  significant, weight `2^t`), tensored with the target `u`. Built through `PureState.tmul` from the
  phased-plus combinator, so its normalization is inherited.
* `controlledUnitary_evolvePure_qubitPlus_hasEigenstate` — the **single-wire phase kickback**:
  if `V|ψ⟩ = e^{iθ}|ψ⟩` then `C(V)(|+⟩ ⊗ |ψ⟩) = |+_θ⟩ ⊗ |ψ⟩` — a controlled gate on a `|+⟩` control
  and an eigenstate target moves the eigenphase onto the control, turning `|+⟩` into `|+_θ⟩` and
  leaving `|ψ⟩` untouched. The atomic step of phase estimation.
* `unCtrl_hasEigenstate_qtowerPhaseGrad` — the **reach-through**: the idle wrap `unCtrl t V` has the
  gradient `qtowerPhaseGrad θ t u` as an eigenstate with the same eigenvalue `V` has on `u`, because
  `unCtrl` acts only on the innermost target `u`.
* `seqCtrlPow_hasEigenstate_qtowerPlusKet` — **the gradient action:** for an eigenstate input
  `U|u⟩ = e^{iθ}|u⟩`, `seqCtrlPow U t (|+⟩^{⊗t} ⊗ |u⟩) = qtowerPhaseGrad θ t u`. Induction on the
  number of controls, peeling the outermost wire: the inner sequence gives the `t`-wire gradient
  (inductive hypothesis), through which the outermost controlled `U^{2^t}` reaches the target
  eigenstate (eigenvalue `e^{i·2^t·θ}` by `HasEigenstate.pow`) and kicks the phase back onto the
  outer `|+⟩` (`controlledUnitary_evolvePure_qubitPlus_hasEigenstate`).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The phase-gradient register -/

/-- **The phase-gradient register** `⊗_w |+_{2^w·θ}⟩ ⊗ |u⟩` on `qtower t S`: each of the `t` control
wires in the phased-plus state `qubitPhasePlus (2^w·θ)` (the outermost wire most significant, weight
`2^t`), tensored with the target pure state `u`. The output of the controlled-power sequence on the
prepared superposition when the target is an eigenstate of eigenphase `θ`; built through
`PureState.tmul` so its normalization is inherited. -/
def qtowerPhaseGrad (θ : ℝ) : (t : ℕ) → PureState S → PureState (qtower t S)
  | 0, u => u
  | (t + 1), u => qubitPhasePlus ((2 : ℝ) ^ t * θ) ⊗ qtowerPhaseGrad θ t u

@[simp] theorem qtowerPhaseGrad_zero (θ : ℝ) (u : PureState S) : qtowerPhaseGrad θ 0 u = u := rfl

/-- Peeling the outermost wire of the phase-gradient register:
`qtowerPhaseGrad θ (t+1) u = |+_{2^t·θ}⟩ ⊗ qtowerPhaseGrad θ t u`. -/
theorem qtowerPhaseGrad_succ (θ : ℝ) (t : ℕ) (u : PureState S) :
    qtowerPhaseGrad θ (t + 1) u = qubitPhasePlus ((2 : ℝ) ^ t * θ) ⊗ qtowerPhaseGrad θ t u := rfl

/-! ### The single-wire phase kickback -/

/-- **Single-wire phase kickback.** If `|ψ⟩` is an eigenstate of `V` with eigenvalue `e^{iθ}`
(`V.HasEigenstate (e^{iθ}) ψ`), then the controlled gate `C(V)` on a `|+⟩` control and target `|ψ⟩`
moves the eigenphase onto the control, turning `|+⟩` into the phased-plus state `|+_θ⟩` and leaving
`|ψ⟩` unchanged: `C(V)(|+⟩ ⊗ |ψ⟩) = |+_θ⟩ ⊗ |ψ⟩`.

The atomic step of phase estimation. Proof at the vector level: unfold `C(V)` to its block operator
`|0⟩⟨0|⊗1 + |1⟩⟨1|⊗V` and apply it to `|+⟩ ⊗ |ψ⟩`; the two rank-one projectors reduce against `|+⟩`
(`⟨i|+⟩ = 1/√2`, `inner_qubitBasis_qubitPlus`) and the `|1⟩` branch turns `V|ψ⟩` into `e^{iθ}|ψ⟩`
(the eigenvalue hypothesis), leaving `(1/√2)(|0⟩ + e^{iθ}|1⟩) ⊗ |ψ⟩ = |+_θ⟩ ⊗ |ψ⟩`
(`qubitPhasePlus_vec`) — the residual qubit-factor amplitude identity closing by `module`. -/
theorem controlledUnitary_evolvePure_qubitPlus_hasEigenstate (V : Evolution S) (θ : ℝ)
    (ψ : PureState S) (h : V.HasEigenstate (Complex.exp ((θ : ℂ) * Complex.I)) ψ) :
    (controlledUnitary V).evolvePure (qubitPlus ⊗ ψ) = qubitPhasePlus θ ⊗ ψ := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, PureState.tmul_vec, PureState.tmul_vec, qubitPhasePlus_vec]
  -- Unfold the controlled gate to its block operator `|0⟩⟨0|⊗1 + |1⟩⟨1|⊗V`, apply it to the
  -- product, and reduce the two rank-one projectors against `|+⟩` (`⟨i|+⟩ = 1/√2`). Every scalar
  -- stays on the qubit factor, so the residual amplitude identity closes by `module`.
  change (TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec)
        (1 : S.space →L[ℂ] S.space)
      + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec) V.op)
      (qubitPlus.vec ⊗ₜ[ℂ] ψ.vec) = _
  rw [add_apply, TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
    InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply, one_apply_eq_self,
    inner_qubitBasis_qubitPlus, inner_qubitBasis_qubitPlus, Concrete.xPlus_apply,
    Concrete.xPlus_apply, show V.op ψ.vec = Complex.exp ((θ : ℂ) * Complex.I) • ψ.vec from h,
    ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
  congr 1
  module

/-! ### Reaching through the controls to the target -/

/-- **The idle wrap reaches through to the target of the phase gradient.** `unCtrl t V` (`V`
wrapped by `t` idle control qubits) leaves the gradient's `t` phased-plus control factors untouched
and applies `V` to the innermost target: `(unCtrl t V)(qtowerPhaseGrad θ t u) = qtowerPhaseGrad θ t
(V|u⟩)`. Induction on the number of controls, peeling one idle wire
(`Evolution.onRight_evolvePure`).
The arbitrary-target analogue of `unCtrl_evolvePure_qtowerKet`. -/
theorem unCtrl_evolvePure_qtowerPhaseGrad (V : Evolution S) (θ : ℝ) :
    ∀ (t : ℕ) (u : PureState S),
      (unCtrl t V).evolvePure (qtowerPhaseGrad θ t u) = qtowerPhaseGrad θ t (V.evolvePure u)
  | 0, _ => rfl
  | (t + 1), u => by
    simp only [qtower, unCtrl_succ, qtowerPhaseGrad_succ, Evolution.onRight_evolvePure,
      unCtrl_evolvePure_qtowerPhaseGrad V θ t u]

/-- **The idle wrap has the phase gradient as an eigenstate.** If `V|u⟩ = μ|u⟩` then the idle wrap
`unCtrl t V` has the phase-gradient register `qtowerPhaseGrad θ t u` as an eigenstate with the
*same*
eigenvalue `μ`: `unCtrl` reaches through the `t` control wires to the innermost target `u`
(`unCtrl_evolvePure_qtowerPhaseGrad`), and `qtowerPhaseGrad` is linear in the target's global phase
(the `vecscale` induction, `|+_·⟩^{⊗t} ⊗ (c • u) = c • (|+_·⟩^{⊗t} ⊗ u)`), so the eigenphase `μ`
factors out. -/
theorem unCtrl_hasEigenstate_qtowerPhaseGrad (V : Evolution S) {μ : ℂ} {u : PureState S}
    (h : V.HasEigenstate μ u) (θ : ℝ) (t : ℕ) :
    (unCtrl t V).HasEigenstate μ (qtowerPhaseGrad θ t u) := by
  have vecscale : ∀ (c : ℂ) (v w : PureState S), w.vec = c • v.vec →
      ∀ s : ℕ, (qtowerPhaseGrad θ s w).vec = c • (qtowerPhaseGrad θ s v).vec := by
    intro c v w hvw s
    induction s with
    | zero => exact hvw
    | succ s ih =>
        rw [qtowerPhaseGrad_succ, qtowerPhaseGrad_succ, PureState.tmul_vec, PureState.tmul_vec, ih]
        exact TensorProduct.tmul_smul _ _ _
  rw [Evolution.HasEigenstate, ← Evolution.evolvePure_vec, unCtrl_evolvePure_qtowerPhaseGrad]
  have hVu : (V.evolvePure u).vec = μ • u.vec := by rw [Evolution.evolvePure_vec]; exact h
  exact vecscale μ u (V.evolvePure u) hVu t

/-! ### The gradient action of the controlled-power sequence -/

/-- **The controlled powers produce the phase gradient.** For an eigenstate input
`U|u⟩ = e^{iθ}|u⟩` (`U.HasEigenstate (e^{iθ}) u`), the controlled-power sequence `seqCtrlPow U t`
(N&C Figure 5.2, second stage) takes the prepared equal superposition `|+⟩^{⊗t} ⊗ |u⟩`
(`qtowerPlusKet t u`) to the phase-gradient register `⊗_w |+_{2^w·θ}⟩ ⊗ |u⟩`
(`qtowerPhaseGrad θ t u`):
`seqCtrlPow U t (|+⟩^{⊗t} ⊗ |u⟩) = qtowerPhaseGrad θ t u`.

Each control wire `w` ends in the phased-plus state carrying the eigenphase `2^w·θ` scaled by its
weight — the linear-in-control-value phase gradient the final inverse QFT reads out.

Induction on the number of controls `t`, peeling the outermost wire (`seqCtrlPow_succ`,
`qtowerPlusKet_succ`): the inner sequence produces the `t`-wire gradient
`qtowerPhaseGrad θ t u` (inductive hypothesis, through `Evolution.onRight_evolvePure`), which is an
eigenstate of the outermost controlled `U^{2^t}` with eigenvalue `(e^{iθ})^{2^t} = e^{i·2^t·θ}`
(`unCtrl_hasEigenstate_qtowerPhaseGrad` on `Evolution.HasEigenstate.pow`); the single-wire kickback
`controlledUnitary_evolvePure_qubitPlus_hasEigenstate` then turns the outer `|+⟩` into
`|+_{2^t·θ}⟩`,
building `qtowerPhaseGrad θ (t+1) u`. -/
theorem seqCtrlPow_hasEigenstate_qtowerPlusKet (U : Evolution S) (θ : ℝ) (u : PureState S)
    (h : U.HasEigenstate (Complex.exp ((θ : ℂ) * Complex.I)) u) :
    ∀ t : ℕ, (seqCtrlPow U t).evolvePure (qtowerPlusKet t u) = qtowerPhaseGrad θ t u
  | 0 => by
    simp only [seqCtrlPow_zero, qtowerPlusKet_zero, qtowerPhaseGrad_zero]
    exact Evolution.id_evolvePure u
  | (t + 1) => by
    have ih := seqCtrlPow_hasEigenstate_qtowerPlusKet U θ u h t
    simp only [qtower, seqCtrlPow_succ, qtowerPlusKet_succ, Evolution.evolvePure_comp,
      Evolution.onRight_evolvePure, ih, qtowerPhaseGrad_succ]
    apply controlledUnitary_evolvePure_qubitPlus_hasEigenstate
    have hpow : (U ^ 2 ^ t).HasEigenstate ((Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 ^ t) u :=
      Evolution.HasEigenstate.pow h (2 ^ t)
    have hexp : (Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 ^ t
        = Complex.exp (((((2 : ℝ) ^ t * θ) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_natCast_mul]
      congr 1
      push_cast
      ring
    rw [hexp] at hpow
    exact unCtrl_hasEigenstate_qtowerPhaseGrad (U ^ 2 ^ t) hpow θ t

end AxQM
