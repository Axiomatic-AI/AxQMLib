/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DualRail

/-!
# Nielsen & Chuang, Exercise 7.7 (phase shift on a dual-rail qubit)

*(N&C p. 291.)*

Show the phase-shift circuit transforms a dual-rail state by diag(e^{iπ},1).

**The physics (N&C §7.4.2).** A logical qubit is dual-rail encoded as a single photon shared
between two optical modes, `|ψ_in⟩ = c₀|01⟩ + c₁|10⟩` (`dualRail`). A phase shifter `P(π)` placed
on the mode carrying the `|01⟩` photon (the "top wire", the second factor of `qubit ⊗ qubit`)
retards that mode's phase: `P(π)|1⟩ = e^{iπ}|1⟩`, `P(π)|0⟩ = |0⟩`. So the `|01⟩` component — whose
photon passes through the shifter — acquires `e^{iπ}`, while the `|10⟩` component, whose photon is
in the other mode, is untouched. The net logical operation is therefore multiplication by the
matrix `diag(e^{iπ}, 1) = diag(-1, 1)` in the `{|01⟩, |10⟩}` basis, which is exactly (7.23).

## The formalisation

The exercise's *circuit* is `phaseShiftCircuit = (phaseShiftGate π).onRight qubit`, the phase
shifter `1 ⊗ P(π)` acting on the second mode of `qubit ⊗ qubit`. Its action is captured by:

* `phaseShiftCircuit_evolvePure_dualRail` — the **headline**: the circuit sends the dual-rail state
  with amplitudes `(c₀, c₁)` to the one with amplitudes `(e^{iπ}c₀, c₁)`, i.e. it acts by the
  matrix `diag(e^{iπ}, 1)` of (7.23) on the logical amplitude vector `|ψ_in⟩`.
* `phaseShiftCircuit_evolvePure_dualRailOne` — the **`|1_L⟩` fixed point**: `|10⟩` (photon in the
  unshifted mode) is left invariant, the `diag(·, 1)` corner of (7.23). The `|0_L⟩` behaviour
  `|01⟩ ↦ e^{iπ}|01⟩` is the `(c₀, c₁) = (1, 0)` case of the headline.

The dual-rail encoding itself (`dualRail`, the logical basis states, and the operator action of the
phase shifter), which serves all of §7.4.2, is in `AxQM/Postulates/API/DualRail.lean`; this file
states the exercise's circuit and its transformation in terms of `evolvePure` and `dualRail`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **Exercise 7.7 optical circuit**: a phase shifter `P(π)` on the `|01⟩` mode of a dual-rail
qubit, i.e. `1 ⊗ P(π)` on the second factor of `qubit ⊗ qubit` (`(phaseShiftGate π).onRight qubit`).
The boxed-`π` phase shifter of the exercise's figure. -/
def phaseShiftCircuit : Evolution (qubit ⊗ qubit) := (phaseShiftGate Real.pi).onRight qubit

/-- **Exercise 7.7 (7.23):** the phase-shift circuit transforms the dual-rail state by
`diag(e^{iπ}, 1)`. Acting on `|ψ_in⟩ = c₀|01⟩ + c₁|10⟩` it produces `e^{iπ}c₀|01⟩ + c₁|10⟩`: the
`|01⟩` amplitude — whose photon traverses the phase shifter — is multiplied by `e^{iπ}`, the `|10⟩`
amplitude is unchanged. This is precisely the matrix `diag(e^{iπ}, 1)` acting on the logical
amplitude vector `(c₀, c₁)`. (The output amplitudes are again normalised since `‖e^{iπ}‖ = 1`.) -/
theorem phaseShiftCircuit_evolvePure_dualRail (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    phaseShiftCircuit.evolvePure (dualRail c0 c1 h)
      = dualRail (Complex.exp ((Real.pi : ℂ) * Complex.I) * c0) c1
          (by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]; exact h) := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, dualRail_vec, dualRail_vec, phaseShiftCircuit]
  exact phaseShiftGate_onRight_op_dualRailVec Real.pi c0 c1

/-- **The logical one `|1_L⟩ = |10⟩` is a fixed point** of the Exercise 7.7 circuit: its photon sits
in the unshifted mode, so the phase shifter leaves it invariant. This is the `diag(·, 1)` corner of
(7.23) — the eigenvalue `1` on `|10⟩`. -/
theorem phaseShiftCircuit_evolvePure_dualRailOne :
    phaseShiftCircuit.evolvePure dualRailOne = dualRailOne := by
  rw [phaseShiftCircuit, dualRailOne, Evolution.onRight_evolvePure,
    phaseShiftGate_evolvePure_qubitBasis_zero]

end AxQM
