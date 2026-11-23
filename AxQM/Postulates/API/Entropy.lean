/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.StateSpace
import AxQM.Postulates.SystemIso
import ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropy

/-!
# AxQM — von Neumann entropy of a quantum state

The **von Neumann entropy** `S(ρ)` of a quantum state `ρ` (Nielsen–Chuang §11.3.1, eq. (11.44)) is

`S(ρ) = -tr(ρ log ρ) = H(λ₁, …, λ_d)`,

the Shannon entropy of the eigenvalue spectrum `λ₁, …, λ_d` of the density operator `ρ`. It is the
central quantity of Nielsen–Chuang Chapter 11 and the quantum generalization of the Shannon entropy.

This file defines `State.vonNeumannEntropy`, the entropy of a state in terms of the operator-level
`ContinuousLinearMap.vonNeumannEntropy` of its density operator, together with the
basic properties collected in Nielsen–Chuang Theorem 11.8: non-negativity, the `log d` upper bound
(attained by the maximally mixed state), and the vanishing of the entropy on pure states.

## Main definitions

* `AxQM.State.vonNeumannEntropy` — the von Neumann entropy `S(ρ)` of a state `ρ`.

## Main results

* `AxQM.State.vonNeumannEntropy_nonneg` — `S(ρ) ≥ 0`.
* `AxQM.State.vonNeumannEntropy_le_log_finrank` — `S(ρ) ≤ log d`, `d = dim S.space`.
* `AxQM.PureState.vonNeumannEntropy_toState_eq_zero` — a pure state has zero entropy.
* `AxQM.State.vonNeumannEntropy_congr` — entropy is invariant under transport along a
  system isomorphism.
-/

namespace AxQM

variable {S : QSystem}

/-- The **von Neumann entropy** `S(ρ) = -tr(ρ log ρ)` of a quantum state `ρ`
(Nielsen–Chuang §11.3.1, eq. (11.44)): the Shannon entropy of the eigenvalue spectrum of the
density operator `ρ.op`. Defined through `ContinuousLinearMap.vonNeumannEntropy`. -/
noncomputable def State.vonNeumannEntropy (ρ : State S) : ℝ :=
  ρ.op.vonNeumannEntropy

/-- The `_op` bridge: the state's von Neumann entropy is the operator-level von Neumann entropy of
its density operator. Holds definitionally; provided so proofs can rewrite
between `State.vonNeumannEntropy` and `ContinuousLinearMap.vonNeumannEntropy`. -/
theorem State.vonNeumannEntropy_def (ρ : State S) :
    ρ.vonNeumannEntropy = ρ.op.vonNeumannEntropy :=
  rfl

/-- **Non-negativity of the von Neumann entropy** (Nielsen–Chuang Theorem 11.8, first item):
`S(ρ) ≥ 0`, since the eigenvalues of a density operator form a probability distribution and Shannon
entropy is non-negative. -/
theorem State.vonNeumannEntropy_nonneg (ρ : State S) : 0 ≤ ρ.vonNeumannEntropy :=
  ρ.isDensity.vonNeumannEntropy_nonneg

/-- **Upper bound on the von Neumann entropy** (Nielsen–Chuang Theorem 11.8, second item):
`S(ρ) ≤ log d` where `d = dim S.space`, with equality for the maximally mixed state. The
nontriviality of `S.space` needed by the underlying bound comes from `State.nontrivial_space`. -/
theorem State.vonNeumannEntropy_le_log_finrank (ρ : State S) :
    ρ.vonNeumannEntropy ≤ Real.log (Module.finrank ℂ S.space : ℝ) := by
  have := ρ.nontrivial_space
  exact ρ.isDensity.vonNeumannEntropy_le_log_dim

/-- **A pure state has zero von Neumann entropy** (Nielsen–Chuang Theorem 11.8, purity item):
`S(|ψ⟩⟨ψ|) = 0`, since the density operator `|ψ⟩⟨ψ|` of a pure state is a rank-one projector whose
spectrum is `(1, 0, …, 0)`. -/
theorem PureState.vonNeumannEntropy_toState_eq_zero (ψ : PureState S) :
    ψ.toState.vonNeumannEntropy = 0 := by
  rw [State.vonNeumannEntropy_def, ψ.toState_op]
  exact ContinuousLinearMap.vonNeumannEntropy_rankOne_self ψ.normalized

/-- **Invariance of the von Neumann entropy under transport**: a system isomorphism does not
change the entropy, `S(e ρ e⁻¹) = S(ρ)`. Rides the operator-level invariance
`ContinuousLinearMap.vonNeumannEntropy_conjStarAlgEquiv` (conjugating by an isometry preserves
the eigenvalue spectrum, hence the entropy) through the `State.congr` transport. The entropy
counterpart of `State.expectation_congr`; used e.g. to read the entropy of a re-associated
tripartite state (strong subadditivity, N&C Theorem 11.14). -/
@[simp] theorem State.vonNeumannEntropy_congr {S T : QSystem} (e : S ≃ₛ T) (ρ : State S) :
    (ρ.congr e).vonNeumannEntropy = ρ.vonNeumannEntropy := by
  rw [State.vonNeumannEntropy_def, State.congr_op,
    ContinuousLinearMap.vonNeumannEntropy_conjStarAlgEquiv, ← State.vonNeumannEntropy_def]

end AxQM
