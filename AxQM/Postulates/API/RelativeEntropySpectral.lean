/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RelativeEntropy
import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropyDiagonal

/-!
# AxQM — the spectral value of the quantum relative entropy

The companion of `EntropySpectral` (the spectral value of the von Neumann entropy) for the **quantum
relative entropy**. When two density operators share an eigenbasis — equivalently, when they commute
— the Umegaki relative entropy `S(ρ ‖ σ) = tr(ρ log ρ) − tr(ρ log σ)` carries nothing genuinely
quantum: it collapses to the **classical Kullback–Leibler divergence** of the two eigenvalue
distributions,

`S(ρ ‖ σ) = D(p ‖ q) = ∑ᵢ pᵢ (log pᵢ − log qᵢ)`.

This is the analytic content behind the modern proof of the **Holevo bound** (Nielsen–Chuang
Theorem 12.1): the two states there are the Born-diagonal images `𝓜(ρ), 𝓜(σ)` of a measurement
outcome channel — both diagonal in the classical outcome basis — so their relative entropy is the
classical KL divergence of the Born distributions `D(p_E(ρ) ‖ p_E(σ))`, the quantity the measurement
data-processing inequality bounds by `S(ρ ‖ σ)`.

This file lifts the operator identity
`ContinuousLinearMap.quantumRelativeEntropy_eq_relativeEntropy_of_isEigenbasis` to states,
exactly as `AxQM/Postulates/API/RelativeEntropy.lean` lifts the other operator-level
relative-entropy lemmas (Klein, joint convexity, partial-trace monotonicity). The
measurement-channel specialization used in the Holevo bound,
`Measurement.quantumRelativeEntropy_measState_eq_relativeEntropy_bornProb` in
`Core/MeasurementChannel.lean`, uses the operator identity directly; the statement here is the
general one for states.

## Main results

* `AxQM.State.quantumRelativeEntropy_eq_relativeEntropy_of_isEigenbasis` — for an
  orthonormal basis simultaneously diagonalizing `ρ` (eigenvalues `p`) and `σ` (eigenvalues `q`),
  `S(ρ ‖ σ) = Real.relativeEntropy p q`.
-/

namespace AxQM

variable {S : QSystem}

/-- **Diagonal quantum relative entropy is the classical Kullback–Leibler divergence.** If an
orthonormal basis `b` simultaneously diagonalizes both `ρ.op` (with real eigenvalue sequence `p`)
and `σ.op` (with real eigenvalue sequence `q`) — `ρ.op (b i) = pᵢ • b i` and `σ.op (b i) = qᵢ • b i`
— then the quantum relative entropy collapses to the classical relative entropy of the eigenvalue
distributions,

`S(ρ ‖ σ) = D(p ‖ q) = ∑ᵢ pᵢ (log pᵢ − log qᵢ)`.

Two density operators sharing an eigenbasis (equivalently, commuting) carry no genuinely quantum
relative entropy: their Umegaki relative entropy is exactly the classical `Real.relativeEntropy` of
their eigenvalue distributions. This is the analytic content behind the modern proof of the Holevo
bound (Nielsen–Chuang Theorem 12.1), applied to the Born-diagonal images `𝓜(ρ), 𝓜(σ)` of a
measurement outcome channel.

The `State`-level lift of the operator identity
`ContinuousLinearMap.quantumRelativeEntropy_eq_relativeEntropy_of_isEigenbasis`, through the
definitional bridge `quantumRelativeEntropy_def` and the self-adjointness of every density operator.
The equality is **unconditional** — no faithfulness of `σ` is required: `Real.log` is continuous on
the (finite) spectrum of any self-adjoint operator even where `0` occurs, and both sides use the
convention `Real.log 0 = 0` consistently, so zero eigenvalues are harmless. -/
theorem State.quantumRelativeEntropy_eq_relativeEntropy_of_isEigenbasis {ι : Type*} [Fintype ι]
    (ρ σ : State S) (b : OrthonormalBasis ι ℂ S.space) {p q : ι → ℝ}
    (hp : ∀ i, ρ.op (b i) = (p i : ℂ) • b i)
    (hq : ∀ i, σ.op (b i) = (q i : ℂ) • b i) :
    ρ.quantumRelativeEntropy σ = Real.relativeEntropy p q := by
  rw [State.quantumRelativeEntropy_def]
  exact ContinuousLinearMap.quantumRelativeEntropy_eq_relativeEntropy_of_isEigenbasis b
    ρ.isDensity.isPositive.isSelfAdjoint σ.isDensity.isPositive.isSelfAdjoint hp hq

end AxQM
