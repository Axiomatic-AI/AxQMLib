/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.UnreadMeasurement
import AxQM.Postulates.API.Entropy
import AxQM.Postulates.API.RelativeEntropy
import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropyPinching
import ToMathlib.Analysis.InnerProductSpace.GeneralizedKleinInequality

/-!
# N&C Theorem 11.9 — Projective measurements increase entropy

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.9, p. 515.

Projective measurements increase entropy: S(rho')>=S(rho), equality iff rho=rho'.

Here `ρ'` is the **unread (non-selective) post-measurement state**
(`AxQM.Measurement.unreadState`) of a **projective** measurement
(`AxQM.Measurement.IsProjective`), and `S` is the von Neumann entropy
(`AxQM.State.vonNeumannEntropy`).

## The two claims

The theorem's two independent claims are formalised as two named theorems, not bundled into one
conjunction:

* `Measurement.IsProjective.vonNeumannEntropy_unreadState_ge` — `S(ρ) ≤ S(ρ')` (eq. (11.66)).
* `Measurement.IsProjective.vonNeumannEntropy_unreadState_eq_iff` — `S(ρ') = S(ρ) ↔ ρ' = ρ`,
  the equality condition.

Both statements are about `Measurement`, `Measurement.IsProjective`, `Measurement.unreadState`,
`State` and `State.vonNeumannEntropy`. Compare Klein's inequality, Theorem 11.7
(`AxQM/NC/Ch11/Theorem11_7.lean`).

## Proof, and fidelity to N&C

The proof is exactly Nielsen & Chuang's: apply Klein's inequality to `ρ` and `ρ'` and use the
**entropy-increase identity** `D(ρ ‖ ρ') = S(ρ') − S(ρ)`. That identity holds because each
projector `Pᵢ` commutes with `ρ' = Σⱼ Pⱼ ρ Pⱼ`, hence with `log ρ'`, so the completeness relation
`Σᵢ Pᵢ = 1` and cyclicity of the trace give `tr((log ρ') ρ) = tr((log ρ') ρ') = −S(ρ')` — i.e.
`−tr(ρ log ρ') = S(ρ')` (N&C eqs. (11.68)–(11.71)). Non-negativity of `D` then gives `S(ρ') ≥ S(ρ)`,
and the equality case of Klein gives `ρ = ρ'`.

The result is proved in **full N&C generality** — for *every* density operator `ρ`, with no
faithfulness hypothesis (which would be a silent weakening). The
faithful Klein inequality needs the second argument full-rank, but here `ρ' = Σᵢ Pᵢ ρ Pᵢ` is
generally rank-deficient. This is handled by the **support condition**: the pinching never enlarges
the support, `ker ρ' ≤ ker ρ` (`ContinuousLinearMap.hasSupportLE_krausSumₗ_of_isStarProjection`),
under which the non-faithful Klein inequality applies. The two ingredients are in
`ToMathlib/`:

* `ContinuousLinearMap.quantumRelativeEntropy_krausSumₗ_eq_vonNeumannEntropy_sub` — the
  entropy-increase identity `D(ρ ‖ Σᵢ Pᵢ ρ Pᵢ) = S(Σᵢ Pᵢ ρ Pᵢ) − S(ρ)`;
* `ContinuousLinearMap.quantumRelativeEntropy_nonneg_of_hasSupportLE` and
  `ContinuousLinearMap.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE` — the non-faithful Klein
  inequality `D ≥ 0` and `D = 0 ↔ ρ = σ` under `HasSupportLE ρ σ`.

The unread state `ρ'` of a projective measurement has operator `Σᵢ Pᵢ ρ Pᵢ` on the nose
(`Measurement.unreadState_op` gives `ρ'.op = krausSumₗ m.op ρ.op`, and for a projective measurement
`krausSumₗ m.op ρ.op = Σᵢ Pᵢ ρ Pᵢ`), so the operator results apply directly to states through the
`_def` bridges.
-/

open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- **Nielsen & Chuang Theorem 11.9, eq. (11.66): projective measurements never decrease entropy.**
For a projective measurement `m` and any state `ρ`, the unread (non-selective) post-measurement
state `ρ' = Σᵢ Pᵢ ρ Pᵢ` (`m.unreadState ρ`) has entropy at least that of `ρ`,

  `S(ρ) ≤ S(ρ')`.

Proof (N&C's): the entropy-increase identity `D(ρ ‖ ρ') = S(ρ') − S(ρ)`, together with
non-negativity of the relative entropy under the support condition `ker ρ' ≤ ker ρ` — which the
pinching always satisfies — gives `0 ≤ S(ρ') − S(ρ)`. Full N&C generality: no faithfulness
hypothesis on `ρ`. -/
theorem Measurement.IsProjective.vonNeumannEntropy_unreadState_ge {m : Measurement ι S}
    (h : m.IsProjective) (ρ : State S) :
    ρ.vonNeumannEntropy ≤ (m.unreadState ρ).vonNeumannEntropy := by
  have hP : ∀ i, IsStarProjection (m.op i) := h
  have horth : ∀ i j, i ≠ j → m.op i * m.op j = 0 := fun _ _ hij => h.orthogonal hij
  have hsum : ∑ i, m.op i = 1 := h.sum_op_eq_one
  have hρ : ρ.op.IsDensityOp := ρ.isDensity
  have hρ'D : (krausSumₗ m.op ρ.op).IsDensityOp :=
    isDensityOp_krausSumₗ_of_isStarProjection hP hsum hρ
  have hsupp : HasSupportLE ρ.op (krausSumₗ m.op ρ.op) :=
    hasSupportLE_krausSumₗ_of_isStarProjection hP hsum hρ.isPositive
  have hident := quantumRelativeEntropy_krausSumₗ_eq_vonNeumannEntropy_sub hP horth hsum hρ
  have hnonneg := hρ.quantumRelativeEntropy_nonneg_of_hasSupportLE hρ'D hsupp
  rw [State.vonNeumannEntropy_def ρ, State.vonNeumannEntropy_def (m.unreadState ρ),
    Measurement.unreadState_op]
  rw [hident] at hnonneg
  linarith

/-- **Nielsen & Chuang Theorem 11.9, equality condition.** For a projective measurement `m` and any
state `ρ`, the unread post-measurement state `ρ' = Σᵢ Pᵢ ρ Pᵢ` (`m.unreadState ρ`) has the *same*
entropy as `ρ` if and only if the measurement leaves the state unchanged,

  `S(ρ') = S(ρ) ↔ ρ' = ρ`.

Proof: by the entropy-increase identity `D(ρ ‖ ρ') = S(ρ') − S(ρ)`, `S(ρ') = S(ρ)` is equivalent to
`D(ρ ‖ ρ') = 0`, which by the equality case of the (non-faithful) Klein inequality holds iff
`ρ = ρ'`. -/
theorem Measurement.IsProjective.vonNeumannEntropy_unreadState_eq_iff {m : Measurement ι S}
    (h : m.IsProjective) (ρ : State S) :
    (m.unreadState ρ).vonNeumannEntropy = ρ.vonNeumannEntropy ↔ m.unreadState ρ = ρ := by
  have hP : ∀ i, IsStarProjection (m.op i) := h
  have horth : ∀ i j, i ≠ j → m.op i * m.op j = 0 := fun _ _ hij => h.orthogonal hij
  have hsum : ∑ i, m.op i = 1 := h.sum_op_eq_one
  have hρ : ρ.op.IsDensityOp := ρ.isDensity
  have hρ'D : (krausSumₗ m.op ρ.op).IsDensityOp :=
    isDensityOp_krausSumₗ_of_isStarProjection hP hsum hρ
  have hsupp : HasSupportLE ρ.op (krausSumₗ m.op ρ.op) :=
    hasSupportLE_krausSumₗ_of_isStarProjection hP hsum hρ.isPositive
  have hident := quantumRelativeEntropy_krausSumₗ_eq_vonNeumannEntropy_sub hP horth hsum hρ
  have hklein := hρ.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE hρ'D hsupp
  rw [State.vonNeumannEntropy_def (m.unreadState ρ), State.vonNeumannEntropy_def ρ,
    Measurement.unreadState_op]
  constructor
  · intro heq
    have hD0 : ρ.op.quantumRelativeEntropy (krausSumₗ m.op ρ.op) = 0 := by rw [hident]; linarith
    have hopeq := hklein.mp hD0
    apply State.ext
    rw [Measurement.unreadState_op]
    exact hopeq.symm
  · intro heq
    have hopeq : ρ.op = krausSumₗ m.op ρ.op := by rw [← Measurement.unreadState_op, heq]
    have hD0 := hklein.mpr hopeq
    rw [hident] at hD0
    linarith

end AxQM
