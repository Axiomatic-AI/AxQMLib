/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Fidelity
import AxQM.Postulates.API.Mixture
import ToMathlib.Analysis.InnerProductSpace.UhlmannMixture

/-!
# Nielsen & Chuang, Theorem 9.7 (Strong concavity of the fidelity)

Strong concavity of fidelity for state mixtures with probability distributions.

Mixing on *both* sides of the fidelity can only bring the two mixtures closer (raise the fidelity)
than the `√(pᵢ qᵢ)`-weighted average of the componentwise fidelities. N&C call this the **strong
concavity** of the fidelity, in analogy with the strong convexity of the trace distance (Theorem
9.3); it is the master inequality from which the joint concavity of the fidelity (Exercise 9.19) and
concavity in the first argument (Exercise 9.20) follow by specialization.

## Statement

The mixtures are `AxQM.State.mix` (`∑ᵢ pᵢ ρᵢ`, N&C mixtures), and the
distance is the **fidelity** `AxQM.State.fidelity` (`ρ.fidelity σ = F(ρ, σ)`, N&C
`(9.53)`). The result is

* `AxQM.State.sum_sqrt_mul_fidelity_le_fidelity_mix` —
  `∑ᵢ √(pᵢ qᵢ) F(ρᵢ, σᵢ) ≤ F(∑ᵢ pᵢ ρᵢ, ∑ᵢ qᵢ σᵢ)` for probability distributions `p, q` and families
  of states `ρ, σ`.

The weights `√(pᵢ qᵢ)` live entirely on the classical probability side.

## Proof

The statement is one rewrite away from the operator inequality proved in `ToMathlib/` as
`ContinuousLinearMap.traceNorm_cfc_sqrt_mul_cfc_sqrt_sum_ge`:

  `∑ᵢ √(pᵢ qᵢ) ‖√ρᵢ √σᵢ‖₁ ≤ ‖√(∑ᵢ pᵢ ρᵢ) √(∑ᵢ qᵢ σᵢ)‖₁`

for positive operators `ρᵢ, σᵢ` and non-negative weights `pᵢ, qᵢ` (no normalization required — the
probability constraints `∑ pᵢ = ∑ qᵢ = 1` are consumed only by `State.mix` here). That inequality is
N&C's proof (§9.2.2, p. 414): choosing per-component maximizing factorizations with real overlap and
assembling **block-row operators** on an enlarged ancilla realizes the joint overlap
`∑ᵢ √(pᵢ qᵢ) ‖√ρᵢ √σᵢ‖₁` as a single Hilbert–Schmidt pairing, bounded by the general-ancilla Uhlmann
upper bound (Theorem 9.4, generalized). The block-row assembly is the operator counterpart of N&C's
joint purifications `|ψ⟩ ≡ ∑ᵢ √pᵢ |ψᵢ⟩|i⟩`, `|ϕ⟩ ≡ ∑ᵢ √qᵢ |ϕᵢ⟩|i⟩` (`(9.93)`).

Two bridges lift that operator inequality to states:

* **Fidelity as a trace norm.** `State.fidelity_eq_traceNorm` rewrites each `F(ρᵢ, σᵢ)` and the
  mixture fidelity to `‖√· √·‖₁` (N&C `(9.71)`).
* **The mixture's density operator.** `State.mix_op` exposes `(∑ᵢ pᵢ ρᵢ).op = ∑ᵢ (pᵢ : ℂ) • ρᵢ.op`,
  matching the operator lemma's mixed arguments; positivity of each `ρᵢ.op` / `σᵢ.op` is
  `State.isDensity.nonneg`.

N&C Theorem 9.7, p. 414. The operator core is in `ToMathlib/` (phase-aligned Uhlmann
achievement and the block-row assembly).
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Strong concavity of the fidelity** (Nielsen & Chuang, Theorem 9.7, `(9.92)`): for probability
distributions `p, q` over a common finite index set and families of states `ρ, σ`,
`∑ᵢ √(pᵢ qᵢ) F(ρᵢ, σᵢ) ≤ F(∑ᵢ pᵢ ρᵢ, ∑ᵢ qᵢ σᵢ)`.

Mixing on both arguments never decreases the fidelity below the `√(pᵢ qᵢ)`-weighted average of the
componentwise fidelities. The proof rewrites both sides through `State.fidelity_eq_traceNorm` and
`State.mix_op` to the operator inequality
`ContinuousLinearMap.traceNorm_cfc_sqrt_mul_cfc_sqrt_sum_ge` (`ToMathlib/`, the block-row Uhlmann
argument); positivity of each density operator supplies its hypotheses. This is the master
inequality behind the joint concavity of the fidelity (Exercise 9.19) and its concavity in the first
argument (Exercise 9.20). -/
theorem State.sum_sqrt_mul_fidelity_le_fidelity_mix {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) (ρ σ : ι → State S) :
    ∑ i, Real.sqrt (p i * q i) * (ρ i).fidelity (σ i)
      ≤ (State.mix p hp hps ρ).fidelity (State.mix q hq hqs σ) := by
  rw [State.fidelity_eq_traceNorm, State.mix_op, State.mix_op]
  simp_rw [State.fidelity_eq_traceNorm]
  exact ContinuousLinearMap.traceNorm_cfc_sqrt_mul_cfc_sqrt_sum_ge
    (fun i => (ρ i).op) (fun i => (σ i).op)
    (fun i => (ρ i).isDensity.nonneg) (fun i => (σ i).isDensity.nonneg) p q hp hq

end AxQM
