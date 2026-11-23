/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.DistillableEntanglement
import AxQM.Core.EntanglementEntropyMonotone
import AxQM.Core.EntropyTensorPow
import AxQM.NC.Ch11.Theorem11_6

/-!
# Nielsen–Chuang, Exercise 12.23 — the entanglement distillation procedure is optimal

N&C §12.5.2, p. 580: *"Prove that the procedure for entanglement
distillation we have described is optimal."*

## The exercise

Prove the described entanglement distillation procedure is optimal.

N&C's surrounding text (p. 580) states the conclusion as an **equality**: "the entanglement of
formation and entanglement of distillation for the state `|ψ⟩` are the same, and both equal
`S(ρ_ψ)`". The achievability half — that the described procedure *attains* `S(ρ_ψ)` — is the
procedure itself; the exercise asks for the remaining **converse**, that this attained rate is
*optimal* (cannot be beaten). Proving `D(ρ_ψ) ≤ S(ρ_ψ)` is therefore exactly the content the
exercise requests, not a narrowing of it (see the fidelity discussion below).

For a bipartite pure state `|ψ⟩` with reduced state `ρ_ψ`, N&C's §12.5.2 exhibits the **entanglement
distillation** procedure: from `m` copies of `|ψ⟩`, using local operations and classical
communication (LOCC), Alice and Bob produce — with fidelity → 1 — roughly `m · S(ρ_ψ)` Bell states
(measure onto the ε-typical subspace to get `|ϕ'_m⟩ ≈ |ψ⟩^⊗m`, then convert `|ϕ'_m⟩` to Bell states
by Nielsen's theorem, eq. (12.170)). So the distillation rate `S(ρ_ψ)` is **achievable**. The
exercise asks to prove this procedure is **optimal**: *no* LOCC protocol distills copies of `|ψ⟩`
into Bell states at a rate exceeding `S(ρ_ψ)`. Equivalently, the *distillable entanglement*
`D(|ψ⟩) = S(ρ_ψ)` — the achievable rate cannot be beaten.

## What is formalised

The rate framework (`IsDistillationRate`, `distillableEntanglement` and its
well-definedness) is in `AxQM/Core/DistillableEntanglement.lean`. This file adds the
Fannes-dependent **optimality converse**, working at the reduced-state level (where LOCC lives, via
Nielsen's theorem — as in `Exercise12_24`), for a general marginal `ρ : State S`:

* `AxQM.IsDistillationRate.le_vonNeumannEntropy` — **optimality, per rate**: every
  achievable distillation rate satisfies `R ≤ S(ρ)`.
* `AxQM.distillableEntanglement_le_vonNeumannEntropy` — the packaged bound
  `distillableEntanglement ρ ≤ S(ρ)`: no protocol beats `S(ρ)`.
* `AxQM.PureState.distillableEntanglement_reducedLeft_le` — the physics headline for a
  bipartite pure state `ψ`: `distillableEntanglement ρ_ψ ≤ S(ρ_ψ)`.

## Why the converse *is* the exercise (fidelity, units, scope)

* **Optimality = the converse.** The procedure achieving `S(ρ_ψ)` is N&C's own text result; the
  exercise asks precisely that it be *optimal*, i.e. that `S(ρ_ψ)` be an upper bound on every
  achievable rate. That upper bound `distillableEntanglement ρ ≤ S(ρ)` is what is proved. The
  achievability half (that `S(ρ_ψ)` is attained, via the typical-subspace measurement) is not what
  the exercise asks and is out of scope here; nothing is weakened.
* **General LOCC, not merely one-way.** The rate predicate `IsDistillationRate` quantifies over
  `State.LOCCConvertible` — Alice steering her reduced state by a single measurement. This is *not*
  a restriction to one-way protocols: N&C **Proposition 12.14**, formalised as
  `AxQM.OneWayLOCC.of_transforms_pureState`, shows every finite-round *two-way* LOCC
  protocol deterministically transforming a bipartite pure state reduces to exactly this one-way
  form. So the converse bounds *every* LOCC distillation rate, matching N&C's unrestricted "no
  protocol beats `S(ρ_ψ)`".
* **Approximate, not exact.** The statement is asymptotic and approximate (fidelity → 1): the exact
  single-shot converse is degenerate (exact LOCC to a maximally entangled state is governed by the
  min-entropy `H_∞`, not `S`), so a single-shot formulation would be *unfaithful*. Fidelity → 1 is
  expressed as trace distance → 0 (Fuchs–van de Graaf: `1 − F ≤ D ≤ √(1 − F²)`, so the two notions
  of convergence coincide); trace distance is also the natural input to Fannes' inequality.
* **Units.** The rate is measured in **nats** of entanglement per copy (`log K_m / m`), matching the
  library's natural-log `vonNeumannEntropy`, so optimality reads cleanly as `D ≤ S(ρ)`. N&C's "`n`
  Bell states" is the `K_m = 2ⁿ` special case, where `log K_m / m = (n/m)·log 2`; dividing by
  `log 2` recovers N&C's Bell-state rate `n/m ≤ S₂(ρ_ψ)` (`S` in bits).

## Proof of the converse

For an achievable rate `R`, with LOCC outputs `σ_m` trace-converging (`D_m → 0`) to rank-`K_m`
maximally entangled marginals `μ_m`:

* `log K_m = S(μ_m)` (`IsMaxEntMarginal.vonNeumannEntropy_eq`);
* `S(μ_m) ≤ S(σ_m) + |S(σ_m) − S(μ_m)|` and, by **weak Fannes'** inequality on `S^⊗ₘ` (dimension
  `d^m`, `State.abs_vonNeumannEntropy_sub_le_fannes_weak`, unconditional; Theorem 11.6 in
  `AxQM/NC/Ch11/Theorem11_6.lean`),
  `|S(σ_m) − S(μ_m)| ≤ 2·D_m·(m·log d) + e⁻¹`;
* `S(σ_m) ≤ S(ρ^⊗m)` — LOCC cannot increase entanglement entropy
  (`State.LOCCConvertible.vonNeumannEntropy_le`) — and `S(ρ^⊗m) = m·S(ρ)`
  (additivity across copies, `State.vonNeumannEntropy_tensorPow`).

Chaining, `log K_m ≤ m·S(ρ) + 2·D_m·(m·log d) + e⁻¹`; dividing by `m`,
`log K_m / m ≤ S(ρ) + 2·D_m·log d + e⁻¹/m`. The right-hand side → `S(ρ)` (as `D_m → 0` and
`e⁻¹/m → 0`), while the left → `R`, so `R ≤ S(ρ)` by comparison of limits. The growing Fannes
prefactor `m·log d` is exactly cancelled by `D_m → 0` — this is why the *quantitative* Fannes bound
(not mere continuity on a fixed system) is needed for this **sharp** `S(ρ)` bound: `σ_m, μ_m` live
on the growing system `S^⊗ₘ`. (The crude `bddAbove` bound `R ≤ log d` needs no Fannes — see
`AxQM/Core/DistillableEntanglement.lean`.)

## N&C's argument, and why the direct converse is faithful to it

N&C prove optimality (p. 580) by a *reduction to Exercise 12.24* — the number of shared Bell states
cannot be increased by LOCC. Were a distillation protocol to beat `S(ρ_ψ)`, Alice and Bob could
first *dilute* `n = m·S(ρ_ψ)` Bell states into `m` copies of `|ψ⟩` (the described dilution
procedure), then over-distill to `> n` Bell states — an LOCC increase of the Bell count, which is
impossible. That route runs optimality through *both* directions of the interconversion. The
formalisation instead proves the same claim by the **direct information-theoretic converse**:
entanglement entropy is an LOCC monotone (`State.LOCCConvertible.vonNeumannEntropy_le` — the
entropy-level content underlying Exercise 12.24) and additive across copies
(`State.vonNeumannEntropy_tensorPow`), so with Fannes' continuity the extraction rate is pinned
below `S(ρ)` outright, with no appeal to dilution. It is the *same theorem* by a self-contained
route — a faithful reformulation of the proof, never a weakening of the statement.
-/

noncomputable section

open Filter Topology

namespace AxQM

variable {S : QSystem}

/-- **Every achievable distillation rate is at most `S(ρ)`** — the optimality converse (N&C
Exercise 12.23), per rate. If `R` is an achievable distillation rate for `ρ` then `R ≤ S(ρ)`: no
LOCC protocol distills entanglement out of copies of `|ψ⟩` faster than the entanglement entropy
`S(ρ_ψ)`.

The output `σ_m` is trace-close to a rank-`K_m` maximally entangled marginal `μ_m` of entropy
`log K_m`; LOCC monotonicity (`State.LOCCConvertible.vonNeumannEntropy_le`) and additivity across
copies (`State.vonNeumannEntropy_tensorPow`) bound `S(σ_m) ≤ m·S(ρ)`, and weak Fannes'
(`State.abs_vonNeumannEntropy_sub_le_fannes_weak`) controls `|S(σ_m) − log K_m|` up to the vanishing
`2·D_m·(m·log d) + e⁻¹`. Dividing by `m` and passing to the limit gives `R ≤ S(ρ)`. -/
theorem IsDistillationRate.le_vonNeumannEntropy {ρ : State S} {R : ℝ}
    (h : IsDistillationRate ρ R) : R ≤ ρ.vonNeumannEntropy := by
  obtain ⟨K, σ, μ, hLOCC, hμ, hD, hR⟩ := h
  -- The per-block bound `log K_m / m ≤ S(ρ) + 2·D_m·log d + e⁻¹/m` for `m ≥ 1`.
  have key : ∀ m : ℕ, 1 ≤ m →
      Real.log (K m) / m ≤
        ρ.vonNeumannEntropy + 2 * (σ m).traceDistance (μ m) * Real.log S.dim
          + Real.exp (-1) / m := by
    intro m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    -- `S(μ_m) = log K_m`.
    have hSμ : (μ m).vonNeumannEntropy = Real.log (K m) := (hμ m).vonNeumannEntropy_eq
    -- LOCC monotone + additivity: `S(σ_m) ≤ m·S(ρ)`.
    have hmono : (σ m).vonNeumannEntropy ≤ (m : ℝ) * ρ.vonNeumannEntropy := by
      have h1 := (hLOCC m).vonNeumannEntropy_le
      rw [State.vonNeumannEntropy_tensorPow] at h1
      exact h1
    -- Weak Fannes on `S^⊗ₘ` (dimension `d^m`), with `log (d^m) = m · log d`.
    have hdimnat := QSystem.dim_tensorPow S m
    have hfannes := State.abs_vonNeumannEntropy_sub_le_fannes_weak (σ m) (μ m)
    rw [hdimnat, Nat.cast_pow, Real.log_pow] at hfannes
    -- `S(μ_m) − S(σ_m) ≤ 2·D_m·(m·log d) + e⁻¹`.
    have hgap : (μ m).vonNeumannEntropy - (σ m).vonNeumannEntropy ≤
        2 * (σ m).traceDistance (μ m) * ((m : ℝ) * Real.log S.dim) + Real.exp (-1) :=
      calc (μ m).vonNeumannEntropy - (σ m).vonNeumannEntropy
          ≤ |(μ m).vonNeumannEntropy - (σ m).vonNeumannEntropy| := le_abs_self _
        _ = |(σ m).vonNeumannEntropy - (μ m).vonNeumannEntropy| := abs_sub_comm _ _
        _ ≤ _ := hfannes
    -- Assemble `log K_m ≤ m·S(ρ) + 2·D_m·(m·log d) + e⁻¹`, then divide by `m`.
    rw [div_le_iff₀ hmpos]
    have hexpand : (ρ.vonNeumannEntropy + 2 * (σ m).traceDistance (μ m) * Real.log S.dim
          + Real.exp (-1) / m) * m
        = (m : ℝ) * ρ.vonNeumannEntropy
          + 2 * (σ m).traceDistance (μ m) * ((m : ℝ) * Real.log S.dim) + Real.exp (-1) := by
      field_simp
    rw [hexpand, ← hSμ]
    linarith [hgap, hmono]
  -- The right-hand side tends to `S(ρ)`; the left tends to `R`; compare.
  have hftendsto :
      Tendsto (fun m : ℕ => ρ.vonNeumannEntropy + 2 * (σ m).traceDistance (μ m) * Real.log S.dim
        + Real.exp (-1) / m) atTop (𝓝 ρ.vonNeumannEntropy) := by
    have h1 : Tendsto (fun m : ℕ => 2 * (σ m).traceDistance (μ m) * Real.log S.dim)
        atTop (𝓝 0) := by
      simpa using (hD.const_mul (2 : ℝ)).mul_const (Real.log S.dim)
    have h2 : Tendsto (fun m : ℕ => Real.exp (-1) / m) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have := ((tendsto_const_nhds (x := ρ.vonNeumannEntropy)).add h1).add h2
    simpa using this
  refine le_of_tendsto_of_tendsto hR hftendsto ?_
  filter_upwards [eventually_ge_atTop 1] with m hm using key m hm

/-- **Optimality of the entanglement distillation procedure** (Nielsen–Chuang, Exercise 12.23): the
distillable entanglement of `ρ` never exceeds its von Neumann entropy,

`distillableEntanglement ρ ≤ S(ρ)`.

Since the procedure of §12.5.2 attains the rate `S(ρ_ψ)`, this upper bound on *every* achievable
rate says exactly that the procedure is optimal — no LOCC protocol distills more Bell-state
entanglement per copy than `S(ρ_ψ)`. Immediate from the per-rate converse
`IsDistillationRate.le_vonNeumannEntropy` and `S(ρ) ≥ 0`. -/
theorem distillableEntanglement_le_vonNeumannEntropy (ρ : State S) :
    distillableEntanglement ρ ≤ ρ.vonNeumannEntropy :=
  Real.sSup_le (fun _ hR => hR.le_vonNeumannEntropy) ρ.vonNeumannEntropy_nonneg

/-- **Optimality of distillation for a bipartite pure state** (the physics headline of N&C
Exercise 12.23): for a bipartite pure state `|ψ⟩`, the distillable entanglement of its reduced state
`ρ_ψ` is at most the entanglement entropy `S(ρ_ψ)`,

`distillableEntanglement ρ_ψ ≤ S(ρ_ψ)`.

Together with N&C's achievability (§12.5.2, the typical-subspace procedure attains `S(ρ_ψ)`), this
says the described distillation procedure is optimal: the distillable entanglement equals `S(ρ_ψ)`.
The reduced-state form `distillableEntanglement_le_vonNeumannEntropy` instantiated at
`ρ = ψ.toState.reducedLeft`. -/
theorem PureState.distillableEntanglement_reducedLeft_le {T : QSystem}
    (ψ : PureState (S.compose T)) :
    distillableEntanglement ψ.toState.reducedLeft ≤ ψ.toState.reducedLeft.vonNeumannEntropy :=
  distillableEntanglement_le_vonNeumannEntropy _

end AxQM
