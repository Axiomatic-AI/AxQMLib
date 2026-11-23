/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MaxEntMarginal
import AxQM.Postulates.API.Entropy
import AxQM.Postulates.API.TensorPowState
import AxQM.Postulates.API.TensorPowDim
import AxQM.Postulates.API.StateMajorization
import AxQM.Postulates.API.TraceDistance

/-!
# AxQM — the asymptotic entanglement-distillation rate framework

The framework behind **entanglement distillation** (N&C §12.5.2): the achievable-rate
predicate `IsDistillationRate` and the operational `distillableEntanglement := sSup` of achievable
rates, with their well-definedness (`bddAbove`, `nonneg`, the maximisation property). This mirrors
the `productStateCapacity` definitions in `AxQM/Core/ProductStateCapacity.lean` (a `sSup` of
achievable rates with its own `bddAbove`/`nonneg`/`le_*`).

For a bipartite pure state `|ψ⟩`, `distillableEntanglement ρ_ψ` (`ρ_ψ` its reduced state) is the
operational amount of entanglement, in nats, extractable from copies of `|ψ⟩` as Bell states by
LOCC. The **optimality** upper bound `distillableEntanglement ρ ≤ S(ρ)` — the content of N&C
Exercise 12.23 — needs Fannes' inequality and is the subject of
`AxQM/NC/Ch12/Exercise12_23.lean`; here we prove only the crude, Fannes-free
well-definedness.

## Well-definedness (Fannes-free)

`bddAbove_isDistillationRate` bounds every achievable rate by `log (dim S)` **without** Fannes:
each target `μ_m` is a rank-`K_m` maximally entangled marginal with `S(μ_m) = log K_m`, and the
maximum-entropy bound `State.vonNeumannEntropy_le_log_finrank` gives
`log K_m = S(μ_m) ≤ log (finrank ℂ (S^⊗ₘ).space) = m · log (dim S)`, so `log K_m / m ≤ log (dim S)`
and hence `R ≤ log (dim S)` in the limit. This crude dimensional bound is all `sSup` needs; the
sharp bound `R ≤ S(ρ)` (the optimality converse) is proved separately with Fannes.
-/

noncomputable section

open Filter Topology

namespace AxQM

variable {S : QSystem}

/-- **An achievable entanglement-distillation rate** (N&C §12.5.2). A real `R` (in *nats* of
entanglement per copy) is achievable for the marginal `ρ` if there is a family of LOCC protocols
that, from `ρ^⊗m` (Alice's marginal of `m` copies of `|ψ⟩`), produce outputs `σ_m` converging in
trace distance (fidelity → 1) to genuine rank-`K_m` maximally entangled marginals `μ_m`, with the
extraction rate `log (K_m) / m → R`.

The `μ_m` pin the target to *actual* `K_m`-dimensional maximal entanglement (`IsMaxEntMarginal`), so
this captures LOCC extraction of Bell-type resources, not merely production of a high-entropy state.
For `K_m = 2ⁿ` the target is `n` Bell pairs. -/
def IsDistillationRate (ρ : State S) (R : ℝ) : Prop :=
  ∃ (K : ℕ → ℕ) (σ μ : (m : ℕ) → State (S.tensorPow m)),
    (∀ m, (ρ.tensorPow m).LOCCConvertible (σ m)) ∧
    (∀ m, (μ m).IsMaxEntMarginal (K m)) ∧
    Tendsto (fun m => (σ m).traceDistance (μ m)) atTop (𝓝 0) ∧
    Tendsto (fun m => Real.log (K m) / m) atTop (𝓝 R)

/-- **The distillable entanglement** `D(ρ)` (N&C §12.5.2): the supremum of all achievable
distillation rates. Mirrors `productStateCapacity` (a `sSup` of achievable rates). For the marginal
`ρ_ψ` of a bipartite pure state `|ψ⟩`, `D(ρ_ψ)` is the operational amount of entanglement (in nats)
extractable from `|ψ⟩` as Bell states by LOCC. -/
def distillableEntanglement (ρ : State S) : ℝ :=
  sSup {R | IsDistillationRate ρ R}

/-- Achievable distillation rates are non-negative: `log K_m / m ≥ 0` for every `m` (`K_m : ℕ`, so
`log K_m ≥ 0`), hence so is the limit `R`. -/
theorem isDistillationRate_nonneg {ρ : State S} {R : ℝ} (h : IsDistillationRate ρ R) : 0 ≤ R := by
  obtain ⟨K, _, _, _, _, _, hR⟩ := h
  refine le_of_tendsto_of_tendsto tendsto_const_nhds hR ?_
  filter_upwards with m
  exact div_nonneg (Real.log_natCast_nonneg (K m)) (Nat.cast_nonneg m)

/-- **The set of achievable distillation rates is bounded above** (by `log (dim S)`), so
`distillableEntanglement ρ` is a genuine supremum. Proved **without** Fannes: for `m ≥ 1`, the
rank-`K_m` maximally entangled target `μ_m` has `log K_m = S(μ_m)`, and the maximum-entropy bound
`State.vonNeumannEntropy_le_log_finrank` gives `S(μ_m) ≤ log (finrank ℂ (S^⊗ₘ).space) =
m · log (dim S)`, whence `log K_m / m ≤ log (dim S)` and, in the limit, `R ≤ log (dim S)`. -/
theorem bddAbove_isDistillationRate (ρ : State S) : BddAbove {R | IsDistillationRate ρ R} := by
  refine ⟨Real.log S.dim, ?_⟩
  rintro R ⟨K, _, μ, -, hμ, -, hR⟩
  refine le_of_tendsto_of_tendsto hR tendsto_const_nhds ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hSμ : (μ m).vonNeumannEntropy = Real.log (K m) := (hμ m).vonNeumannEntropy_eq
  -- `S(μ_m) ≤ log (finrank (S^⊗ₘ).space) = m · log (dim S)`.
  have hfin : Module.finrank ℂ (S.tensorPow m).space = S.dim ^ m := QSystem.dim_tensorPow S m
  have hle : (μ m).vonNeumannEntropy ≤ (m : ℝ) * Real.log S.dim := by
    have h := (μ m).vonNeumannEntropy_le_log_finrank
    rw [hfin, Nat.cast_pow, Real.log_pow] at h
    exact h
  rw [div_le_iff₀ hmpos, ← hSμ]
  calc (μ m).vonNeumannEntropy ≤ (m : ℝ) * Real.log S.dim := hle
    _ = Real.log S.dim * m := by ring

/-- The maximisation property: an achievable distillation rate is `≤ distillableEntanglement ρ`. -/
theorem le_distillableEntanglement {ρ : State S} {R : ℝ} (h : IsDistillationRate ρ R) :
    R ≤ distillableEntanglement ρ :=
  le_csSup (bddAbove_isDistillationRate ρ) h

/-- The distillable entanglement is non-negative. -/
theorem distillableEntanglement_nonneg (ρ : State S) : 0 ≤ distillableEntanglement ρ :=
  Real.sSup_nonneg fun _ hR => isDistillationRate_nonneg hR

end AxQM
