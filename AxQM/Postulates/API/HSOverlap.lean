/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Purity

/-!
# AxQM.Postulates.API — Hilbert–Schmidt overlap of two states

The **Hilbert–Schmidt (Frobenius) overlap** `tr(ρ σ)` of two density operators, as a real number.
It measures how far apart two states are: for orthogonally-supported
states it is `0`, and it is bounded by the purities via Cauchy–Schwarz. It is the natural
distinguishability resource behind the "nearly orthogonal reduced states" of the hidden subgroup
problem (Nielsen & Chuang, Problem 5.5).

* `State.hsOverlap ρ σ` — the overlap `re tr(ρ σ)`. The trace of `ρ.op * σ.op` is real when both
  operators are positive (it equals `tr(√ρ σ √ρ)` for the cyclic form), and `hsOverlap` records
  that real trace. Compare `State.purity`, of which it is the diagonal
  (`State.hsOverlap_self`).

`State.hsOverlap_comm` records the symmetry `tr(ρ σ) = tr(σ ρ)` (cyclicity of the trace) and
`State.hsOverlap_self` records the diagonal `hsOverlap ρ ρ = purity ρ`, so `hsOverlap` genuinely
generalises `State.purity`.
-/

noncomputable section

open scoped InnerProductSpace

namespace AxQM

variable {S : QSystem}

/-- The **Hilbert–Schmidt (Frobenius) overlap** `tr(ρ σ)` of two states `ρ σ`, as a real number
(`re tr(ρ.op σ.op)`). It measures the (un-normalised) overlap of the two density operators: it
vanishes exactly when their supports are orthogonal, and by Cauchy–Schwarz
`(tr ρσ)² ≤ tr(ρ²) · tr(σ²)`, so it is controlled by the purities. Its diagonal
`hsOverlap ρ ρ` is the purity `tr(ρ²)` (`State.hsOverlap_self`). -/
def State.hsOverlap (ρ σ : State S) : ℝ :=
  RCLike.re (LinearMap.trace ℂ S ((ρ.op * σ.op : S →L[ℂ] S) : S →ₗ[ℂ] S))

/-- The **self-overlap is the purity**: `hsOverlap ρ ρ = tr(ρ²) = purity ρ`. Holds definitionally,
since `State.purity` is `re tr(ρ.op * ρ.op)` and `hsOverlap ρ ρ` is the same expression. Exhibits
`hsOverlap` as the off-diagonal generalisation of `State.purity`. -/
@[simp]
theorem State.hsOverlap_self (ρ : State S) : ρ.hsOverlap ρ = ρ.purity := rfl

/-- **Symmetry of the Hilbert–Schmidt overlap**: `hsOverlap ρ σ = hsOverlap σ ρ`, from the
cyclicity of the trace `tr(ρ σ) = tr(σ ρ)` (`LinearMap.trace_mul_comm`). -/
theorem State.hsOverlap_comm (ρ σ : State S) : ρ.hsOverlap σ = σ.hsOverlap ρ := by
  unfold State.hsOverlap
  rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul,
      LinearMap.trace_mul_comm]

end AxQM
