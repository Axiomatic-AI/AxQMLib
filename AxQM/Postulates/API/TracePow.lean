/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Purity

/-!
# AxQM.Postulates.API — the trace power `tr(ρᵏ)`

The **`k`-th trace power** `tr(ρᵏ)` of a state, the derived quantity in which Nielsen & Chuang
Exercise 8.18 (`tr(ρᵏ)` is never increased by the depolarizing channel) is stated. It generalizes
the **purity** `tr(ρ²)` (`State.purity`, the `k = 2` case, `Postulates/API/Purity.lean`).

* `State.traceOfPow ρ k` — the real number `tr(ρᵏ) = re tr(ρ.op ^ k)`.
* `State.purity_eq_traceOfPow_two` — the lemma **realizing** the generalization:
  `ρ.purity = ρ.traceOfPow 2` (so `tr(ρ²)` is literally the `k = 2` trace power, and any result
  about `traceOfPow` specializes to the purity at `k = 2`).

## Design notes

`traceOfPow` has the same `re (trace …)` shape as `State.purity` with the square `ρ.op * ρ.op`
replaced by the `k`-th power `ρ.op ^ k`. Recording `purity = traceOfPow 2` in code (rather than only
in prose) makes "the `k = 2` case is the purity" a theorem, not a comment.
-/

noncomputable section

open scoped InnerProductSpace

namespace AxQM

variable {S : QSystem}

/-- The **`k`-th trace power** `tr(ρᵏ)` of a state `ρ`, as a real number `re tr(ρ.op ^ k)`. Since
`ρ` is a positive operator, `ρ ^ k` is positive and its trace is real. Generalizes `State.purity`,
the `k = 2` case `tr(ρ²)` (see `State.purity_eq_traceOfPow_two`). The quantity in
which Nielsen & Chuang Exercise 8.18 — the non-increase of `tr(ρᵏ)` under the depolarizing channel —
is stated. -/
def State.traceOfPow (ρ : State S) (k : ℕ) : ℝ :=
  RCLike.re (LinearMap.trace ℂ S.space ((ρ.op ^ k : S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space))

/-- **The purity is the `k = 2` trace power:** `ρ.purity = ρ.traceOfPow 2`. This makes precise that
`State.traceOfPow` generalizes `State.purity` (`tr(ρ²) = tr(ρ^2)`, since `ρ.op * ρ.op = ρ.op ^ 2`),
so the trace-power monotonicity of Exercise 8.18 specializes at `k = 2` to a purity non-increase. -/
theorem State.purity_eq_traceOfPow_two (ρ : State S) : ρ.purity = ρ.traceOfPow 2 := by
  simp only [State.purity, State.traceOfPow, pow_two]

end AxQM
