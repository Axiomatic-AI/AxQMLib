/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.StateMajorization
import AxQM.Postulates.API.ReducedEigenEnsemble

/-!
# AxQM — rank monotonicity under majorization of quantum states

Majorization of density operators (`State.Majorize`, N&C's `ρ ≺ σ`) compares the eigenvalue
*distributions*: a majorized `ρ` is more spread out than `σ`. Consequently `ρ` has at least as many
non-zero eigenvalues as `σ`, i.e. at least as large a rank. This file records that single fact,

`AxQM.State.rank_le_of_majorize : ρ.Majorize σ → σ.rank ≤ ρ.rank`,

the spectral fact that turns Nielsen's theorem (N&C Theorem 12.15, whose forward direction
`State.LOCCConvertible.majorize` yields `ρ ≺ σ`) into the LOCC-monotonicity of the Schmidt number
(N&C Exercise 12.24): the reduced-state rank *is* the Schmidt number
(`PureState.schmidtNumber_eq_rank_reducedLeft`).

## Proof

`State.rank` is the number of non-zero eigenvalues (`rank_eq_card_eigenvalues_ne_zero`), and
`ρ.eigenvalueDist` is exactly that eigenvalue vector, non-negative and summing to one. The purely
combinatorial content — a nonnegative vector majorized by another has at least as large a support —
is `Majorize.card_filter_ne_zero_le` (`ToMathlib.Analysis.Convex.Majorization`); here we specialise
it
to the eigenvalue distributions and re-read both cardinalities as ranks.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace State

/-- **Majorization does not increase the rank of a density operator.** If `ρ` is majorized by `σ`
(`ρ ≺ σ`, i.e. `ρ` is more spread out spectrally), then `σ.rank ≤ ρ.rank`: the more concentrated
state has no more non-zero eigenvalues. This is the spectral core of the LOCC-monotonicity of the
Schmidt number (N&C Exercise 12.24), obtained from the vector fact
`Majorize.card_filter_ne_zero_le` applied to the eigenvalue distributions, since `State.rank` counts
the non-zero eigenvalues (`rank_eq_card_eigenvalues_ne_zero`). -/
theorem rank_le_of_majorize {ρ σ : State S} (h : ρ.Majorize σ) : σ.rank ≤ ρ.rank := by
  rw [rank_eq_card_eigenvalues_ne_zero σ, rank_eq_card_eigenvalues_ne_zero ρ]
  exact Majorize.card_filter_ne_zero_le h σ.eigenvalueDist_nonneg

end State

end AxQM
