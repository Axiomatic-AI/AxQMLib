/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SchmidtNumber

/-!
# Nielsen & Chuang, Exercise 2.76 (Schmidt decomposition for unequal dimensions)

Extend the Schmidt decomposition proof to unequal-dimension A and B.

## What the exercise adds

N&C prove Theorem 2.7 — `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩` — for the equal-dimension case: the coefficient
array `a` (with `|ψ⟩ = ∑ⱼₖ aⱼₖ |j⟩|k⟩`) is then a *square* matrix and its singular value
decomposition `a = u d v` uses square unitaries `u`, `v`. Exercise 2.76 asks to redo the proof
when `dim A ≠ dim B`, where `a` is *rectangular*. The distinctive fact the rectangular case
exposes is that the number of Schmidt terms — the number of nonzero singular values of `a` — is
bounded by the *smaller* of the two dimensions: a rectangular matrix has rank `≤ min(#rows, #cols)`,
so the Schmidt number is `≤ min(dim A, dim B)`.

The **existence** of the decomposition for arbitrary — hence possibly unequal — dimensions is
already `AxQM.PureState.exists_schmidt_decomposition` (Theorem 2.7, proved uniformly via
the SVD of the matricized coefficient operator, for any dimensions of `A` and `B`), so nothing more
is needed for existence. The distinctive **unequal-dimension content** — the term bound — is
formalised in two complementary forms:

* `AxQM.PureState.schmidtNumber_le_dim` (below) — the Schmidt number is at most
  `min S.dim T.dim`, stated with `schmidtNumber` and `dim` (both `ℕ`-valued).
* `AxQM.PureState.exists_schmidt_decomposition_card_le`
  (`AxQM/Postulates/API/SchmidtDecomposition.lean`) — the full
  decomposition `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩` *together with* the bound `n ≤ min S.dim T.dim` on the
  number of Schmidt terms, in terms of the state vector `ψ.vec` and `⊗ₜ`.

Both are strict strengthenings of the equal-dimension Theorem 2.7, not weakenings: the bound is
proved for arbitrary dimensions and adds information rather than assuming `dim A = dim B`.

Compare `schmidtNumber_eq_rank_reducedLeft` in Problem 2.2 (`AxQM/NC/Ch2/Problem2_2.lean`).

The statement `schmidtNumber_le_dim` is in this file.
-/

open scoped InnerProductSpace

namespace AxQM

variable {S T : QSystem}

/-- **Schmidt number bound for unequal subsystem dimensions (Nielsen–Chuang Exercise 2.76).**
The Schmidt number of a bipartite pure state `|ψ⟩` — the number of nonzero Schmidt coefficients in
`|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩` — is at most the smaller of the two subsystem dimensions,
`Sch(ψ) ≤ min(dim A, dim B)`.

This is the content of Exercise 2.76: extending the Schmidt decomposition to `dim A ≠ dim B` makes
the coefficient operator `M = matricize ψ.vec : B → A` *rectangular*, and the Schmidt number is
`rank M`, which is at most both the domain and codomain dimensions, hence `≤ min(dim A, dim B)`.
Proved from `Sch(ψ) = rank M` (`schmidtNumber_eq_finrank_range_matricize`) together with
`rank M ≤ dim A` (its range is a subspace of `A`, `Submodule.finrank_le`) and `rank M ≤ dim B`
(a range has dimension at most that of the domain, `LinearMap.finrank_range_le`). -/
theorem PureState.schmidtNumber_le_dim (ψ : PureState (S ⊗ T)) :
    ψ.schmidtNumber ≤ min S.dim T.dim := by
  rw [ψ.schmidtNumber_eq_finrank_range_matricize]
  exact le_min (Submodule.finrank_le _) (LinearMap.finrank_range_le _)

end AxQM
