/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SchmidtNumber
import AxQM.Postulates.API.SchmidtDecomposition

/-!
# Nielsen & Chuang, Problem 2.2 (Properties of the Schmidt number)

Properties of the Schmidt number: rank of rho^A, subadditivity over decompositions,
Sch(psi)>=|Sch(phi)-Sch(gamma)|.

## Definitions

The **definitions** — the Schmidt number `PureState.schmidtNumber` and the state rank
`State.rank` — are in `AxQM/Postulates/API/SchmidtNumber.lean`. The Schmidt number is defined there
as the number of non-zero singular values of the matricized coefficient operator
`M = matricize ψ.vec` (these singular values are the Schmidt coefficients `λᵢ` of
`|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩`). Defining it that way — rather than as the rank of `ρᴬ` — is what makes
**Part 1** a genuine theorem rather than a definitional tautology (a faithfulness requirement:
defining `Sch(ψ)` as `rank ρᴬ` would silently trivialise the problem).

## Statements

Part 1 is `PureState.schmidtNumber_eq_rank_reducedLeft` below.

**Parts 2 and 3** have hypotheses that are equations between the underlying state vectors — a
product decomposition `ψ.vec = ∑ⱼ αⱼ ⊗ βⱼ` (Part 2) and a superposition
`ψ.vec = α • φ.vec + β • γ.vec` (Part 3). They are in `AxQM/Postulates/API/SchmidtNumber.lean`:

* **Part 2** (number of product terms `≥ Sch(ψ)`) — `PureState.schmidtNumber_le_card_of_sum_tmul`:
  if `ψ.vec = ∑ⱼ∈s αⱼ ⊗ βⱼ` then `Sch(ψ) ≤ s.card`.
* **Part 3** (`Sch(ψ) ≥ |Sch(φ) − Sch(γ)|` for `ψ = αφ + βγ`) —
  `PureState.natAbs_sub_schmidtNumber_le`: if `ψ.vec = α • φ.vec + β • γ.vec` with `α, β ≠ 0`
  then `|Sch(φ) − Sch(γ)| ≤ Sch(ψ)`. The nonzero amplitudes are a genuine correctness
  hypothesis — the inequality is *false* for `α = 0` (`ψ = βγ` with `φ` maximally entangled and `γ`
  a product state) — a faithful reading of N&C's tacit two-term superposition, not a weakening.
-/

open scoped InnerProductSpace

namespace AxQM

variable {S T : QSystem}

/-- **Problem 2.2(1).** The Schmidt number of a bipartite pure state `|ψ⟩` equals the
rank of its left reduced density operator `ρᴬ = tr_B(|ψ⟩⟨ψ|)`.

The number of non-zero Schmidt coefficients (the singular values of the coefficient
operator `M = matricize ψ.vec`, by definition of `schmidtNumber`) equals `rank M`
(`schmidtNumber_eq_finrank_range_matricize`); and `ρᴬ = M Mᵀ` with `rank (M Mᵀ) = rank M`
(`rank_reducedLeft_toState_eq_finrank_range_matricize`). The statement is about
`schmidtNumber`, `reducedLeft`, and `rank`. -/
theorem PureState.schmidtNumber_eq_rank_reducedLeft (ψ : PureState (S ⊗ T)) :
    ψ.schmidtNumber = ψ.toState.reducedLeft.rank :=
  (ψ.schmidtNumber_eq_finrank_range_matricize).trans
    (State.rank_reducedLeft_toState_eq_finrank_range_matricize ψ).symm

/-- **Problem 2.2(1), right-hand mirror.** The Schmidt number of a bipartite pure state `|ψ⟩` also
equals the rank of its *right* reduced density operator `ρᴮ = tr_A(|ψ⟩⟨ψ|)` — both marginals share
the eigenvalues `λᵢ²`, so both have rank `Sch(ψ)`. Co-located with the left version
`schmidtNumber_eq_rank_reducedLeft`; reused by Exercise 2.78's `product ⟺ ρᴮ pure` equivalence.

Proof: from the Schmidt decomposition `|ψ⟩ = ∑ᵢ<ₙ λᵢ |iᴬ⟩|iᴮ⟩` (`exists_schmidt_decomposition`,
positive `λᵢ`, orthonormal Schmidt bases) both marginals diagonalise — `ρᴬ = ∑ᵢ λᵢ² |iᴬ⟩⟨iᴬ|` and
`ρᴮ = ∑ᵢ λᵢ² |iᴮ⟩⟨iᴮ|` (`partialTrace{Right,Left}_rankOne_eq_sum_rankOne_of_schmidt`) — so each has
rank `n` (`InnerProductSpace.finrank_range_sum_smul_rankOne_self`, the `λᵢ² ≠ 0`). With
`Sch(ψ) = rank ρᴬ = n` this gives `Sch(ψ) = rank ρᴮ`. The statement is about
`schmidtNumber`, `reducedRight`, and `rank`. -/
theorem PureState.schmidtNumber_eq_rank_reducedRight (ψ : PureState (S ⊗ T)) :
    ψ.schmidtNumber = ψ.toState.reducedRight.rank := by
  obtain ⟨n, l, a, b, hpos, ha, hb, _, hdecomp⟩ := ψ.exists_schmidt_decomposition
  have hcne : ∀ i, ((l i : ℂ)) ^ 2 ≠ 0 := fun i =>
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt (hpos i)))
  have hR : (ψ.toState.reducedRight.op : T.space →ₗ[ℂ] T.space)
      = ∑ i, ((l i : ℂ)) ^ 2 • (InnerProductSpace.rankOne ℂ (b i) (b i)).toLinearMap := by
    rw [State.reducedRight_op, LinearMap.coe_toContinuousLinearMap, PureState.toState_op]
    exact LinearMap.partialTraceLeft_rankOne_eq_sum_rankOne_of_schmidt
      (stdOrthonormalBasis ℂ S.space) l a b (fun i j _ _ => orthonormal_iff_ite.mp ha i j) hdecomp
  have hL : (ψ.toState.reducedLeft.op : S.space →ₗ[ℂ] S.space)
      = ∑ i, ((l i : ℂ)) ^ 2 • (InnerProductSpace.rankOne ℂ (a i) (a i)).toLinearMap := by
    rw [State.reducedLeft_op, LinearMap.coe_toContinuousLinearMap, PureState.toState_op]
    exact LinearMap.partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt
      (stdOrthonormalBasis ℂ T.space) l a b hb hdecomp
  have hrR : ψ.toState.reducedRight.rank = n := by
    rw [State.rank, hR]; exact InnerProductSpace.finrank_range_sum_smul_rankOne_self b _ hb hcne
  have hrL : ψ.toState.reducedLeft.rank = n := by
    rw [State.rank, hL]; exact InnerProductSpace.finrank_range_sum_smul_rankOne_self a _ ha hcne
  rw [ψ.schmidtNumber_eq_rank_reducedLeft, hrL, hrR]

end AxQM
