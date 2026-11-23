/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Ensemble
import AxQM.Postulates.API.Support
import ToMathlib.Analysis.InnerProductSpace.RankOneSum

/-!
# AxQM — the reduced eigenensemble of a density operator

Nielsen & Chuang, Exercise 2.73, call an ensemble `{pᵢ, |ψᵢ⟩}` **minimal** for `ρ` when it has
exactly `rank ρ` elements. The eigenensemble `Ensemble.ofState ρ` (spectral decomposition) has
`finrank ℂ S.space` elements — one per basis vector — which is *not* minimal once `ρ` has a kernel
(zero eigenvalues). This file trims it to its **reduced eigenensemble**: the spectral decomposition
restricted to the non-zero eigenvalues,
`ρ = ∑ⱼ μⱼ |gⱼ⟩⟨gⱼ|` (sum over `μⱼ ≠ 0`),
a genuine minimal ensemble (size `rank ρ`, strictly positive weights, orthonormal states, generating
`ρ`). It is the canonical witness that a minimal ensemble exists, and the fixed reference ensemble
against which any *other* minimal ensemble is compared (via Theorem 2.6) in the rest of Exercise
2.73 — both the existence of a minimal ensemble through a prescribed support vector and the
probability formula `pᵢ = 1/⟨ψᵢ|ρ⁻¹|ψᵢ⟩`.

The construction reindexes the non-zero-eigenvalue indices onto `Fin (rank ρ)`. The count of
non-zero eigenvalues is exactly the rank: for the self-adjoint `ρ`, the zero-eigenspace is the
kernel (`Module.End.eigenspace_zero`), whose dimension counts the zero eigenvalues
(`card_filter_eigenvalues_eq`), and rank-nullity turns "space minus kernel" into
"non-zero eigenvalue count" (`rank_eq_card_eigenvalues_ne_zero`). The resulting bijection
`eigenIndexEquiv : Fin (rank ρ) ≃ {i // μᵢ ≠ 0}` selects the non-zero
spectrum.

## Main definitions

* `AxQM.State.eigenIndexEquiv` — a bijection `Fin (rank ρ) ≃ {i // μᵢ ≠ 0}` selecting the
  non-zero-eigenvalue indices.
* `AxQM.State.reducedEigenEnsemble` — the reduced eigenensemble `{μⱼ, |gⱼ⟩}` (`μⱼ ≠ 0`).

## Main results

* `State.rank_eq_card_eigenvalues_ne_zero` — the rank is the number of non-zero eigenvalues.
* `State.reducedEigenEnsemble_card` — the reduced eigenensemble has `rank ρ` elements
  (definitional).
* `State.reducedEigenEnsemble_prob_pos` — every weight `μⱼ` is strictly positive.
* `State.reducedEigenEnsemble_states_mem_support` — every state `|gⱼ⟩` lies in the support of `ρ`.
* `State.reducedEigenEnsemble_toState` — the reduced eigenensemble generates `ρ`.
-/

open scoped InnerProductSpace
open InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace State

/-- **The rank of `ρ` is the number of its non-zero eigenvalues.** For the self-adjoint density
operator `ρ`, the zero-eigenspace is the kernel (`Module.End.eigenspace_zero`), so the number of
*zero* eigenvalues is `finrank (ker ρ)` (`card_filter_eigenvalues_eq` at `μ = 0`); rank-nullity
(`finrank (range ρ) + finrank (ker ρ) = finrank S.space`) then equates `rank ρ = finrank (range ρ)`
with the number of *non-zero* eigenvalues. The cardinality identity underlying the reindexing
`eigenIndexEquiv` used to build the reduced eigenensemble. -/
theorem rank_eq_card_eigenvalues_ne_zero (ρ : State S) :
    ρ.rank =
      (Finset.univ.filter
        (fun i : Fin (Module.finrank ℂ S.space) =>
          ρ.isDensity.isSymmetric.eigenvalues rfl i ≠ 0)).card := by
  classical
  -- rank-nullity for `ρ.op`
  have hrn := LinearMap.finrank_range_add_finrank_ker (ρ.op : S.space →ₗ[ℂ] S.space)
  -- the number of zero eigenvalues is `finrank (ker ρ)`: the zero-eigenspace is the kernel
  have hzero : (Finset.univ.filter
        (fun i => ρ.isDensity.isSymmetric.eigenvalues rfl i = 0)).card
      = Module.finrank ℂ (LinearMap.ker (ρ.op : S.space →ₗ[ℂ] S.space)) := by
    rw [← Module.End.eigenspace_zero, ← ρ.isDensity.isSymmetric.card_filter_eigenvalues_eq rfl 0]
    exact congrArg Finset.card (Finset.filter_congr fun i _ => by rw [RCLike.ofReal_eq_zero])
  -- split `univ` into zero / non-zero eigenvalue indices
  have hsplit : (Finset.univ.filter
        (fun i => ρ.isDensity.isSymmetric.eigenvalues rfl i ≠ 0)).card
      + (Finset.univ.filter (fun i => ρ.isDensity.isSymmetric.eigenvalues rfl i = 0)).card
      = Module.finrank ℂ S.space := by
    simp only [ne_eq]
    rw [add_comm, Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset _))
      (fun i => ρ.isDensity.isSymmetric.eigenvalues rfl i = 0)]
    simp
  -- `rank = finrank range`, so `rank + #zero = finrank range + finrank ker = finrank space`
  have hrank : ρ.rank = Module.finrank ℂ (LinearMap.range (ρ.op : S.space →ₗ[ℂ] S.space)) := rfl
  omega

/-- **The bijection selecting the non-zero-eigenvalue indices.** A chosen equivalence
`Fin (rank ρ) ≃ {i // μᵢ ≠ 0}` between `Fin (rank ρ)` and the indices of the non-zero eigenvalues,
available because the two are equinumerous (`rank_eq_card_eigenvalues_ne_zero`). Used to reindex the
non-zero spectrum onto `Fin (rank ρ)` when building the reduced eigenensemble. -/
def eigenIndexEquiv (ρ : State S) :
    Fin ρ.rank ≃
      {i : Fin (Module.finrank ℂ S.space) // ρ.isDensity.isSymmetric.eigenvalues rfl i ≠ 0} :=
  (Fintype.equivFinOfCardEq (by
    classical
    rw [Fintype.card_subtype]
    exact (rank_eq_card_eigenvalues_ne_zero ρ).symm)).symm

/-- **The eigenvalue selected by `eigenIndexEquiv` is non-zero.** By construction the reindexing
lands on non-zero-eigenvalue indices. -/
theorem eigenvalues_eigenIndexEquiv_ne_zero (ρ : State S) (i : Fin ρ.rank) :
    ρ.isDensity.isSymmetric.eigenvalues rfl (ρ.eigenIndexEquiv i).val ≠ 0 :=
  (ρ.eigenIndexEquiv i).2

/-- **Reindexing a spectral sum onto `Fin (rank ρ)`.** If `f` vanishes at every zero-eigenvalue
index, then summing `f` over the non-zero-eigenvalue indices (reindexed by `eigenIndexEquiv`) equals
summing `f` over the whole spectrum — the zero-eigenvalue terms contribute nothing. The shared
mechanism behind `reducedEigenEnsemble`'s `sum_prob` (weights) and `reducedEigenEnsemble_toState`
(operator). -/
theorem sum_eigenIndexEquiv {M : Type*} [AddCommMonoid M] (ρ : State S)
    (f : Fin (Module.finrank ℂ S.space) → M)
    (hf : ∀ i, ρ.isDensity.isSymmetric.eigenvalues rfl i = 0 → f i = 0) :
    ∑ i, f (ρ.eigenIndexEquiv i).val = ∑ i, f i := by
  classical
  rw [Equiv.sum_comp ρ.eigenIndexEquiv (fun x => f x.val),
    ← Finset.sum_subtype (Finset.univ.filter
      (fun i => ρ.isDensity.isSymmetric.eigenvalues rfl i ≠ 0))
      (fun i => by simp) f]
  exact Finset.sum_filter_of_ne fun x _ hfx h0 => hfx (hf x h0)

/-- **The reduced eigenensemble of `ρ`** (Nielsen–Chuang Exercise 2.73): the spectral decomposition
of `ρ` restricted to its non-zero eigenvalues, `{μⱼ, |gⱼ⟩}` over `μⱼ ≠ 0`. Its size is `rank ρ`
(one element per non-zero eigenvalue, via `eigenIndexEquiv`); the weights are the non-zero
eigenvalues `μⱼ > 0` and the states the corresponding orthonormal eigenvectors `|gⱼ⟩`. A minimal
ensemble for `ρ` (`reducedEigenEnsemble_card` / `reducedEigenEnsemble_toState`), and the canonical
reference against which any other minimal ensemble is compared via Theorem 2.6. -/
def reducedEigenEnsemble (ρ : State S) : Ensemble S where
  card := ρ.rank
  prob i := ρ.isDensity.isSymmetric.eigenvalues rfl (ρ.eigenIndexEquiv i).val
  states i :=
    ⟨ρ.isDensity.isSymmetric.eigenvectorBasis rfl (ρ.eigenIndexEquiv i).val,
      (ρ.isDensity.isSymmetric.eigenvectorBasis rfl).orthonormal.norm_eq_one _⟩
  prob_nonneg i := ρ.isDensity.eigenvalues_nonneg rfl _
  sum_prob := by
    rw [ρ.sum_eigenIndexEquiv (ρ.isDensity.isSymmetric.eigenvalues rfl) fun i hi => hi]
    exact ρ.isDensity.eigenvalues_sum_eq_one rfl

/-- **The reduced eigenensemble has `rank ρ` elements** — it is minimal (definitional). -/
@[simp]
theorem reducedEigenEnsemble_card (ρ : State S) : ρ.reducedEigenEnsemble.card = ρ.rank := rfl

/-- **The weights of the reduced eigenensemble are strictly positive.** Each weight is a non-zero
eigenvalue of the (positive) density operator `ρ`, hence `> 0`. -/
theorem reducedEigenEnsemble_prob_pos (ρ : State S) (i : Fin ρ.rank) :
    0 < ρ.reducedEigenEnsemble.prob i :=
  lt_of_le_of_ne (ρ.isDensity.eigenvalues_nonneg rfl _)
    (Ne.symm (ρ.eigenvalues_eigenIndexEquiv_ne_zero i))

/-- **The states of the reduced eigenensemble lie in the support of `ρ`.** Each is an eigenvector of
`ρ` with non-zero eigenvalue, so it lies in the support (`eigenvectorBasis_mem_support_iff`). -/
theorem reducedEigenEnsemble_states_mem_support (ρ : State S) (i : Fin ρ.rank) :
    (ρ.reducedEigenEnsemble.states i).vec ∈ ρ.support :=
  (ρ.eigenvectorBasis_mem_support_iff _).mpr (ρ.eigenvalues_eigenIndexEquiv_ne_zero i)

/-- **The reduced eigenensemble generates `ρ`** (Nielsen–Chuang Exercise 2.73): its density operator
`∑ⱼ μⱼ |gⱼ⟩⟨gⱼ|` (over `μⱼ ≠ 0`) is `ρ`. Reindexing the reduced sum back onto the full spectrum
(`sum_eigenIndexEquiv`, the zero-eigenvalue terms vanishing) turns it into the full spectral
decomposition, which is `ρ` via the eigenensemble (`Ensemble.ofState_toState`). Together with
`reducedEigenEnsemble_card` this exhibits the reduced eigenensemble as a *minimal* ensemble for
`ρ`. -/
theorem reducedEigenEnsemble_toState (ρ : State S) : ρ.reducedEigenEnsemble.toState = ρ := by
  refine State.ext ?_
  -- both the reduced and the full eigenensemble generate the same operator (the full spectral sum)
  have key : ρ.reducedEigenEnsemble.toState.op = (Ensemble.ofState ρ).toState.op := by
    rw [Ensemble.toState_op, Ensemble.toState_op]
    simp only [reducedEigenEnsemble, Ensemble.ofState, PureState.toState_op]
    exact ρ.sum_eigenIndexEquiv (fun k => (ρ.isDensity.isSymmetric.eigenvalues rfl k : ℂ) •
      InnerProductSpace.rankOne ℂ (ρ.isDensity.isSymmetric.eigenvectorBasis rfl k)
        (ρ.isDensity.isSymmetric.eigenvectorBasis rfl k)) fun k hk => by simp [hk]
  rw [key, Ensemble.ofState_toState]
end State

end AxQM
