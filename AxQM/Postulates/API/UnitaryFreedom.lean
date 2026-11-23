/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Ensemble
import ToMathlib.Analysis.InnerProductSpace.RankOneSum

/-!
# AxQM — unitary freedom in the ensemble

This file contains the machinery behind **Nielsen–Chuang Theorem 2.6** ("unitary freedom
in the ensemble for density matrices"). The theorem answers: *which ensembles give rise to the same
density operator?* Following N&C, it is convenient to absorb the probabilities into the vectors,
working with the **subnormalized vectors** `|ψ̃ᵢ⟩ = √pᵢ |ψᵢ⟩` (eq. between (2.165) and (2.166)); an
ensemble `{pᵢ, |ψᵢ⟩}` then "generates" the density operator `ρ = ∑ᵢ |ψ̃ᵢ⟩⟨ψ̃ᵢ|`, since
`√pᵢ · conj(√pᵢ) = pᵢ`.

The ensemble form of the theorem (N&C eq. (2.167)) is: two ensembles `e`, `f` **of the same size**
(the "padded" form — pad the smaller ensemble with probability-zero entries) generate the same
density operator iff their subnormalized vectors are related by a unitary matrix,
`√pᵢ|ψᵢ⟩ = ∑ⱼ uᵢⱼ √qⱼ|φⱼ⟩`.

## Main definitions

* `AxQM.Ensemble.tildeVec` — the subnormalized vectors `√pᵢ • |ψᵢ⟩` of an ensemble.
* `AxQM.Ensemble.UnitarilyRelated` — the relation "same size, and the subnormalized
  vectors are related by a unitary coefficient matrix" (N&C eq. (2.167)).

## Main results

* `Ensemble.toState_op_eq_sum_rankOne_tildeVec` — the **bridge**: an ensemble's density operator is
  the sum of the rank-one projectors of its subnormalized vectors, `ρ = ∑ᵢ |ψ̃ᵢ⟩⟨ψ̃ᵢ|`.
* `Ensemble.toState_op_eq_iff_unitarilyRelated` — Theorem 2.6, operator form over ensembles: two
  equal-size ensembles have equal density operators iff they are `UnitarilyRelated`.

The statement of Theorem 2.6, `Ensemble.toState_eq_iff_unitarilyRelated`, for ensembles and
states, is in `AxQM/NC/Ch2/Theorem2_6.lean`.

The mathematical core — the vector-family biconditional
`InnerProductSpace.sum_rankOne_self_eq_iff_exists_mem_unitaryGroup` — lives in
`ToMathlib/Analysis/InnerProductSpace/RankOneSum.lean`.
-/

open scoped InnerProductSpace
open InnerProductSpace Finset

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Ensemble

/-- The **subnormalized vectors** `|ψ̃ᵢ⟩ = √pᵢ |ψᵢ⟩` of an ensemble `{pᵢ, |ψᵢ⟩}` (Nielsen–Chuang,
between eqs. (2.165) and (2.166)): the pure-state vectors scaled by the square roots of their
probabilities. The ensemble's density operator `ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` is exactly the sum of the
rank-one projectors of these vectors, `∑ᵢ |ψ̃ᵢ⟩⟨ψ̃ᵢ|` (`toState_op_eq_sum_rankOne_tildeVec`),
because `√pᵢ · conj(√pᵢ) = pᵢ`. -/
def tildeVec (e : Ensemble S) (i : Fin e.card) : S.space :=
  (Real.sqrt (e.prob i) : ℂ) • (e.states i).vec

/-- **The density operator of an ensemble is the sum of rank-one projectors of its subnormalized
vectors**: `ρ = ∑ᵢ |ψ̃ᵢ⟩⟨ψ̃ᵢ|` with `|ψ̃ᵢ⟩ = √pᵢ |ψᵢ⟩`. This is the bridge from the
probability-weighted form `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` (`Ensemble.toState_op`) to the subnormalized-vector form
used by Nielsen–Chuang Theorem 2.6, using `rankOne (√pᵢ • v) (√pᵢ • v) = (√pᵢ · conj √pᵢ) • rankOne
v v = pᵢ • rankOne v v` (`InnerProductSpace.rankOne_smul_smul_self`, `Real.mul_self_sqrt`). -/
theorem toState_op_eq_sum_rankOne_tildeVec (e : Ensemble S) :
    e.toState.op = ∑ i, rankOne ℂ (e.tildeVec i) (e.tildeVec i) := by
  rw [toState_op]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tildeVec, rankOne_smul_smul_self, ← PureState.toState_op]
  congr 1
  rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (e.prob_nonneg i)]

/-- **Unitary freedom relation** on ensembles (Nielsen–Chuang Theorem 2.6, eq. (2.167)): two
ensembles `e`, `f` are unitarily related when they have the **same size** (`e.card = f.card` — the
"padded" form: pad the smaller ensemble with probability-zero entries) and their subnormalized
vectors are related by a unitary coefficient matrix `u`, `√pᵢ|ψᵢ⟩ = ∑ⱼ uᵢⱼ √qⱼ|φⱼ⟩`. -/
def UnitarilyRelated (e f : Ensemble S) : Prop :=
  ∃ (h : e.card = f.card) (u : Matrix (Fin e.card) (Fin e.card) ℂ),
    u ∈ Matrix.unitaryGroup (Fin e.card) ℂ ∧
      ∀ i, e.tildeVec i = ∑ j, u i j • f.tildeVec (Fin.cast h j)

/-- **Nielsen–Chuang Theorem 2.6, operator form over ensembles** (eq. (2.167)). Two ensembles `e`,
`f` of the same size (`e.card = f.card`, the padded form) have equal density operators
`e.toState.op = f.toState.op` **iff** they are `UnitarilyRelated`: their subnormalized vectors
`√pᵢ|ψᵢ⟩` are related by a unitary coefficient matrix.

Via the bridge `toState_op_eq_sum_rankOne_tildeVec`, both density operators are sums of rank-one
projectors of subnormalized vectors; reindexing `f`'s sum along `Fin.cast` onto the common index
`Fin e.card`, the vector-family biconditional
`InnerProductSpace.sum_rankOne_self_eq_iff_exists_mem_unitaryGroup` gives exactly the unitary
coefficient matrix. -/
theorem toState_op_eq_iff_unitarilyRelated {e f : Ensemble S} (hcard : e.card = f.card) :
    e.toState.op = f.toState.op ↔ e.UnitarilyRelated f := by
  have : CompleteSpace S.space := FiniteDimensional.completeSpace ℂ S.space
  have hf : f.toState.op
      = ∑ i : Fin e.card,
          rankOne ℂ (f.tildeVec (Fin.cast hcard i)) (f.tildeVec (Fin.cast hcard i)) := by
    rw [toState_op_eq_sum_rankOne_tildeVec]
    exact (Equiv.sum_comp (finCongr hcard)
      (fun j => rankOne ℂ (f.tildeVec j) (f.tildeVec j))).symm
  rw [toState_op_eq_sum_rankOne_tildeVec e, hf,
    sum_rankOne_self_eq_iff_exists_mem_unitaryGroup]
  constructor
  · rintro ⟨u, hu, hrel⟩
    exact ⟨hcard, u, hu, hrel⟩
  · rintro ⟨_, u, hu, hrel⟩
    exact ⟨u, hu, hrel⟩

end Ensemble

end AxQM
