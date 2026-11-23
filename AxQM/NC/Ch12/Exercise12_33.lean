/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CommutingObservables
import AxQM.Postulates.API.Eigenstate
import AxQM.Postulates.API.ProjectiveMeasurement
import AxQM.Postulates.Measurement
import ToMathlib.Analysis.InnerProductSpace.Trace

/-!
# Nielsen & Chuang, Exercise 12.33 (commuting observables obey classical probability)

*(N&C p. 597.)*

Commuting measurement observables [M_i,M_j]=0 obey classical probability arguments.

## The argument

Commuting observables are **simultaneously diagonalizable**: they share a common orthonormal
eigenbasis `b` (the content of `Observable.exists_commonEigenbasis_of_pairwise_commute`, which rests
on the `n`-operator simultaneous-diagonalization theorem in `ToMathlib/`). Measuring in that
common basis is a *single* projective measurement `m` whose outcome `ω` assigns **every** observable
`Mⱼ` a definite value `Xⱼ ω` at once — the basis vectors are joint eigenstates. The Born rule then
makes `ω ↦ m.bornProb ρ ω` a genuine (classical) probability distribution over the joint outcomes,
on which each `Xⱼ` is an ordinary real-valued random variable. Because the outcomes carry
simultaneous definite values, the family `{Xⱼ}` is described by this one classical joint
distribution, and its expectations reproduce the quantum ones — so the `Xⱼ` obey classical
probability arguments.

## The formalisation

`commuting_observables_classicalProbability` bundles this single claim: for pairwise-commuting
observables there exist an outcome space `Ω`, a joint measurement `m : Measurement Ω S`, real value
functions `X : ι → Ω → ℝ`, and pointer states `ψ : Ω → PureState S` such that

1. `ω ↦ m.bornProb ρ ω` is a genuine probability distribution (non-negative, sums to one);
2. each outcome `ω` is a **simultaneous eigenstate** `ψ ω` of every observable with definite value
   `X j ω` (`(M j).HasEigenstate (X j ω) (ψ ω)`) — the observables are co-measurable; and
3. each observable's quantum expectation is the classical average of its value random variable,
   `∑ ω, m.bornProb ρ ω * X j ω = ρ.expectation (M j)`.

The value functions `X` are shared between (2) and (3): the *same* `X j` is both the definite value
in the pointer state and the classical random variable whose `m`-average reproduces `⟪Mⱼ⟫_ρ`. This
is a faithful reading of "obey classical probability arguments": one classical sample space
`(Ω, bornProb)` carrying all the `Xⱼ` jointly, consistent with quantum predictions. The statement
uses `Observable`, `Measurement`, `PureState`, `Commutes`, `HasEigenstate`, `bornProb` and
`expectation`; the simultaneous diagonalization is in
`AxQM/Postulates/API/CommutingObservables.lean`.

The commutation hypothesis is `∀ i j, (M i).Commutes (M j)` over the whole family — the faithful
`n`-observable statement, not a two-observable specialization.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Exercise 12.33.** Commuting measurement observables obey classical probability arguments.

Given a finite family `M` of pairwise-commuting observables (`∀ i j, (M i).Commutes (M j)`) measured
on a state `ρ`, there exist a finite outcome space `Ω`, a single joint measurement `m`, real value
functions `X j` (the result of `M j`), and pointer states `ψ` such that

* `m.bornProb ρ` is a genuine classical probability distribution (non-negative, total mass one);
* every outcome `ω` is a simultaneous eigenstate `ψ ω` of each `M j` with definite value `X j ω`;
* each observable's quantum expectation is the classical average of `X j` over the joint
  distribution, `∑ ω, m.bornProb ρ ω * X j ω = ρ.expectation (M j)`.

Hence the outcome random variables `X j` live on one classical sample space `(Ω, m.bornProb ρ)` and
reproduce the quantum statistics — they obey classical probability arguments. -/
theorem commuting_observables_classicalProbability {S : QSystem} {ι : Type*} [Finite ι]
    (M : ι → Observable S) (ρ : State S) (hM : ∀ i j, (M i).Commutes (M j)) :
    ∃ (Ω : Type) (_ : Fintype Ω) (m : Measurement Ω S) (X : ι → Ω → ℝ) (ψ : Ω → PureState S),
      (∀ ω, 0 ≤ m.bornProb ρ ω) ∧ (∑ ω, m.bornProb ρ ω = 1) ∧
      (∀ j ω, (M j).HasEigenstate (X j ω) (ψ ω)) ∧
      (∀ j, ∑ ω, m.bornProb ρ ω * X j ω = ρ.expectation (M j)) := by
  obtain ⟨b, X, hb⟩ := Observable.exists_commonEigenbasis_of_pairwise_commute M hM
  refine ⟨Fin (Module.finrank ℂ S.space), inferInstance, Measurement.ofOrthonormalBasis b, X,
    fun ω => ⟨b ω, b.orthonormal.1 ω⟩,
    fun ω => (Measurement.ofOrthonormalBasis b).bornProb_nonneg ρ ω,
    (Measurement.ofOrthonormalBasis b).sum_bornProb_eq_one ρ,
    fun j ω => hb j ω, fun j => ?_⟩
  -- Expand the quantum expectation as a trace in the eigenbasis and match it term-by-term,
  -- using the general-state Born rule in a basis `bornProb ρ i = re ⟪bᵢ, ρ bᵢ⟫`.
  rw [State.expectation, LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have key : ⟪b i, ((ρ.op ∘L (M j).op : S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space) (b i)⟫_ℂ
      = (X j i : ℂ) * ⟪b i, ρ.op (b i)⟫_ℂ := by
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, hb j i, map_smul,
      inner_smul_right]
  rw [Measurement.bornProb_ofOrthonormalBasis b ρ i, key, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

end AxQM
