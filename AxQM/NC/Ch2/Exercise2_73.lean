/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MinimalEnsembleProbability

/-!
# Nielsen & Chuang, Exercise 2.73 (minimal ensemble through a support vector)

Minimal ensemble for rho containing |psi> in support, with p_i=1/<psi|rho^-1|psi>.

The exercise makes two claims about the ensembles that realise `ρ` with as few states as possible:

* `exists_isMinimalFor_states_eq_of_memSupport` — **existence:** for `|ψ⟩` in the support of `ρ`
  (`PureState.MemSupport`), some minimal ensemble for `ρ` (`Ensemble.IsMinimalFor`, size `rank ρ`)
  has `|ψ⟩` as one of its states.
* `Ensemble.IsMinimalFor.prob_eq_inv_pseudoInverseExpectation` — **probability formula:** in any
  minimal ensemble for `ρ`, each state `|ψᵢ⟩` appears with weight `pᵢ = 1/⟨ψᵢ|ρ⁻¹|ψᵢ⟩`, where
  `⟨ψᵢ|ρ⁻¹|ψᵢ⟩` is the pseudo-inverse expectation `State.pseudoInverseExpectation`.

The notions they use are defined in `AxQM/Postulates/API/`: the pseudo-inverse
`State.pseudoInverse` (`PseudoInverse`), the support `State.support` (`Support`), the reduced
eigenensemble `State.reducedEigenEnsemble` (`ReducedEigenEnsemble`) and the minimal-ensemble
predicate `Ensemble.IsMinimalFor` (`MinimalEnsemble`). The proofs are
`exists_isMinimalFor_mem_of_mem_support` (`MinimalEnsembleExistence`) and the probability formula
in `MinimalEnsembleProbability`.
-/

namespace AxQM

variable {S : QSystem}

/-- **Nielsen–Chuang Exercise 2.73 (existence).** For a pure state `|ψ⟩` in the support of `ρ`
(`ψ.MemSupport ρ`) there is a *minimal* ensemble for `ρ` (`Ensemble.IsMinimalFor`, of size `rank ρ`)
that **contains** `|ψ⟩`: one of its pure states equals `|ψ⟩`.

The construction (rotating the reduced eigenensemble by a unitary whose first row produces `|ψ⟩`)
is `exists_isMinimalFor_mem_of_mem_support` in `AxQM/Postulates/API/MinimalEnsembleExistence.lean`.
Equality of pure states `e.states i = ψ` follows from equality of their vectors by
`PureState.ext`. -/
theorem exists_isMinimalFor_states_eq_of_memSupport (ρ : State S) (ψ : PureState S)
    (h : ψ.MemSupport ρ) :
    ∃ e : Ensemble S, e.IsMinimalFor ρ ∧ ∃ i, e.states i = ψ := by
  obtain ⟨e, hmin, i, hi⟩ := exists_isMinimalFor_mem_of_mem_support ρ ψ h
  exact ⟨e, hmin, i, PureState.ext hi⟩

/-- **Nielsen–Chuang Exercise 2.73 (probability formula).** In any minimal ensemble `{pᵢ, |ψᵢ⟩}` for
`ρ`, each state `|ψᵢ⟩` appears with probability
`pᵢ = 1 / ⟨ψᵢ|ρ⁻¹|ψᵢ⟩`,
where `⟨ψᵢ|ρ⁻¹|ψᵢ⟩` is the pseudo-inverse expectation `State.pseudoInverseExpectation` (the matrix
element of the "inverse on the support" `ρ⁻¹` in `|ψᵢ⟩`). N&C eq. (2.176).

It is the reciprocal of `Ensemble.IsMinimalFor.pseudoInverseExpectation_eq_inv_prob`
(`⟨ψᵢ|ρ⁻¹|ψᵢ⟩ = pᵢ⁻¹`) in `AxQM/Postulates/API/MinimalEnsembleProbability.lean`. -/
theorem Ensemble.IsMinimalFor.prob_eq_inv_pseudoInverseExpectation {e : Ensemble S} {ρ : State S}
    (hmin : e.IsMinimalFor ρ) (i : Fin e.card) :
    e.prob i = 1 / ρ.pseudoInverseExpectation (e.states i) := by
  rw [hmin.pseudoInverseExpectation_eq_inv_prob i, one_div, inv_inv]

end AxQM
