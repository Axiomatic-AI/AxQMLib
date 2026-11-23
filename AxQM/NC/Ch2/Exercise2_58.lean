/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Variance

/-!
# Nielsen & Chuang, Exercise 2.58

For an eigenstate of observable M, find the average value and standard deviation.

The exercise is read off the projective-measurement machinery of
N&C §2.2.5 (page 88): the average value of an observable `M` in the state `|ψ⟩` is `⟪M⟫ = ⟨ψ|M|ψ⟩`
(N&C (2.113)) and the standard deviation is `Δ(M) = √(⟪M²⟫ − ⟪M⟫²)` (N&C (2.115)). For an eigenstate
the answers are `⟪M⟫ = m` and `Δ(M) = 0`: a measurement of `M` yields `m` with certainty, so its
average is `m` and there is no spread.

## The formalisation

The two theorems below are the exercise's two answers, stated with the eigenstate predicate
`Observable.HasEigenstate` and the statistics `PureState.expectation` / `PureState.stdDev`:

* `AxQM.eigenstate_expectation_eq_eigenvalue` — **the average is the eigenvalue:** if `ψ`
  is an eigenstate of `M` with eigenvalue `m`, then `⟪M⟫_ψ = m`.
* `AxQM.eigenstate_stdDev_eq_zero` — **the standard deviation vanishes:** in the same
  situation `Δ(M)_ψ = 0`.

## Design notes

* **The eigenstate predicate.** The eigenvalue condition `M ψ = m • ψ` is the predicate
  `Observable.HasEigenstate` (in `AxQM/Postulates/API/Eigenstate.lean`, also used by
  Exercise 2.53). The average answer *is* the general lemma
  `PureState.expectation_of_hasEigenstate` (the expectation in an eigenstate equals the eigenvalue);
  `eigenstate_expectation_eq_eigenvalue` records it as Exercise 2.58's named answer by applying that
  lemma.
* **Statistics.** `PureState.variance`, `PureState.stdDev`, `Observable.sq` (`M²`) and
  `Observable.HasEigenstate.sq` are defined in `AxQM/Postulates/API/Variance.lean`;
  Exercise 2.59 (average/standard deviation of `X` on `|0⟩`) uses the same `variance`/`stdDev`.
* **Proof.** The average is `PureState.expectation_of_hasEigenstate`. For the standard deviation,
  `Observable.HasEigenstate.sq` upgrades the eigenstate to an eigenstate of `M²` with eigenvalue
  `m²`, so `⟪M²⟫ = m²` and `⟪M⟫² = m²`; the variance `⟪M²⟫ − ⟪M⟫² = 0` and `√0 = 0`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 2.58 (average).** If the pure state `ψ` is an eigenstate of the
observable `M` with eigenvalue `m`, then the average observed value of `M` is the eigenvalue:
`⟪M⟫_ψ = m`. The measurement of `M` in an eigenstate returns `m` with certainty, so its mean is `m`.
Exercise 2.58's named form of the general lemma `PureState.expectation_of_hasEigenstate`. -/
theorem eigenstate_expectation_eq_eigenvalue {ψ : PureState S} {M : Observable S} {m : ℝ}
    (h : M.HasEigenstate m ψ) : ψ.expectation M = m :=
  PureState.expectation_of_hasEigenstate h

/-- **Nielsen & Chuang, Exercise 2.58 (standard deviation).** If the pure state `ψ` is an eigenstate
of the observable `M` with eigenvalue `m`, then the standard deviation of `M` vanishes:
`Δ(M)_ψ = 0`. There is no spread in the measured values, since `M` yields `m` with certainty.
Proof: `Observable.HasEigenstate.sq` gives `⟪M²⟫ = m²`, and `⟪M⟫ = m` gives `⟪M⟫² = m²`, so the
variance `⟪M²⟫ − ⟪M⟫² = 0` and `Δ(M) = √0 = 0`. -/
theorem eigenstate_stdDev_eq_zero {ψ : PureState S} {M : Observable S} {m : ℝ}
    (h : M.HasEigenstate m ψ) : ψ.stdDev M = 0 := by
  simp only [PureState.stdDev, PureState.variance,
    PureState.expectation_of_hasEigenstate h,
    PureState.expectation_of_hasEigenstate h.sq, sub_self, Real.sqrt_zero]

end AxQM
