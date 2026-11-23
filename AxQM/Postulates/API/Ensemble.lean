/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.StateSpace
import ToMathlib.Analysis.InnerProductSpace.Spectrum

/-!
# AxQM — ensembles of pure states and the density operator they generate

An **ensemble of pure states** `{pᵢ, |ψᵢ⟩}` (Nielsen–Chuang §2.4.1) is a finite family of
pure states `|ψᵢ⟩` together with a probability distribution `pᵢ`. Its **density operator**
is the probability-weighted mixture of the pure-state projectors,
`ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` (eq. (2.138)).

This file is the machinery behind **Theorem 2.5** (characterization of density
operators). The theorem says an operator is a density operator (arises from an ensemble) *iff*
it is positive with trace one. In this development a `State` already bundles
"positive with trace one", so the two halves are:

* **forward** (ensemble ⟹ density operator): `Ensemble.toState` produces a genuine `State`;
* **converse** (density operator ⟹ ensemble): `Ensemble.ofState` builds the *eigenensemble*
  (spectral decomposition, eq. (2.157)) and `Ensemble.ofState_toState` shows it reproduces the
  state — hence `Ensemble.toState` is onto `State S` (`Ensemble.toState_surjective`, in
  `AxQM/NC/Ch2/Theorem2_5.lean`).

## Main definitions

* `AxQM.Ensemble` — an ensemble of pure states: a finite family of `PureState`s with a
  probability distribution.
* `AxQM.Ensemble.toState` — the density operator `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` of an ensemble.
* `AxQM.Ensemble.ofState` — the eigenensemble of a state (spectral decomposition).

## Main results

* `Ensemble.toState_op` / `Ensemble.toState_op_apply` — the `_op` bridges: the ensemble's operator
  is `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`.
* `Ensemble.ofState_toState` — the eigenensemble reproduces the state (converse of Theorem 2.5).
* `isDensityOp_iff_exists_ensemble` — Theorem 2.5, operator form: `T` is a density operator iff it
  is the density operator of some ensemble.
-/

open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- An **ensemble of pure states** `{pᵢ, |ψᵢ⟩}` of a quantum system `S` (Nielsen–Chuang §2.4.1):
a finite family of pure states `states i` together with a probability distribution `prob i`
(non-negative, summing to one). The generating data for a (possibly mixed) density operator. -/
structure Ensemble (S : QSystem) where
  /-- The number of pure states in the ensemble. -/
  card : ℕ
  /-- The probability weights `pᵢ` of the ensemble. -/
  prob : Fin card → ℝ
  /-- The pure states `|ψᵢ⟩` of the ensemble. -/
  states : Fin card → PureState S
  /-- Each probability is non-negative. -/
  prob_nonneg : ∀ i, 0 ≤ prob i
  /-- The probabilities sum to one. -/
  sum_prob : ∑ i, prob i = 1

namespace Ensemble

/-- The **density operator of an ensemble** `{pᵢ, |ψᵢ⟩}` (Nielsen–Chuang eq. (2.138)): the state
`ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`, the probability-weighted mixture of the pure-state projectors. This is the
*forward* half of Theorem 2.5 — every ensemble yields a genuine density operator — captured by the
target type `State S`: positivity is a sum of `pᵢ • (positive)` with `pᵢ ≥ 0`, and the trace is
`∑ᵢ pᵢ · 1 = ∑ᵢ pᵢ = 1`. -/
def toState (e : Ensemble S) : State S where
  op := ∑ i, (e.prob i : ℂ) • (e.states i).toState.op
  isDensity := by
    refine ⟨?_, ?_⟩
    · exact ContinuousLinearMap.isPositive_sum _ fun i _ =>
        (e.states i).toState.isPositive_op.smul_of_nonneg (by exact_mod_cast e.prob_nonneg i)
    · rw [ContinuousLinearMap.toLinearMap_sum, map_sum]
      simp only [ContinuousLinearMap.toLinearMap_smul, map_smul, State.trace_op_eq_one, smul_eq_mul,
        mul_one]
      rw [← Complex.ofReal_sum, e.sum_prob, Complex.ofReal_one]

/-- The **`_op` bridge** for an ensemble's density operator: `ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`, i.e. Nielsen–
Chuang eq. (2.138). Definitional. -/
theorem toState_op (e : Ensemble S) :
    e.toState.op = ∑ i, (e.prob i : ℂ) • (e.states i).toState.op := rfl

/-- The action of an ensemble's density operator on a vector: `ρ v = ∑ᵢ pᵢ ⟪ψᵢ, v⟫ |ψᵢ⟩`,
obtained from `toState_op` and `rankOne_apply`. The pointwise form consumed by
`Ensemble.ofState_toState`. -/
theorem toState_op_apply (e : Ensemble S) (v : S) :
    e.toState.op v = ∑ i, (e.prob i : ℂ) • (inner ℂ (e.states i).vec v • (e.states i).vec) := by
  rw [toState_op, sum_apply]
  simp only [smul_apply, PureState.toState_op, InnerProductSpace.rankOne_apply]

/-- The **eigenensemble** of a state `ρ` (Nielsen–Chuang, converse of Theorem 2.5, eq. (2.157)):
the ensemble `{λⱼ, |j⟩}` whose pure states `|j⟩` form an orthonormal eigenbasis of the density
operator `ρ`, weighted by the eigenvalues `λⱼ`. The eigenvalues are non-negative and sum to one
(`IsDensityOp.eigenvalues_nonneg` / `eigenvalues_sum_eq_one`), so they form a probability
distribution; the eigenvectors are unit vectors (orthonormality). The construction
invokes the spectral theorem. -/
def ofState (ρ : State S) : Ensemble S where
  card := Module.finrank ℂ S.space
  prob := ρ.isDensity.isSymmetric.eigenvalues rfl
  states i :=
    ⟨ρ.isDensity.isSymmetric.eigenvectorBasis rfl i,
      (ρ.isDensity.isSymmetric.eigenvectorBasis rfl).orthonormal.norm_eq_one i⟩
  prob_nonneg i := ρ.isDensity.eigenvalues_nonneg rfl i
  sum_prob := ρ.isDensity.eigenvalues_sum_eq_one rfl

/-- **The eigenensemble reproduces the state**: `(Ensemble.ofState ρ).toState = ρ` for every state
`ρ`. This is the *converse* half of Nielsen–Chuang Theorem 2.5 — every density operator arises from
an ensemble (here the eigenensemble). Proved by the spectral expansion
`LinearMap.IsSymmetric.spectral_sum_apply`: on each vector `v`,
`ρ v = ∑ⱼ λⱼ ⟪|j⟩, v⟫ |j⟩ = (∑ⱼ λⱼ |j⟩⟨j|) v`. -/
theorem ofState_toState (ρ : State S) : (ofState ρ).toState = ρ := by
  refine State.ext ?_
  refine ContinuousLinearMap.ext fun v => ?_
  rw [toState_op_apply]
  exact (ρ.isDensity.isSymmetric.spectral_sum_apply (n := (ofState ρ).card) rfl v).symm

end Ensemble

/-- **Nielsen–Chuang Theorem 2.5, operator form.** An operator `T` on a quantum system `S` is a
*density operator* — positive with trace one (`ContinuousLinearMap.IsDensityOp`) — if and only if
it is the density operator `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` of some ensemble of pure states. The literal rendering
of the textbook "ρ is a density operator iff (1) trace one (2) positive": the `IsDensityOp`
predicate is exactly the trace-and-positivity conditions.

Forward: pack `T` and its density hypothesis as a `State`, whose eigenensemble
(`Ensemble.ofState` / `ofState_toState`) reproduces it. Backward: an ensemble's operator is a
density operator by construction (`Ensemble.toState`). -/
theorem isDensityOp_iff_exists_ensemble {T : S →L[ℂ] S} :
    T.IsDensityOp ↔ ∃ e : Ensemble S, e.toState.op = T := by
  constructor
  · intro hT
    exact ⟨Ensemble.ofState ⟨T, hT⟩, congrArg State.op (Ensemble.ofState_toState ⟨T, hT⟩)⟩
  · rintro ⟨e, rfl⟩
    exact e.toState.isDensity

end AxQM
