/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Support
import AxQM.Postulates.API.Mixture
import AxQM.Postulates.API.ConditionalEntropyConcave
import AxQM.Postulates.API.EntropyOrthogonalMixture

/-!
# AxQM — vocabulary for the Araki–Lieb equality conditions (N&C Exercise 11.16)

Nielsen & Chuang's Exercise 11.16 characterises when the triangle (Araki–Lieb) inequality
`S(A, B) ≥ S(B) − S(A)` is saturated, in terms of the marginals `ρ^A_i = tr_B(|i⟩⟨i|)` and
`ρ^B_i = tr_A(|i⟩⟨i|)` of the eigenprojectors of `ρ^{AB}`. This file supplies the two
predicates that phrasing needs — "the `ρ^A_i` have a common eigenbasis" and "the `ρ^B_i` have
orthogonal support" — together with the partial-trace / support facts that
`AxQM/NC/Ch11/Exercise11_16.lean` uses to discharge them.

## Main definitions

* `AxQM.State.HasCommonEigenbasis` — a finite family of states `ρ : ι → State S` is
  simultaneously diagonalisable: there is a single orthonormal basis `e` of `S.space` every vector
  of which is an eigenvector (real eigenvalue) of every `ρ i`. This is the precise reading of
  N&C's "the operators `ρ^A_i` have a common eigenbasis".
* `AxQM.State.OrthogonalSupports` — a finite family `ρ : ι → State S` has pairwise
  orthogonal supports, `(ρ i).support ⟂ (ρ j).support` for `i ≠ j` (`State.support`, the range of
  the density operator). N&C's "the `ρ^B_i` have orthogonal support".

## Main results

* `AxQM.State.support_isOrtho_toState_of_inner_eq_zero` — two pure states with orthogonal
  vectors have orthogonal supports, `⟪ψ, φ⟫ = 0 → |ψ⟩⟨ψ|.support ⟂ |φ⟩⟨φ|.support`.
* `AxQM.State.reducedLeft_mix` / `State.reducedRight_mix` — the partial trace is linear:
  the reduced state of a mixture `∑ᵢ pᵢ ρᵢ` is the mixture `∑ᵢ pᵢ (ρᵢ)_A` of the reduced states.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **A finite family of states has a common eigenbasis** — it is simultaneously diagonalisable.
There exists an **orthonormal basis** of `S.space` (a family `e : Fin n → S.space` that is
orthonormal and spans, `Submodule.span ℂ (Set.range e) = ⊤`) every vector `e k` of which is an
eigenvector, with a real eigenvalue, of *every* member `ρ i`: `(ρ i).op (e k) = c • e k`. This is
the precise reading of Nielsen & Chuang's phrase "the operators `ρ^A_i` have a common eigenbasis"
(Exercise 11.16). -/
def State.HasCommonEigenbasis {ι : Type*} (ρ : ι → State S) : Prop :=
  ∃ (n : ℕ) (e : Fin n → S.space), Orthonormal ℂ e ∧ Submodule.span ℂ (Set.range e) = ⊤ ∧
    ∀ (i : ι) (k : Fin n), ∃ c : ℝ, (ρ i).op (e k) = (c : ℂ) • e k

/-- **A finite family of states has pairwise orthogonal supports.** For `i ≠ j` the supports
`(ρ i).support`, `(ρ j).support` (the ranges of the density operators, `State.support`) are
orthogonal submodules. Nielsen & Chuang's "the `ρ^B_i` have orthogonal support" (Exercise 11.16). -/
def State.OrthogonalSupports {ι : Type*} (ρ : ι → State S) : Prop :=
  Pairwise fun i j => (ρ i).support ⟂ (ρ j).support

/-- **Orthogonal vectors give orthogonal supports for the associated pure states.** If the unit
vectors of two pure states are orthogonal, `⟪ψ.vec, φ.vec⟫ = 0`, then the supports of the rank-one
projectors `|ψ⟩⟨ψ|` and `|φ⟩⟨φ|` are orthogonal submodules. The support of `|ψ⟩⟨ψ|` is the range of
`rankOne ψ.vec ψ.vec`, i.e. the line `ℂ · ψ.vec`; two such lines are orthogonal exactly when the
vectors are. The building block behind the "orthogonal support" hypothesis of Exercise 11.16 for
families of orthonormal pure states. -/
theorem State.support_isOrtho_toState_of_inner_eq_zero (ψ φ : PureState S)
    (h : inner ℂ ψ.vec φ.vec = 0) :
    ψ.toState.support ⟂ φ.toState.support := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  simp only [State.support, PureState.toState_op, LinearMap.mem_range] at hu hv
  obtain ⟨x, rfl⟩ := hu
  obtain ⟨y, rfl⟩ := hv
  simp only [ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply, inner_smul_left,
    inner_smul_right, h, mul_zero]

/-- **An orthonormal family of pure states has pairwise orthogonal supports.** If the state vectors
`(ψ i).vec` are orthonormal, then the rank-one projectors `(ψ i).toState = |ψᵢ⟩⟨ψᵢ|` have pairwise
orthogonal supports (each pair of distinct vectors is orthogonal, so
`State.support_isOrtho_toState_of_inner_eq_zero` applies). The bridge from an orthonormal
eigen/Schmidt frame to the `OrthogonalSupports` / `vonNeumannEntropy_mix_orthogonalSupport`
hypotheses. -/
theorem State.pairwise_support_isOrtho_of_orthonormal {ι : Type*}
    (ψ : ι → PureState S) (h : Orthonormal ℂ fun i => (ψ i).vec) :
    Pairwise fun i j => (ψ i).toState.support ⟂ (ψ j).toState.support := fun _ _ hij =>
  State.support_isOrtho_toState_of_inner_eq_zero _ _ (h.2 hij)

/-- **The von Neumann entropy of a mixture of an orthonormal family of pure states is the Shannon
entropy of the mixing weights**: `S(∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|) = H(p)` when the `(ψ i).vec` are orthonormal.
The pure-component specialization of `State.vonNeumannEntropy_mix_orthogonalSupport` (each component
has zero entropy and the family has orthogonal supports by
`pairwise_support_isOrtho_of_orthonormal`), so the general `H(p) + ∑ᵢ pᵢ S(ρᵢ)` collapses to
`H(p)`. -/
theorem State.vonNeumannEntropy_mix_toState_orthonormal {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ψ : ι → PureState S)
    (h : Orthonormal ℂ fun i => (ψ i).vec) :
    (State.mix p hp hsum (fun i => (ψ i).toState)).vonNeumannEntropy = Real.entropy p := by
  rw [State.vonNeumannEntropy_mix_orthogonalSupport _ _ _ _
    (State.pairwise_support_isOrtho_of_orthonormal ψ h)]
  simp only [PureState.vonNeumannEntropy_toState_eq_zero, mul_zero, Finset.sum_const_zero, add_zero]

/-- **The partial trace over the right factor is linear on mixtures**: the left reduced state of a
mixture `∑ᵢ pᵢ ρᵢ` is the mixture `∑ᵢ pᵢ (ρᵢ)_A` of the left reduced states. Both `.op`s are
`∑ᵢ pᵢ · Tr_T(ρᵢ.op)` — the operator-level linearity `State.mix_reducedLeft_op` (built on the
structural `LinearMap.partialTraceRight_sum_smul`) plus the mixture bridge `State.mix_op`. -/
theorem State.reducedLeft_mix {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (ρ : ι → State (S ⊗ T)) :
    (State.mix p hp hsum ρ).reducedLeft = State.mix p hp hsum (fun i => (ρ i).reducedLeft) := by
  ext1
  rw [State.mix_reducedLeft_op, State.mix_op]

/-- **The partial trace over the left factor is linear on mixtures**: the right reduced state of a
mixture `∑ᵢ pᵢ ρᵢ` is the mixture `∑ᵢ pᵢ (ρᵢ)_B` of the right reduced states. The `reducedRight`
analogue of `State.reducedLeft_mix`, via the operator-level linearity `State.mix_reducedRight_op`
and the mixture bridge `State.mix_op`. -/
theorem State.reducedRight_mix {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (ρ : ι → State (S ⊗ T)) :
    (State.mix p hp hsum ρ).reducedRight = State.mix p hp hsum (fun i => (ρ i).reducedRight) := by
  ext1
  rw [State.mix_reducedRight_op, State.mix_op]

end AxQM
