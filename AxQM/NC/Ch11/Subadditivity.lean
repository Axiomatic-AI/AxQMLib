/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch11.StrongSubadditivityGeneral
import AxQM.NC.Ch11.Theorem11_8
import AxQM.NC.Ch2.Exercise2_78
import AxQM.Postulates.API.ReducedEigenEnsemble
import AxQM.Postulates.API.EntropyConcavity
import AxQM.Postulates.API.MutualInformation
import AxQM.Postulates.API.MutualInformationAncilla
import AxQM.Postulates.API.ReducedStateTransport
import AxQM.Postulates.API.ReducedStateReshape
import AxQM.Postulates.API.ReducedStateComm
import AxQM.Postulates.API.Mixture
import AxQM.Postulates.API.CompositeState
import AxQM.Postulates.API.Qudit

/-!
# Subadditivity of the von Neumann entropy (N&C §11.3.4, eq. (11.74))

Nielsen & Chuang, §11.3.4: for a bipartite state `ρ` on `A ⊗ B`,

`S(A, B) ≤ S(A) + S(B)`      (**subadditivity**, eq. (11.74)),

equivalently `0 ≤ S(A : B)` (the quantum mutual information is non-negative). This file proves
this basic bipartite inequality, the weaker companion of *strong* subadditivity
(`State.vonNeumannEntropy_add_le_add'`, Theorem 11.14).

## Why this is not the `B`-trivial case of strong subadditivity for free

Subadditivity `S(A,B) ≤ S(A) + S(B)` is the specialisation of strong subadditivity
`S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)` to a **trivial middle system** `B`. We realise exactly that:
insert a one-dimensional system `qudit 1` (prepared in the pure state `|0⟩`, contributing zero
entropy) as the middle factor of a tripartite state built from `ρ`, and apply the faithfulness-free
strong subadditivity `State.vonNeumannEntropy_add_le_add'`. Reading off the four marginal entropies
of that inserted state collapses the inequality to `S(A,B) + 0 ≤ S(A) + S(B)`.

The one non-formal step this needs is the entropy of the `A ⊗ (trivial)`-marginal: appending an
uncorrelated pure system does not change the entropy. That is the content of the reusable
factorisation crux proved first:

* `State.eq_tmul_of_isPure_reducedRight` — a bipartite state whose **right marginal is pure**
  factorises as the product of its marginals, `ρ = ρ_A ⊗ ρ_B`. (A mixed-state companion of
  Exercise 2.78, which handles the pure-state case.) Its entropy corollary
  `State.vonNeumannEntropy_eq_reducedLeft_of_isPure_reducedRight` gives `S(ρ) = S(ρ_A)` when `ρ_B`
  is pure.

## Proof of the factorisation crux

`ρ` with `ρ_B` pure: decompose `ρ` into its reduced eigenensemble `{μⱼ, |gⱼ⟩}` (all `μⱼ > 0`), so
`ρ = ∑ⱼ μⱼ |gⱼ⟩⟨gⱼ|`. Tracing out `A` gives `ρ_B = ∑ⱼ μⱼ (|gⱼ⟩⟨gⱼ|)_B`, a convex combination equal
to the *pure* state `ρ_B`; a pure state is an extreme point of the state space
(`State.eq_of_isPure_mix`, proved from the equality condition for concavity of the von Neumann
entropy `State.vonNeumannEntropy_mix_eq_sum_iff'`), so every component `(|gⱼ⟩⟨gⱼ|)_B = ρ_B` is
pure. By Exercise 2.78 (`PureState.isProduct_iff_isPure_reducedRight`) each eigenvector `|gⱼ⟩` is
then a product `|aⱼ⟩|bⱼ⟩` with `|bⱼ⟩⟨bⱼ| = ρ_B`, whence
`ρ = (∑ⱼ μⱼ |aⱼ⟩⟨aⱼ|) ⊗ ρ_B = ρ_A ⊗ ρ_B` by linearity of the tensor product over mixtures.

## Ingredients

The proofs use the faithfulness-free strong subadditivity `State.vonNeumannEntropy_add_le_add'`
(`AxQM/NC/Ch11/StrongSubadditivityGeneral.lean`) and the product-state characterisation
`PureState.isProduct_iff_isPure_reducedRight` (`AxQM/NC/Ch2/Exercise2_78.lean`); the `qudit 1`
trivial system used in the subadditivity proof appears only in proof bodies, never in a statement.

## Main results

* `AxQM.State.eq_of_isPure_mix` — a pure state is extreme: if a mixture is pure, each
  positive-weight component equals it.
* `AxQM.State.eq_tmul_of_isPure_reducedRight` — pure right marginal ⇒ product state.
* `AxQM.State.vonNeumannEntropy_eq_reducedLeft_of_isPure_reducedRight` — `S(ρ) = S(ρ_A)`
  when `ρ_B` is pure.
* `AxQM.State.vonNeumannEntropy_le_reducedLeft_add_reducedRight` — subadditivity
  `S(A,B) ≤ S(A) + S(B)` (N&C eq. (11.74)).
* `AxQM.State.vonNeumannMutualInfo_nonneg` — `0 ≤ S(A : B)`.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S T X Y : QSystem}

/-- **A pure state is an extreme point of the state space.** If a finite mixture
`∑ᵢ pᵢ ρᵢ = State.mix p hp hsum ρ` is a *pure* state, then every component `ρ i` with positive
weight `pᵢ > 0` equals the mixture. The concavity gap `S(mix) − ∑ᵢ pᵢ S(ρᵢ)` is squeezed to `0`
between the faithfulness-free concavity
`State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix'` and the vanishing entropy of the pure
mixture, and the equality condition `State.vonNeumannEntropy_mix_eq_sum_iff'` then forces
`ρ i = mix`. -/
theorem State.eq_of_isPure_mix {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (ρ : ι → State S) (hpure : (State.mix p hp hsum ρ).IsPure) {i : ι}
    (hpi : 0 < p i) : ρ i = State.mix p hp hsum ρ := by
  have hS : (State.mix p hp hsum ρ).vonNeumannEntropy = 0 :=
    State.vonNeumannEntropy_eq_zero_of_isPure _ hpure
  have hconc : ∑ j, p j * (ρ j).vonNeumannEntropy ≤ (State.mix p hp hsum ρ).vonNeumannEntropy :=
    State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix' p hp hsum ρ
  have hnonneg : 0 ≤ ∑ j, p j * (ρ j).vonNeumannEntropy :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hp j) (State.vonNeumannEntropy_nonneg _)
  have heq : (State.mix p hp hsum ρ).vonNeumannEntropy = ∑ j, p j * (ρ j).vonNeumannEntropy := by
    rw [hS]; linarith
  exact (State.vonNeumannEntropy_mix_eq_sum_iff' p hp hsum ρ).mp heq i hpi

/-- **A bipartite state with a pure right marginal is a product state.** If the marginal
`ρ_B = ρ.reducedRight` of `ρ : State (X ⊗ Y)` is pure, then `ρ = ρ_A ⊗ ρ_B` with
`ρ_A = ρ.reducedLeft`. This is the mixed-state companion of Nielsen & Chuang, Exercise 2.78
(`PureState.isProduct_iff_isPure_reducedRight`, the pure-state case): a pure marginal means the
second party carries no correlations. Proved via the spectral (reduced eigenensemble) decomposition
of `ρ`, the extreme-point property of the pure marginal (`State.eq_of_isPure_mix`), Exercise 2.78
applied to each eigenvector, and linearity of the tensor product over mixtures
(`State.mix_tmul`). -/
theorem State.eq_tmul_of_isPure_reducedRight (ρ : State (X.compose Y))
    (h : ρ.reducedRight.IsPure) : ρ = ρ.reducedLeft.tmul ρ.reducedRight := by
  set e := ρ.reducedEigenEnsemble with he
  have hetoState : e.toState = ρ := by rw [he]; exact State.reducedEigenEnsemble_toState ρ
  -- `ρ` is the mixture of its eigenprojectors.
  have hmix : State.mix e.prob e.prob_nonneg e.sum_prob (fun i => (e.states i).toState) = ρ := by
    rw [← hetoState]
    apply State.ext
    rw [State.mix_op, Ensemble.toState_op]
  -- the right marginal is the mixture of the components' right marginals
  have hRmix : ρ.reducedRight
      = State.mix e.prob e.prob_nonneg e.sum_prob (fun i => (e.states i).toState.reducedRight) := by
    rw [← hmix, State.reducedRight_mix]
  -- each component's right marginal equals the (pure) marginal, by extremality
  have hprodR : ∀ i, (e.states i).toState.reducedRight = ρ.reducedRight := by
    intro i
    have hpure : (State.mix e.prob e.prob_nonneg e.sum_prob
        (fun i => (e.states i).toState.reducedRight)).IsPure := by rw [← hRmix]; exact h
    have hpi : 0 < e.prob i := State.reducedEigenEnsemble_prob_pos ρ i
    have hcomp := State.eq_of_isPure_mix e.prob e.prob_nonneg e.sum_prob
      (fun i => (e.states i).toState.reducedRight) hpure hpi
    rw [← hRmix] at hcomp
    exact hcomp
  -- each eigenvector is a product, so each component factors as (·)_A ⊗ ρ_B
  have hfactor : ∀ i, (e.states i).toState
      = (e.states i).toState.reducedLeft.tmul ρ.reducedRight := by
    intro i
    have hProd : (e.states i).IsProduct := by
      rw [PureState.isProduct_iff_isPure_reducedRight, hprodR i]; exact h
    obtain ⟨a, b, hab⟩ := hProd
    have hb : b.toState = ρ.reducedRight := by
      rw [← hprodR i, hab, reducedRight_toState_tmul]
    have hstate : (e.states i).toState = a.toState.tmul b.toState := by
      rw [hab, PureState.toState_tmul]
    have hleft : (e.states i).toState.reducedLeft = a.toState := by
      rw [hab, reducedLeft_toState_tmul]
    rw [hleft, hstate, hb]
  -- assemble
  have hfam : (fun i => (e.states i).toState)
      = (fun i => ((e.states i).toState.reducedLeft).tmul ρ.reducedRight) := funext hfactor
  calc ρ = State.mix e.prob e.prob_nonneg e.sum_prob (fun i => (e.states i).toState) := hmix.symm
    _ = State.mix e.prob e.prob_nonneg e.sum_prob
          (fun i => ((e.states i).toState.reducedLeft).tmul ρ.reducedRight) := by rw [hfam]
    _ = (State.mix e.prob e.prob_nonneg e.sum_prob
          (fun i => (e.states i).toState.reducedLeft)).tmul ρ.reducedRight :=
        (State.mix_tmul e.prob e.prob_nonneg e.sum_prob
          (fun i => (e.states i).toState.reducedLeft) ρ.reducedRight).symm
    _ = ρ.reducedLeft.tmul ρ.reducedRight := by
        rw [← State.reducedLeft_mix e.prob e.prob_nonneg e.sum_prob
          (fun i => (e.states i).toState), hmix]

/-- **A bipartite state with a pure left marginal is a product state.** If the marginal
`ρ_A = ρ.reducedLeft` of `ρ : State (X ⊗ Y)` is pure, then `ρ = ρ_A ⊗ ρ_B` with
`ρ_B = ρ.reducedRight`. The left companion of `State.eq_tmul_of_isPure_reducedRight`: a pure
marginal means the first party carries no correlations. Proved by the same spectral (reduced
eigenensemble) decomposition, the extreme-point property of the pure marginal
(`State.eq_of_isPure_mix`), Exercise 2.78 (`PureState.isProduct_iff_isPure_reducedLeft`) applied to
each eigenvector, and linearity of the tensor product over mixtures (`State.tmul_mix`). -/
theorem State.eq_tmul_of_isPure_reducedLeft (ρ : State (X.compose Y))
    (h : ρ.reducedLeft.IsPure) : ρ = ρ.reducedLeft.tmul ρ.reducedRight := by
  set e := ρ.reducedEigenEnsemble with he
  have hetoState : e.toState = ρ := by rw [he]; exact State.reducedEigenEnsemble_toState ρ
  have hmix : State.mix e.prob e.prob_nonneg e.sum_prob (fun i => (e.states i).toState) = ρ := by
    rw [← hetoState]
    apply State.ext
    rw [State.mix_op, Ensemble.toState_op]
  -- the left marginal is the mixture of the components' left marginals
  have hLmix : ρ.reducedLeft
      = State.mix e.prob e.prob_nonneg e.sum_prob (fun i => (e.states i).toState.reducedLeft) := by
    rw [← hmix, State.reducedLeft_mix]
  -- each component's left marginal equals the (pure) marginal, by extremality
  have hprodL : ∀ i, (e.states i).toState.reducedLeft = ρ.reducedLeft := by
    intro i
    have hpure : (State.mix e.prob e.prob_nonneg e.sum_prob
        (fun i => (e.states i).toState.reducedLeft)).IsPure := by rw [← hLmix]; exact h
    have hpi : 0 < e.prob i := State.reducedEigenEnsemble_prob_pos ρ i
    have hcomp := State.eq_of_isPure_mix e.prob e.prob_nonneg e.sum_prob
      (fun i => (e.states i).toState.reducedLeft) hpure hpi
    rw [← hLmix] at hcomp
    exact hcomp
  -- each eigenvector is a product, so each component factors as ρ_A ⊗ (·)_B
  have hfactor : ∀ i, (e.states i).toState
      = ρ.reducedLeft.tmul ((e.states i).toState.reducedRight) := by
    intro i
    have hProd : (e.states i).IsProduct := by
      rw [PureState.isProduct_iff_isPure_reducedLeft, hprodL i]; exact h
    obtain ⟨a, b, hab⟩ := hProd
    have ha : a.toState = ρ.reducedLeft := by
      rw [← hprodL i, hab, reducedLeft_toState_tmul]
    have hstate : (e.states i).toState = a.toState.tmul b.toState := by
      rw [hab, PureState.toState_tmul]
    have hright : (e.states i).toState.reducedRight = b.toState := by
      rw [hab, reducedRight_toState_tmul]
    rw [hright, hstate, ha]
  -- assemble
  have hfam : (fun i => (e.states i).toState)
      = (fun i => ρ.reducedLeft.tmul ((e.states i).toState.reducedRight)) := funext hfactor
  calc ρ = State.mix e.prob e.prob_nonneg e.sum_prob (fun i => (e.states i).toState) := hmix.symm
    _ = State.mix e.prob e.prob_nonneg e.sum_prob
          (fun i => ρ.reducedLeft.tmul ((e.states i).toState.reducedRight)) := by rw [hfam]
    _ = ρ.reducedLeft.tmul (State.mix e.prob e.prob_nonneg e.sum_prob
          (fun i => (e.states i).toState.reducedRight)) :=
        (State.tmul_mix e.prob e.prob_nonneg e.sum_prob ρ.reducedLeft
          (fun i => (e.states i).toState.reducedRight)).symm
    _ = ρ.reducedLeft.tmul ρ.reducedRight := by
        rw [← State.reducedRight_mix e.prob e.prob_nonneg e.sum_prob
          (fun i => (e.states i).toState), hmix]

/-- **Entropy of a state with a pure right marginal.** If `ρ.reducedRight` is pure, then
`S(ρ) = S(ρ.reducedLeft)`: the (uncorrelated, pure) second factor contributes nothing to the
entropy. Immediate from the factorisation `State.eq_tmul_of_isPure_reducedRight`, the additivity of
entropy over tensor products (`State.vonNeumannEntropy_tmul`), and the vanishing entropy of a pure
state. -/
theorem State.vonNeumannEntropy_eq_reducedLeft_of_isPure_reducedRight (ρ : State (X.compose Y))
    (h : ρ.reducedRight.IsPure) : ρ.vonNeumannEntropy = ρ.reducedLeft.vonNeumannEntropy := by
  conv_lhs => rw [State.eq_tmul_of_isPure_reducedRight ρ h]
  rw [State.vonNeumannEntropy_tmul, State.vonNeumannEntropy_eq_zero_of_isPure _ h, add_zero]

/-- **Subadditivity of the von Neumann entropy** (Nielsen & Chuang, §11.3.4, eq. (11.74)): for a
bipartite state `σ` on `S ⊗ T`,

`S(σ) ≤ S(σ_S) + S(σ_T)`.

Realised as the trivial-middle-system case of strong subadditivity: append a pure one-dimensional
ancilla `τ = |0⟩⟨0|` on `qudit 1` and re-associate `σ ⊗ τ` into the tripartite state
`ρ` on `S ⊗ ((qudit 1) ⊗ T)`, so that `qudit 1` sits in the *middle*. Strong subadditivity
`State.vonNeumannEntropy_add_le_add'` for `ρ` reads `S(σ) + S(τ) ≤ S(M) + S(σ_T)`, where `M` is the
`S ⊗ (qudit 1)`-marginal; since `τ` is pure (`S(τ) = 0`) and `M` has a pure `qudit 1`-marginal
(`S(M) = S(σ_S)` by `State.vonNeumannEntropy_eq_reducedLeft_of_isPure_reducedRight`), this collapses
to the subadditivity inequality. -/
theorem State.vonNeumannEntropy_le_reducedLeft_add_reducedRight (σ : State (S.compose T)) :
    σ.vonNeumannEntropy ≤ σ.reducedLeft.vonNeumannEntropy + σ.reducedRight.vonNeumannEntropy := by
  -- trivial one-dimensional middle system, prepared pure
  set τ : State (qudit 1) := (quditBasis (0 : Fin 1)).toState with hτdef
  have hτpure : τ.IsPure := ⟨quditBasis (0 : Fin 1), hτdef⟩
  have hτ0 : τ.vonNeumannEntropy = 0 := State.vonNeumannEntropy_eq_zero_of_isPure _ hτpure
  -- `κ` on `S ⊗ (T ⊗ triv)`: `σ` with a pure trivial factor appended on the far right
  set κ : State (S.compose (T.compose (qudit 1))) :=
    State.congr (QSystem.assoc S T (qudit 1)).symm (σ.tmul τ) with hκdef
  have hκL : κ.reducedLeft = σ.reducedLeft := State.reducedLeft_congr_symm_assoc_tmul σ τ
  have hκR : κ.reducedRight = σ.reducedRight.tmul τ := State.reducedRight_congr_symm_assoc_tmul σ τ
  have hκent : κ.vonNeumannEntropy = σ.vonNeumannEntropy := by
    rw [hκdef, State.vonNeumannEntropy_congr, State.vonNeumannEntropy_tmul, hτ0, add_zero]
  -- `ρ` on `S ⊗ (triv ⊗ T)`: swap the middle trivial factor inward
  set ρ : State (S.compose ((qudit 1).compose T)) :=
    State.congr ((QSystem.Iso.refl S).tmul (QSystem.Iso.comm T (qudit 1))) κ with hρdef
  have hρL : ρ.reducedLeft = σ.reducedLeft := by
    rw [hρdef, State.reducedLeft_congr_tmul_refl, hκL]
  have hρR : ρ.reducedRight
      = State.congr (QSystem.Iso.comm T (qudit 1)) (σ.reducedRight.tmul τ) := by
    rw [hρdef, State.reducedRight_congr_tmul_right, hκR]
  have hρent : ρ.vonNeumannEntropy = σ.vonNeumannEntropy := by
    rw [hρdef, State.vonNeumannEntropy_congr, hκent]
  have hρRL : ρ.reducedRight.reducedLeft = τ := by
    rw [hρR, ← State.reducedRight_congr_comm (σ.reducedRight.tmul τ), State.reducedRight_tmul]
  have hρRent : ρ.reducedRight.vonNeumannEntropy = σ.reducedRight.vonNeumannEntropy := by
    rw [hρR, State.vonNeumannEntropy_congr, State.vonNeumannEntropy_tmul, hτ0, add_zero]
  -- the `S ⊗ triv`-marginal `M` has entropy `S(σ_S)`, since its trivial factor is pure
  set M : State (S.compose (qudit 1)) :=
    (State.congr (QSystem.assoc S (qudit 1) T) ρ).reducedLeft with hMdef
  have hML : M.reducedLeft = σ.reducedLeft := by
    rw [hMdef, State.reducedLeft_reducedLeft_congr_assoc, hρL]
  have hMR : M.reducedRight = τ := by
    rw [hMdef, State.reducedRight_reducedLeft_congr_assoc, hρRL]
  have hMent : M.vonNeumannEntropy = σ.reducedLeft.vonNeumannEntropy := by
    rw [State.vonNeumannEntropy_eq_reducedLeft_of_isPure_reducedRight M
      (by rw [hMR]; exact hτpure), hML]
  -- strong subadditivity with the trivial middle system collapses to subadditivity
  have hSSA := State.vonNeumannEntropy_add_le_add' ρ
  rw [hρent, hρRL, hτ0, ← hMdef, hMent, hρRent] at hSSA
  linarith

/-- **Non-negativity of the quantum mutual information** (Nielsen & Chuang, §11.3.4): for a
bipartite state `σ` on `S ⊗ T`, `0 ≤ S(S : T)`. This is subadditivity
`State.vonNeumannEntropy_le_reducedLeft_add_reducedRight` rewritten through the definition
`S(S : T) = S(σ_S) + S(σ_T) − S(σ)`. -/
theorem State.vonNeumannMutualInfo_nonneg (σ : State (S.compose T)) :
    0 ≤ σ.vonNeumannMutualInfo := by
  rw [State.vonNeumannMutualInfo_def]
  linarith [State.vonNeumannEntropy_le_reducedLeft_add_reducedRight σ]

end AxQM
