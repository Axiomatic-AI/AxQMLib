/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl
import AxQM.Postulates.API.EntropyConcavity
import AxQM.Postulates.API.EntropyEvolution
import AxQM.Postulates.API.MaximallyMixed
import AxQM.Postulates.API.Evolution

/-!
# AxQM — `I/d` is the unique maximal-entropy state (the depolarizing-twirl proof)

Nielsen & Chuang, **Exercise 11.19** (p. 517), part 2: the completely mixed state `I/d` is the
**unique** state of maximal von Neumann entropy. This file supplies the *alternate* proof the
exercise asks for — via the depolarizing **twirl** and the *strict* concavity of the entropy —
distinct from the eigenvalue/Shannon-entropy argument in `AxQM/Postulates/API/EntropyExtremal.lean`
(`State.eq_maximallyMixed_of_vonNeumannEntropy_eq_log_finrank`).

## The twirl (part 1) and the deduction (part 2)

The operator content of the exercise — "there exist unitaries `Uⱼ` and probabilities `pⱼ` with
`∑ⱼ pⱼ Uⱼ A Uⱼ† = tr(A) I/d` for **any** matrix `A`" — is pure linear algebra and lives in
`ToMathlib` as `LinearIsometryEquiv.exists_conjStarAlgEquiv_oneDesign` (built on the `2^d·d!`-term
depolarizing `1`-design `OrthonormalBasis.sum_conjStarAlgEquiv_depolarizingUnitary`).
`exists_randomUnitary_twirl_eq_maximallyMixed` lifts it to states: since a density
operator has unit trace, twirling **any state** `ρ` gives `∑ⱼ pⱼ Uⱼ ρ Uⱼ† = I/d`.

The deduction is N&C's: `I/d = ∑ⱼ pⱼ Uⱼ ρ Uⱼ†` is a mixture of the `Uⱼ ρ Uⱼ†`, so concavity
(`State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix`) plus unitary invariance
(`State.vonNeumannEntropy_evolve`, `S(Uⱼ ρ Uⱼ†) = S(ρ)`) give `S(I/d) ≥ S(ρ)` — maximality. For
uniqueness, `S(ρ) = S(I/d)` forces *equality* in concavity, so **strict** concavity (Exercise 11.18,
`State.vonNeumannEntropy_mix_eq_sum_iff`) makes all the `Uⱼ ρ Uⱼ†` coincide; their common value is
their average `I/d`, so `Uⱼ ρ Uⱼ† = I/d` for some `j`, whence `ρ = Uⱼ† (I/d) Uⱼ = I/d`
(`Evolution.evolve_maximallyMixedState`).

The statements of Exercise 11.19 are in `AxQM/NC/Ch11/Exercise11_19.lean`, which refers to the
declarations here.

## Main results

* `AxQM.exists_randomUnitary_twirl_eq_maximallyMixed` — part 1 (physics form): a finite
  family of unitary evolutions whose uniform twirl sends every state to `I/d`.
* `AxQM.State.vonNeumannEntropy_le_maximallyMixed` — part 2, maximality: `S(ρ) ≤ S(I/d)`.
* `AxQM.State.eq_maximallyMixed_of_vonNeumannEntropy_eq` — part 2, uniqueness:
  `S(ρ) = S(I/d) ⇒ ρ = I/d`.
* `AxQM.State.maximallyMixedState_unique_maxEntropy` — the headline characterization:
  `ρ` maximises the entropy `↔ ρ = I/d`.
-/

open scoped ComplexOrder

noncomputable section

namespace AxQM

/-- **Exercise 11.19, part 1 (physics form).** There is a finite family of unitary evolutions `Uⱼ`
and a probability distribution `pⱼ` such that twirling *any* state `ρ` yields the maximally mixed
state: `∑ⱼ pⱼ Uⱼ ρ Uⱼ† = I/d`.

This is the state-level shadow of the operator identity `∑ⱼ pⱼ Uⱼ A Uⱼ† = tr(A) I/d`
(`LinearIsometryEquiv.exists_conjStarAlgEquiv_oneDesign`): a density operator has unit trace, so the
right-hand side is `I/d`. The witnessing unitaries are the depolarizing `1`-design of the standard
basis, packaged as `Evolution`s via `Evolution.ofLinearIsometryEquiv`. -/
theorem exists_randomUnitary_twirl_eq_maximallyMixed (S : QSystem) [Nontrivial S.space] :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → Evolution S) (p : ι → ℝ)
      (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1),
      ∀ ρ : State S, State.mix p hp hsum (fun i => (U i).evolve ρ) = maximallyMixedState S := by
  obtain ⟨ι, hι, U, p, hp, hsum, hA⟩ :=
    LinearIsometryEquiv.exists_conjStarAlgEquiv_oneDesign (𝕜 := ℂ) (E := S.space)
  refine ⟨ι, hι, fun i => Evolution.ofLinearIsometryEquiv (U i), p, hp, hsum, fun ρ => ?_⟩
  apply State.ext
  rw [State.mix_op, maximallyMixedState_op]
  have htie : ∀ i, (Evolution.ofLinearIsometryEquiv (U i)).toIsometryEquiv = U i := by
    intro i
    ext x
    rw [Evolution.toIsometryEquiv_apply, Evolution.ofLinearIsometryEquiv_op_apply]
  have hstep : ∀ i, ((Evolution.ofLinearIsometryEquiv (U i)).evolve ρ).op
      = (U i).conjStarAlgEquiv ρ.op := by
    intro i
    rw [Evolution.evolve_op_conjStarAlgEquiv, htie i]
  simp_rw [hstep]
  have hA' := hA ρ.op
  rw [State.trace_op_eq_one, one_div] at hA'
  exact hA'

/-- **Exercise 11.19, part 2 (maximality).** The maximally mixed state has the greatest von Neumann
entropy: `S(ρ) ≤ S(I/d)` for every state `ρ`.

Alternate proof via the twirl: writing `I/d = ∑ⱼ pⱼ Uⱼ ρ Uⱼ†`
(`exists_randomUnitary_twirl_eq_maximallyMixed`), concavity of the entropy gives
`S(I/d) ≥ ∑ⱼ pⱼ S(Uⱼ ρ Uⱼ†)`, and unitary invariance `S(Uⱼ ρ Uⱼ†) = S(ρ)` collapses the
right-hand side to `(∑ⱼ pⱼ) S(ρ) = S(ρ)`. -/
theorem State.vonNeumannEntropy_le_maximallyMixed (S : QSystem) [Nontrivial S.space] (ρ : State S) :
    ρ.vonNeumannEntropy ≤ (maximallyMixedState S).vonNeumannEntropy := by
  obtain ⟨ι, hι, U, p, hp, hsum, hmix⟩ := exists_randomUnitary_twirl_eq_maximallyMixed S
  have hpos : IsStrictlyPositive (State.mix p hp hsum (fun i => (U i).evolve ρ)).op := by
    rw [hmix ρ]; exact maximallyMixedState_isStrictlyPositive S
  have hconc := State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix p hp hsum
    (fun i => (U i).evolve ρ) hpos
  rw [hmix ρ] at hconc
  have hent : ∀ i, ((U i).evolve ρ).vonNeumannEntropy = ρ.vonNeumannEntropy :=
    fun i => State.vonNeumannEntropy_evolve (U i) ρ
  simp_rw [hent] at hconc
  rwa [← Finset.sum_mul, hsum, one_mul] at hconc

/-- **Exercise 11.19, part 2 (uniqueness).** If a state attains the maximal entropy `S(I/d)`, it
*is* the maximally mixed state.

Alternate proof via the twirl and *strict* concavity (Exercise 11.18): with
`I/d = ∑ⱼ pⱼ Uⱼ ρ Uⱼ†`, the hypothesis `S(ρ) = S(I/d)` makes the concavity inequality an equality,
so `State.vonNeumannEntropy_mix_eq_sum_iff` forces all the (positive-weight) `Uⱼ ρ Uⱼ†` to coincide.
Their common value equals their mixture `I/d`, so for any single `j`, `Uⱼ ρ Uⱼ† = I/d` and hence
`ρ = Uⱼ† (I/d) Uⱼ = I/d`. -/
theorem State.eq_maximallyMixed_of_vonNeumannEntropy_eq (S : QSystem) [Nontrivial S.space]
    (ρ : State S) (h : ρ.vonNeumannEntropy = (maximallyMixedState S).vonNeumannEntropy) :
    ρ = maximallyMixedState S := by
  obtain ⟨ι, hι, U, p, hp, hsum, hmix⟩ := exists_randomUnitary_twirl_eq_maximallyMixed S
  -- some component carries positive weight (the probabilities sum to `1`)
  obtain ⟨j₀, hj₀⟩ : ∃ i, 0 < p i := by
    by_contra hc
    simp only [not_exists, not_lt] at hc
    exact one_ne_zero (hsum ▸ Finset.sum_eq_zero fun i _ => le_antisymm (hc i) (hp i))
  have hpos : IsStrictlyPositive (State.mix p hp hsum (fun i => (U i).evolve ρ)).op := by
    rw [hmix ρ]; exact maximallyMixedState_isStrictlyPositive S
  -- equality in concavity, from `S(ρ) = S(I/d)` and unitary invariance
  have heq : (State.mix p hp hsum (fun i => (U i).evolve ρ)).vonNeumannEntropy
      = ∑ i, p i * ((U i).evolve ρ).vonNeumannEntropy := by
    have hent : ∀ i, ((U i).evolve ρ).vonNeumannEntropy = ρ.vonNeumannEntropy :=
      fun i => State.vonNeumannEntropy_evolve (U i) ρ
    rw [hmix ρ]
    simp_rw [hent]
    rw [← Finset.sum_mul, hsum, one_mul, ← h]
  -- strict concavity: all positive-weight components are equal
  have hall := (State.vonNeumannEntropy_mix_eq_sum_iff p hp hsum
    (fun i => (U i).evolve ρ) hpos).mp heq
  -- hence the mixture equals the single component `j₀`, which is therefore `I/d`
  have hj₀eq : (U j₀).evolve ρ = maximallyMixedState S := by
    rw [← hmix ρ]
    exact (State.mix_eq_of_forall_pos_eq p hp hsum _ _ fun j hj => hall j j₀ hj hj₀).symm
  -- invert the unitary conjugation to recover `ρ`
  have := (U j₀).evolve_adjoint_evolve ρ
  rw [hj₀eq, Evolution.evolve_maximallyMixedState] at this
  exact this.symm

/-- **Exercise 11.19 (headline): the completely mixed state `I/d` is the unique state of maximal
von Neumann entropy.** A state `ρ` maximises the entropy — `S(σ) ≤ S(ρ)` for all `σ` — **iff** it is
the maximally mixed state `I/d`.

Combines `State.vonNeumannEntropy_le_maximallyMixed` (`I/d` is a maximiser) with
`State.eq_maximallyMixed_of_vonNeumannEntropy_eq` (a maximiser matching `S(I/d)` must be `I/d`). -/
theorem State.maximallyMixedState_unique_maxEntropy (S : QSystem) [Nontrivial S.space]
    (ρ : State S) :
    (∀ σ : State S, σ.vonNeumannEntropy ≤ ρ.vonNeumannEntropy) ↔ ρ = maximallyMixedState S := by
  constructor
  · intro hmax
    exact State.eq_maximallyMixed_of_vonNeumannEntropy_eq S ρ
      (le_antisymm (State.vonNeumannEntropy_le_maximallyMixed S ρ)
        (hmax (maximallyMixedState S)))
  · rintro rfl
    exact fun σ => State.vonNeumannEntropy_le_maximallyMixed S σ

end AxQM
