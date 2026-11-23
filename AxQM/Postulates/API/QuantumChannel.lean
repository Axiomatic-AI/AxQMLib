/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.StateSpace
import ToMathlib.Analysis.InnerProductSpace.OperatorSumCP
import ToMathlib.Analysis.InnerProductSpace.OperatorSumTheorem
import ToMathlib.Analysis.InnerProductSpace.OperatorSumComposition

/-!
# AxQM.Postulates.API — quantum channels (CPTP maps on states)

A **quantum channel** is the completely-positive trace-preserving (CPTP) evolution of an open
quantum system: the trace-preserving special case of a Nielsen & Chuang *quantum operation*
(Chapter 8). Abstractly it is a linear superoperator `Φ` on operators that is completely positive
(N&C axiom A3) and trace-preserving (`tr Φ(A) = tr A`, N&C's trace condition with *equality* — a
deterministic process, no measurement outcome discarded). By the operator-sum representation
theorem (N&C Theorem 8.1) such a `Φ` is exactly one of the form `ρ ↦ ∑ₖ Eₖ ρ Eₖ†` with the
**completeness relation** `∑ₖ Eₖ† Eₖ = I`.

* `AxQM.IsChannel` — the predicate on a state-map `f : State S → State S` saying `f` is a
  quantum channel: it is the restriction to states of a completely-positive, trace-preserving
  linear superoperator `Φ` on `S.space`. This is the object that Nielsen & Chuang's "unital
  channel" of **Problem 8.3** quantifies over — the hypothesis of the qubit converse ("every unital
  qubit channel is random-unitary") and the existential of the higher-dimensional counterexample.
* `AxQM.isChannel_of_kraus` — the **operator-sum ⟹ channel** constructor (the
  trace-preserving direction of N&C Theorem 8.1): a Kraus family `E` whose operation elements obey
  the completeness relation `∑ₖ Eₖ† Eₖ = 1` realises a channel. Complete positivity is
  `krausSumₗ_isCompletelyPositive` (unconditional); trace preservation is `trace_krausSumₗ`
  (`tr(∑ₖ Eₖ ρ Eₖ†) = tr((∑ₖ Eₖ† Eₖ) ρ) = tr ρ`) using the completeness relation. This is the
  standard way to exhibit a concrete channel (random-unitary averages, the Werner–Holevo channel,
  …) and is reused in both parts of Problem 8.3.

`IsChannel` is phrased in terms of the density operator `State.op`, operators
`S.space →L[ℂ] S.space`, and `LinearMap.trace`, complete positivity and the operator-sum map
`krausSumₗ`, exactly like `maximallyMixedState`, `RandomUnitaryChannel`, and the ensemble mixture.

## Design notes

* **Why a predicate on `State S → State S`, not a bundled `Φ`.** The companion predicates
  `IsUnital` and `IsRandomUnitary` (Problem 8.3) are already phrased on `f : State S → State S`, so
  keeping `IsChannel` in the same shape lets Problem 8.3's claims read uniformly
  (`IsChannel f → IsUnital f → IsRandomUnitary f`, and `∃ f, IsChannel f ∧ IsUnital f ∧
  ¬ IsRandomUnitary f`). The *linear* superoperator `Φ` — which carries the completely-positive /
  trace-preserving content that a bare `State → State` map cannot — is existentially bundled: a
  state-map is a channel exactly when *some* CPTP `Φ` restricts to it.
* **Why CP + trace-preserving abstractly (not "has an operator-sum with `∑ Eₖ†Eₖ = 1`").** Both are
  equivalent by N&C Theorem 8.1, but the abstract CPTP form is the definitional meaning of
  "channel" and privileges no particular Kraus representation; the operator-sum direction is
  supplied as the constructor `isChannel_of_kraus`, which is what one uses to *build* a channel.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A quantum channel (CPTP map) on the states of `S`.** A state-map `f : State S → State S` is a
**channel** when it is the restriction to states of a linear superoperator `Φ` on the operators of
`S.space` that is

* **completely positive** (`ContinuousLinearMap.IsCompletelyPositive`, Nielsen & Chuang axiom A3),
  and
* **trace-preserving**, `tr Φ(A) = tr A` for every operator `A` (N&C's trace condition with
  equality — the process is deterministic).

i.e. `(f ρ).op = Φ ρ.op` for every state `ρ`. This is Nielsen & Chuang's *trace-preserving quantum
operation*; by the operator-sum representation theorem (N&C Theorem 8.1) it is equivalently a map
`ρ ↦ ∑ₖ Eₖ ρ Eₖ†` with `∑ₖ Eₖ† Eₖ = I` (see `isChannel_of_kraus`). It is the object over which
**Problem 8.3**'s "unital channel" ranges. -/
def IsChannel (f : State S → State S) : Prop :=
  ∃ Φ : (S.space →L[ℂ] S.space) →ₗ[ℂ] (S.space →L[ℂ] S.space),
    ContinuousLinearMap.IsCompletelyPositive Φ ∧
    (∀ A : S.space →L[ℂ] S.space,
      LinearMap.trace ℂ S.space ↑(Φ A) = LinearMap.trace ℂ S.space ↑A) ∧
    ∀ ρ : State S, (f ρ).op = Φ ρ.op

/-- **Operator-sum ⟹ channel** — the trace-preserving direction of Nielsen & Chuang Theorem 8.1.
If a finite family of operation elements `E : ι → S.space →L[ℂ] S.space` obeys the **completeness
relation** `∑ₖ Eₖ† Eₖ = I`, then any state-map `f` acting as the operator sum
`(f ρ).op = ∑ₖ Eₖ ρ Eₖ†` is a quantum channel. The witnessing superoperator is the Kraus map
`krausSumₗ E`: it is completely
positive unconditionally (`krausSumₗ_isCompletelyPositive`) and trace-preserving because
`tr(∑ₖ Eₖ ρ Eₖ†) = tr((∑ₖ Eₖ† Eₖ) ρ) = tr(I ρ) = tr ρ` (`trace_krausSumₗ` with the completeness
relation). This is the constructor used to exhibit concrete channels. -/
theorem isChannel_of_kraus {ι : Type*} [Fintype ι]
    (E : ι → S.space →L[ℂ] S.space)
    (hE : ∑ i, (ContinuousLinearMap.adjoint (E i)).comp (E i) = 1)
    {f : State S → State S}
    (hf : ∀ ρ : State S, (f ρ).op = ContinuousLinearMap.krausSumₗ E ρ.op) :
    IsChannel f := by
  refine ⟨ContinuousLinearMap.krausSumₗ E,
    ContinuousLinearMap.krausSumₗ_isCompletelyPositive E, ?_, hf⟩
  intro A
  rw [ContinuousLinearMap.trace_krausSumₗ, hE, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp]

/-- **A trace-preserving Kraus family gives a quantum channel** — the existence companion of
`isChannel_of_kraus`. If a finite family of operation elements `E : ι → S.space →L[ℂ] S.space` obeys
the completeness relation `∑ₖ Eₖ† Eₖ = I`, then the state-map `ρ ↦ ∑ₖ Eₖ ρ Eₖ†` exists as a genuine
quantum channel (`IsChannel`): the operator sum sends a density operator to a density operator
(`ContinuousLinearMap.isDensityOp_krausSumₗ`), defining the map on `State S`, and it is a channel by
`isChannel_of_kraus`. Use this to *construct* a channel from a completeness-satisfying Kraus family
(e.g. the recovery of N&C Theorem 10.1), rather than being handed the state-map. -/
theorem exists_isChannel_of_completeness {ι : Type*} [Fintype ι]
    (E : ι → S.space →L[ℂ] S.space)
    (hE : ∑ i, (ContinuousLinearMap.adjoint (E i)).comp (E i) = 1) :
    ∃ f : State S → State S,
      IsChannel f ∧ ∀ ρ : State S, (f ρ).op = ContinuousLinearMap.krausSumₗ E ρ.op :=
  ⟨fun ρ => ⟨ContinuousLinearMap.krausSumₗ E ρ.op,
      ContinuousLinearMap.isDensityOp_krausSumₗ E hE ρ.isDensity⟩,
    isChannel_of_kraus E hE fun _ => rfl, fun _ => rfl⟩

/-- **Quantum channels are closed under composition.** If `f` and `g` are quantum channels of the
system `S` (`IsChannel`), then so is their composite `f ∘ g`, `fun ρ ↦ f (g ρ)` — the first
argument `f` being the *outer* map, matching the convention of `isRandomUnitary_comp` and
`RandomUnitaryChannel.comp` (whose action is `C.apply (D.apply ρ)`). The witnessing superoperator is
`Φ_f ∘ₗ Φ_g`: it is trace-preserving because each factor is (`tr Φ_f(Φ_g A) = tr Φ_g A = tr A`), and
it is completely positive by the **composition of quantum operations** (Nielsen & Chuang,
Exercise 8.6): each factor is a quantum operation (`SatisfiesOperationAxioms`, being completely
positive and — since trace-*preserving* — trace-non-increasing), hence has a Kraus representation
(the operator-sum theorem, N&C Theorem 8.1,
`ContinuousLinearMap.satisfiesOperationAxioms_iff_isOperatorSum`), and the composite of two
operator-sum maps is again a quantum operation
(`ContinuousLinearMap.IsOperatorSum.comp_satisfiesAxioms`, Kraus family the products `{Fⱼ Eᵢ}`);
its completeness gives the complete positivity of `Φ_f ∘ₗ Φ_g`.

This is the State-level companion of Exercise 8.6 (whose formal core, the composition of
operator-sum maps, is in `ToMathlib/`). It is the closure property the qubit converse of
**Problem 8.3** uses to *diagonalise* a unital qubit channel: conjugating a channel by the unitary
rotations realising the singular-value rotations `O₁, O₂` of its Bloch matrix — unitary
conjugations are themselves channels — yields a channel with diagonal Bloch action, on which the
complete-positivity (Fujiwara–Algoet) analysis is carried out. -/
theorem isChannel_comp {f g : State S → State S} (hf : IsChannel f) (hg : IsChannel g) :
    IsChannel (fun ρ => f (g ρ)) := by
  obtain ⟨Φf, hΦfCP, hΦfTP, hfop⟩ := hf
  obtain ⟨Φg, hΦgCP, hΦgTP, hgop⟩ := hg
  -- Each factor is a quantum operation (CP + trace-non-increasing, the latter from
  -- trace-preservation), hence has a Kraus representation by the operator-sum theorem.
  obtain ⟨_, _, E, hE⟩ :=
    (ContinuousLinearMap.satisfiesOperationAxioms_iff_isOperatorSum Φg).mp
      ⟨hΦgCP, fun ρ _ => le_of_eq (by rw [hΦgTP ρ])⟩
  obtain ⟨_, _, F, hF⟩ :=
    (ContinuousLinearMap.satisfiesOperationAxioms_iff_isOperatorSum Φf).mp
      ⟨hΦfCP, fun ρ _ => le_of_eq (by rw [hΦfTP ρ])⟩
  -- The composite is a quantum operation (Exercise 8.6); take its completely-positive component.
  refine ⟨Φf ∘ₗ Φg, (hE.comp_satisfiesAxioms hF).1, ?_, ?_⟩
  · intro A
    rw [LinearMap.comp_apply, hΦfTP (Φg A), hΦgTP A]
  · intro ρ
    rw [hfop, hgop, LinearMap.comp_apply]

end AxQM
