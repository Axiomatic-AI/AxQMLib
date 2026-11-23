/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.API.ProjectiveMeasurement
import AxQM.Postulates.API.UnreadMeasurement

/-!
# AxQM — projective-measurement-then-conditional-unitary recovery (N&C Problem 10.1(2))

Nielsen & Chuang, Problem 10.1(2) assumes an error-correction procedure performed as *a projective
measurement followed by a conditional unitary operation* and asks how to turn one for a channel `E₁`
into one for an equivalent channel `E₂ = U ∘ E₁ ∘ V`. This file supplies the vocabulary for that
recovery form and the algebraic identity behind the transfer; the statements (`Corrects`,
`corrects_of_channelEquiv`, `corrects_conjugate`) are in `AxQM/NC/Ch10/Problem10_1.lean`.

A recovery of this form is a syndrome **measurement** `{Mᵢ}` (projective — the `Mᵢ` are orthogonal
projectors, `Measurement.IsProjective`) together with conditional **unitary** corrections `{Wᵢ}`;
its action on a state is

  `R(ρ) = ∑ᵢ Wᵢ Mᵢ ρ Mᵢ† Wᵢ†`,

a genuine CPTP channel (the operator sum with Kraus operators `Wᵢ Mᵢ`, whose completeness
`∑ᵢ Mᵢ† Wᵢ† Wᵢ Mᵢ = ∑ᵢ Mᵢ† Mᵢ = 1` uses only unitarity of the `Wᵢ`). It is exactly the unread
post-measurement state `Measurement.unreadState` of the measurement whose operators are `Wᵢ Mᵢ`
(`Measurement.conjUnitary`), so it is a `State` for free.

## Contents

* `ContinuousLinearMap.krausSumₗ_conj` — the general operator identity
  `∑ᵢ (B Eᵢ A) τ (B Eᵢ A)† = B (∑ᵢ Eᵢ (A τ A†) Eᵢ†) B†`: pre- and post-composing a Kraus family by
  fixed operators `A`, `B` conjugates its operator-sum map. Pure operator mathematics, the engine of
  `apply_conjugate`.
* `AxQM.Measurement.conj` — conjugate a measurement by a unitary, `Mᵢ ↦ U Mᵢ U†`; and
  `AxQM.Measurement.IsProjective.conj` — this preserves projectivity (a unitary conjugate
  of an orthogonal projector is an orthogonal projector), so the transformed syndrome is again a
  projective measurement.
* `AxQM.Measurement.conjUnitary` — pre-compose each operator by a unitary, `Mᵢ ↦ Wᵢ Mᵢ`;
  the operators of the recovery `R` (its `unreadState` is `R`).
* `AxQM.ProjectiveUnitaryRecovery` — the bundled recovery: a projective syndrome
  measurement plus conditional unitaries; `apply` its channel action; `conjugate U V` the
  transformed recovery with syndrome `{U Mᵢ U†}` and corrections `{V† Wᵢ U†}`; and
  `apply_conjugate`, the identity `(R.conjugate U V).apply = V† ∘ R.apply ∘ U†` at the heart of the
  transfer.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

/-- **Conjugating a Kraus family conjugates its operator-sum map.** For fixed operators `A`, `B` and
a Kraus family `E`, pre-composing each `Eᵢ` by `A` and post-composing by `B`,

  `∑ᵢ (B Eᵢ A) τ (B Eᵢ A)† = B (∑ᵢ Eᵢ (A τ A†) Eᵢ†) B†`,

i.e. the operator-sum map of `{B Eᵢ A}` at `τ` equals
`B · (operator-sum map of {Eᵢ} at A τ A†) · B†`. Pure operator mathematics (each side is the same
sum after distributing the outer `B (·) B†` and pushing the adjoints through the products),
independent of any completeness relation. This is the engine turning
`V† ∘ (∑ᵢ Wᵢ Mᵢ · Mᵢ† Wᵢ†) ∘ U†` into a single operator-sum recovery in
`ProjectiveUnitaryRecovery.apply_conjugate`. General `ContinuousLinearMap.krausSumₗ` operator
algebra (compare `ContinuousLinearMap.isDensityOp_krausSumₗ` and
`ContinuousLinearMap.krausSumₗ_comp`). -/
theorem ContinuousLinearMap.krausSumₗ_conj {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {κ : Type*} [Fintype κ] (E : κ → H →L[ℂ] H)
    (A B τ : H →L[ℂ] H) :
    (krausSumₗ fun i => B.comp ((E i).comp A)) τ
      = B.comp (((krausSumₗ E) (A.comp (τ.comp (adjoint A)))).comp (adjoint B)) := by
  rw [krausSumₗ_apply, krausSumₗ_apply, ContinuousLinearMap.finsetSum_comp,
      ContinuousLinearMap.comp_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint, star_mul,
    mul_assoc]

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- **Unitary cancellation on the state operators** `U† (U X) = X`: pre-multiplying by `U.op` and
then by its adjoint `U† = star U.op` cancels, since `U† U = 1` (`Evolution.adjoint_comp_self`). The
shared workhorse of the completeness / projectivity / conjugation proofs below, where a `U† U`
appears in the middle of an operator product. -/
theorem Evolution.star_op_mul_cancel (U : Evolution S) (X : S.space →L[ℂ] S.space) :
    star U.op * (U.op * X) = X := by
  have h : star U.op * U.op = 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
    exact U.adjoint_comp_self
  rw [← mul_assoc, h, one_mul]

namespace Measurement

/-- **Conjugating a measurement by a unitary evolution** `U`: the measurement with operators
`Mᵢ ↦ U Mᵢ U†`. Still a measurement — the completeness relation is conjugated,
`∑ᵢ (U Mᵢ U†)† (U Mᵢ U†) = U (∑ᵢ Mᵢ† Mᵢ) U† = U · 1 · U† = 1` (unitarity `U† U = U U† = 1`). This is
the syndrome measurement of the recovery for `E₂ = U ∘ E₁ ∘ V` obtained from that for `E₁`. -/
def conj (m : Measurement ι S) (U : Evolution S) : Measurement ι S where
  op i := U.op.comp ((m.op i).comp (adjoint U.op))
  complete := by
    have hUU' : U.op * adjoint U.op = 1 := by
      rw [ContinuousLinearMap.mul_def]; exact U.comp_adjoint_self
    have key : ∀ i, (adjoint (U.op.comp ((m.op i).comp (adjoint U.op)))).comp
          (U.op.comp ((m.op i).comp (adjoint U.op)))
        = U.op.comp (((adjoint (m.op i)).comp (m.op i)).comp (adjoint U.op)) := by
      intro i
      simp only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint, star_mul,
        star_star, mul_assoc]
      simp only [Evolution.star_op_mul_cancel]
    rw [Finset.sum_congr rfl fun i _ => key i, ← ContinuousLinearMap.comp_finsetSum,
        ← ContinuousLinearMap.finsetSum_comp, m.complete]
    simp only [← ContinuousLinearMap.mul_def, one_mul]
    exact hUU'

/-- The operators of a unitary-conjugated measurement: `(m.conj U).op i = U Mᵢ U†`. -/
@[simp] theorem conj_op (m : Measurement ι S) (U : Evolution S) (i : ι) :
    (m.conj U).op i = U.op.comp ((m.op i).comp (adjoint U.op)) := rfl

/-- **A unitary conjugate of a projective measurement is projective.** Conjugating an orthogonal
projector `Mᵢ` by a unitary `U` gives the orthogonal projector `U Mᵢ U†` (self-adjoint:
`(U Mᵢ U†)† = U Mᵢ† U† = U Mᵢ U†`; idempotent: `(U Mᵢ U†)² = U Mᵢ (U† U) Mᵢ U† = U Mᵢ U†`), so the
conjugated syndrome measurement is again a projective measurement — the transferred procedure is "in
the same fashion". -/
theorem IsProjective.conj {m : Measurement ι S} (h : m.IsProjective) (U : Evolution S) :
    (m.conj U).IsProjective := by
  intro i
  rw [conj_op]
  refine ⟨?_, ?_⟩
  · -- idempotent: `(U Mᵢ U†)(U Mᵢ U†) = U Mᵢ U†`
    have hidem : m.op i * m.op i = m.op i := (h i).isIdempotentElem
    change (U.op.comp ((m.op i).comp (adjoint U.op))) * (U.op.comp ((m.op i).comp (adjoint U.op)))
        = U.op.comp ((m.op i).comp (adjoint U.op))
    simp only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint, mul_assoc]
    simp only [Evolution.star_op_mul_cancel]
    rw [← mul_assoc (m.op i) (m.op i), hidem]
  · -- self-adjoint: `(U Mᵢ U†)† = U Mᵢ U†`
    have hsa : star (m.op i) = m.op i := (h i).isSelfAdjoint.star_eq
    change star (U.op.comp ((m.op i).comp (adjoint U.op)))
        = U.op.comp ((m.op i).comp (adjoint U.op))
    simp only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint, star_mul,
      star_star, hsa, mul_assoc]

/-- **Pre-composing each measurement operator by a unitary** `Wᵢ`: the measurement with operators
`Mᵢ ↦ Wᵢ Mᵢ`. Still a measurement — `∑ᵢ (Wᵢ Mᵢ)† (Wᵢ Mᵢ) = ∑ᵢ Mᵢ† Wᵢ† Wᵢ Mᵢ = ∑ᵢ Mᵢ† Mᵢ = 1`
(unitarity `Wᵢ† Wᵢ = 1`). Its unread post-measurement state `Σᵢ Wᵢ Mᵢ ρ Mᵢ† Wᵢ†` is the action
of the recovery `ProjectiveUnitaryRecovery.apply`. -/
def conjUnitary (m : Measurement ι S) (W : ι → Evolution S) : Measurement ι S where
  op i := (W i).op.comp (m.op i)
  complete := by
    have key : ∀ i, (adjoint ((W i).op.comp (m.op i))).comp ((W i).op.comp (m.op i))
        = (adjoint (m.op i)).comp (m.op i) := by
      intro i
      simp only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint, star_mul,
        mul_assoc]
      simp only [Evolution.star_op_mul_cancel]
    rw [Finset.sum_congr rfl fun i _ => key i]
    exact m.complete

/-- The operators of `conjUnitary`: `(m.conjUnitary W).op i = Wᵢ Mᵢ`. -/
@[simp] theorem conjUnitary_op (m : Measurement ι S) (W : ι → Evolution S) (i : ι) :
    (m.conjUnitary W).op i = (W i).op.comp (m.op i) := rfl

end Measurement

/-- **A projective-measurement-then-conditional-unitary recovery** (Nielsen & Chuang, Problem
10.1(2)): a projective syndrome **measurement** `meas` (`Measurement.IsProjective`) together with a
family of conditional **unitary** corrections `corr`. Its action on a state (`apply`) is
`R(ρ) = ∑ᵢ Wᵢ Mᵢ ρ Mᵢ† Wᵢ†` — measure the syndrome `{Mᵢ}`, then apply the correction `Wᵢ`
conditioned on the outcome. This is the concrete form N&C assumes the error-correction procedure
takes. -/
structure ProjectiveUnitaryRecovery (ι : Type*) [Fintype ι] (S : QSystem) where
  /-- The syndrome measurement. -/
  meas : Measurement ι S
  /-- The syndrome measurement is projective (its operators are orthogonal projectors). -/
  proj : meas.IsProjective
  /-- The conditional unitary corrections `Wᵢ`, one per measurement outcome. -/
  corr : ι → Evolution S

namespace ProjectiveUnitaryRecovery

variable (R : ProjectiveUnitaryRecovery ι S)

/-- **The action of a projective-unitary recovery** `R(ρ) = ∑ᵢ Wᵢ Mᵢ ρ Mᵢ† Wᵢ†`: measure the
syndrome `{Mᵢ}`, then apply the conditional unitary `Wᵢ`. It is the unread (non-selective)
post-measurement state (`Measurement.unreadState`) of the measurement with operators `Wᵢ Mᵢ`
(`Measurement.conjUnitary`), hence a genuine `State` and a CPTP channel. -/
def apply (ρ : State S) : State S := (R.meas.conjUnitary R.corr).unreadState ρ

/-- The operator of `R.apply ρ` is the Kraus sum `∑ᵢ Wᵢ Mᵢ ρ Mᵢ† Wᵢ†`. -/
@[simp] theorem apply_op (ρ : State S) :
    (R.apply ρ).op = krausSumₗ (R.meas.conjUnitary R.corr).op ρ.op := rfl

/-- **The recovery transformed for an equivalent channel** `E₂ = U ∘ E₁ ∘ V`: syndrome measurement
`{U Mᵢ U†}` (`Measurement.conj`) and conditional unitaries `{V† Wᵢ U†}`. Projectivity of the new
syndrome is `Measurement.IsProjective.conj`. This is the recovery for `E₂` obtained from the one for
`E₁`, still "a projective measurement followed by a conditional unitary". -/
def conjugate (U V : Evolution S) : ProjectiveUnitaryRecovery ι S where
  meas := R.meas.conj U
  proj := R.proj.conj U
  corr i := V.adjoint.comp ((R.corr i).comp U.adjoint)

@[simp] theorem conjugate_meas (U V : Evolution S) : (R.conjugate U V).meas = R.meas.conj U := rfl

@[simp] theorem conjugate_corr (U V : Evolution S) (i : ι) :
    (R.conjugate U V).corr i = V.adjoint.comp ((R.corr i).comp U.adjoint) := rfl

/-- **The transformed recovery is `V† ∘ R ∘ U†`.** The recovery `(R.conjugate U V).apply` for the
equivalent channel acts as: undo the trailing `U` (`U†`), run the original recovery `R`, then undo
the leading `V` (`V†`):

  `(R.conjugate U V).apply σ = V† (R.apply (U† σ U)) V`.

Proved at the operator level: both sides are the operator sum `∑ᵢ (V† Wᵢ Mᵢ U†) σ (V† Wᵢ Mᵢ U†)†`,
using `krausSumₗ_conj` to conjugate the Kraus family and the cancellation `U† U = 1` to collapse the
new syndrome/correction operators `V† Wᵢ U† · U Mᵢ U† = V† Wᵢ Mᵢ U†`. Combined with the abstract
transfer `corrects_of_channelEquiv`, this yields that the transformed recovery corrects `E₂`. -/
theorem apply_conjugate (U V : Evolution S) (σ : State S) :
    (R.conjugate U V).apply σ = V.adjoint.evolve (R.apply (U.adjoint.evolve σ)) := by
  apply State.ext
  have hfam : ((R.conjugate U V).meas.conjUnitary (R.conjugate U V).corr).op
      = fun i => (adjoint V.op).comp (((R.meas.conjUnitary R.corr).op i).comp (adjoint U.op)) := by
    funext i
    simp only [conjugate_meas, conjugate_corr, Measurement.conjUnitary_op, Measurement.conj_op,
      Evolution.comp_op, Evolution.adjoint_op, ← ContinuousLinearMap.mul_def,
      ← ContinuousLinearMap.star_eq_adjoint, mul_assoc]
    simp only [Evolution.star_op_mul_cancel]
  rw [apply_op, hfam, krausSumₗ_conj (R.meas.conjUnitary R.corr).op (adjoint U.op) (adjoint V.op)]
  simp only [Evolution.evolve_op, apply_op, Evolution.adjoint_op,
    ContinuousLinearMap.adjoint_adjoint]

end ProjectiveUnitaryRecovery

end AxQM
