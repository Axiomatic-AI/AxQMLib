/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Measurement

/-!
# AxQM — the cascade of two measurements (N&C Exercise 2.57)

The **cascade** construction `L.cascade M`: given a measurement `L` (outcomes `κ`) and a
measurement `M` (outcomes `μ`), the composite that measures `L` and then `M` is itself a single
measurement with outcome set `κ × μ` and operators

  `N₍ₗ,ₘ₎ = Mₘ Lₗ`   (Nielsen–Chuang Exercise 2.57).

Completeness of the composite family is exactly the two given completeness relations chained:
`∑₍ₗ,ₘ₎ N₍ₗ,ₘ₎† N₍ₗ,ₘ₎ = ∑ₗ Lₗ† (∑ₘ Mₘ† Mₘ) Lₗ = ∑ₗ Lₗ† Lₗ = 1`, so `cascade` produces a genuine
`Measurement (κ × μ) S` — this is the exercise's construction. The two physical-equivalence
statements (the joint Born probability factorizes as `p(l,m) = p(l)·p(m∣l)`, and the cascade
post-measurement state equals the sequential one) are the theorems in
`AxQM/NC/Ch2/Exercise2_57.lean`, built on the identities here.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {κ μ : Type*} [Fintype κ] [Fintype μ] {S : QSystem}

namespace Measurement

/-- The **cascade** of two measurements `L` (outcomes `κ`) and `M` (outcomes `μ`): the single
measurement with outcome set `κ × μ` whose operator for outcome `(l, m)` is `N₍ₗ,ₘ₎ = Mₘ Lₗ`
(Nielsen–Chuang Exercise 2.57). Completeness `∑₍ₗ,ₘ₎ N₍ₗ,ₘ₎† N₍ₗ,ₘ₎ = 1` chains the completeness
relations of `M` and `L`. -/
def cascade (L : Measurement κ S) (M : Measurement μ S) : Measurement (κ × μ) S where
  op p := (M.op p.2).comp (L.op p.1)
  complete := by
    rw [← L.complete, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hsummand : ∀ m : μ,
        (adjoint ((M.op m).comp (L.op l))).comp ((M.op m).comp (L.op l))
          = (adjoint (L.op l)).comp (((adjoint (M.op m)).comp (M.op m)).comp (L.op l)) :=
      fun m => by rw [adjoint_comp, comp_assoc, comp_assoc]
    simp only [hsummand]
    rw [← ContinuousLinearMap.comp_finsetSum, ← ContinuousLinearMap.finsetSum_comp, M.complete,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

@[simp]
theorem cascade_op (L : Measurement κ S) (M : Measurement μ S) (l : κ) (m : μ) :
    (L.cascade M).op (l, m) = (M.op m).comp (L.op l) := rfl

/-- The post-measurement operation of the cascade factors through the two individual
post-measurement operations: `E₍ₗ,ₘ₎(ρ) = Mₘ Lₗ ρ Lₗ† Mₘ† = Eₘ(Eₗ(ρ))`. The identity
underlying both physical-equivalence theorems. -/
theorem postOp_cascade (L : Measurement κ S) (M : Measurement μ S) (ρ : S →L[ℂ] S) (l : κ) (m : μ) :
    ContinuousLinearMap.postOp (L.cascade M).op ρ (l, m)
      = ContinuousLinearMap.postOp M.op (ContinuousLinearMap.postOp L.op ρ l) m := by
  simp only [ContinuousLinearMap.postOp, cascade_op, adjoint_comp, comp_assoc]

/-! ### Outcome-operator congruence

Both the Born probability (Postulate 3) and the post-measurement collapse (Postulate 4) are
functions of a *single* outcome's measurement operator `Mᵢ`. Hence two measurements — even over
different outcome sets — that share an outcome operator assign that outcome identical statistics
and identical collapses. These general congruences are exactly what makes "two measurements whose
operators agree up to a relabeling of outcomes are physically equivalent" (e.g. Nielsen–Chuang
Exercise 10.3) a one-line consequence of an operator identity. -/

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- **Born probabilities depend only on the outcome operator.** If two measurements have the same
operator at a pair of outcomes (`m₁.op i = m₂.op j`), those outcomes have equal Born probability in
every state. -/
theorem bornProb_congr {m₁ : Measurement ι₁ S} {m₂ : Measurement ι₂ S} {i : ι₁} {j : ι₂}
    (h : m₁.op i = m₂.op j) (ρ : State S) : m₁.bornProb ρ i = m₂.bornProb ρ j := by
  rw [Measurement.bornProb_eq_re_trace_postOp, Measurement.bornProb_eq_re_trace_postOp,
    ContinuousLinearMap.postOp, ContinuousLinearMap.postOp, h]

/-- **Post-measurement states depend only on the outcome operator.** If two measurements have the
same operator at a pair of (possible) outcomes, those outcomes collapse every state identically. -/
theorem postMeasurement_congr {m₁ : Measurement ι₁ S} {m₂ : Measurement ι₂ S} {i : ι₁} {j : ι₂}
    (h : m₁.op i = m₂.op j) (ρ : State S) (hi : m₁.bornProb ρ i ≠ 0) (hj : m₂.bornProb ρ j ≠ 0) :
    m₁.postMeasurement ρ i hi = m₂.postMeasurement ρ j hj := by
  apply State.ext
  rw [Measurement.postMeasurement_op, Measurement.postMeasurement_op,
    ContinuousLinearMap.postState, ContinuousLinearMap.postState, ContinuousLinearMap.postOp,
    ContinuousLinearMap.postOp, h]

end Measurement

end AxQM
