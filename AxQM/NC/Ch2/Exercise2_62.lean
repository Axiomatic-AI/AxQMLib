/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ProjectiveMeasurement

/-!
# Nielsen & Chuang, Exercise 2.62 (self-POVM measurements are projective)

Show any measurement where measurement operators and POVM elements coincide is projective.

A general measurement (Postulate 3 / §2.2.3) has an induced POVM with effects `Eᵢ = Mᵢ† Mᵢ`
(`Measurement.toPOVM`). The exercise's hypothesis "the measurement operators and the POVM elements
coincide" is the predicate `Measurement.IsSelfPOVM` (`∀ i, Mᵢ = Eᵢ`), and "is a projective
measurement" is `Measurement.IsProjective` — N&C §2.2.5's orthogonal projectors
`Pₘ Pₘ' = δₘₘ' Pₘ` with `∑ₘ Pₘ = I` (both predicates and their structural facts are in
`AxQM/Postulates/API/ProjectiveMeasurement.lean`).

The theorem `Measurement.isProjective_of_isSelfPOVM` states that `IsSelfPOVM` implies
`IsProjective`.

**The mathematics.** Write `A = Mᵢ`. The hypothesis is `A = A† A`. Then:
* `A` is **self-adjoint**: `A† A` is always self-adjoint (`IsSelfAdjoint.star_mul_self`), and
  `A = A† A`, so `A† = A`.
* `A` is **idempotent**: `A A = A† A` (using `A† = A`) `= A` (the hypothesis). So `A² = A`, and `A`
  is a star projection — an orthogonal projector, N&C's `Pₘ`.
Hence every operator is a projector, which is exactly `Measurement.IsProjective`. Mutual
orthogonality `Mᵢ Mⱼ = 0` (`i ≠ j`) and the resolution of the identity `∑ᵢ Mᵢ = 1` are then
automatic for a measurement built from projectors, and are the derived theorems
`Measurement.IsProjective.orthogonal` and `Measurement.IsProjective.sum_op_eq_one`. Together the
conclusion and these two corollaries are exactly N&C's definition of a projective measurement
(`Pₘ Pₘ' = δₘₘ' Pₘ`, `∑ₘ Pₘ = I`), so the measurement is projective.

No weakening: the statement holds for an arbitrary finite outcome set `ι` on any system `S`, and
the projective structure delivered — orthogonal projectors (`IsProjective`) that are pairwise
orthogonal (`IsProjective.orthogonal`) and resolve the identity (`IsProjective.sum_op_eq_one`) — is
the full N&C definition, not merely that each operator is a projector.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- **N&C Exercise 2.62.** A measurement whose measurement operators coincide with their POVM
elements (`Mᵢ = Eᵢ = Mᵢ† Mᵢ`, i.e. `Measurement.IsSelfPOVM`) is a projective measurement
(`Measurement.IsProjective`): every `Mᵢ` is an orthogonal projector. The hypothesis `Mᵢ = Mᵢ† Mᵢ`
forces `Mᵢ` to be self-adjoint (`Mᵢ† Mᵢ` always is) and then idempotent, i.e. a star projection.
The rest of N&C §2.2.5's projective structure then follows as derived theorems: distinct operators
are orthogonal (`IsProjective.orthogonal`) and the operators resolve the identity
(`IsProjective.sum_op_eq_one`) — together, `Pₘ Pₘ' = δₘₘ' Pₘ` and `∑ₘ Pₘ = I`. -/
theorem Measurement.isProjective_of_isSelfPOVM (m : Measurement ι S) (h : m.IsSelfPOVM) :
    m.IsProjective := by
  -- `m.IsProjective` is defeq `∀ i, IsStarProjection (m.op i)`, so `intro i` works on the goal.
  intro i
  -- `Mᵢ = Mᵢ† Mᵢ`, written with `star`/`*`.
  have hi : m.op i = star (m.op i) * m.op i := by
    have he := h i
    rw [Measurement.toPOVM_elements, ← ContinuousLinearMap.mul_def,
      ← ContinuousLinearMap.star_eq_adjoint] at he
    exact he
  -- self-adjoint: `Mᵢ† Mᵢ` is self-adjoint, and `Mᵢ = Mᵢ† Mᵢ`.
  have hsa : IsSelfAdjoint (m.op i) := by
    rw [hi]; exact IsSelfAdjoint.star_mul_self _
  -- idempotent: `Mᵢ Mᵢ = Mᵢ† Mᵢ = Mᵢ`.
  have hidem : IsIdempotentElem (m.op i) := by
    have h2 := hi
    rw [hsa.star_eq] at h2
    exact h2.symm
  exact ⟨hidem, hsa⟩

end AxQM
