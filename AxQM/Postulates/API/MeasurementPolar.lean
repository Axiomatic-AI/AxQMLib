/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Measurement
import ToMathlib.Analysis.InnerProductSpace.PolarUnitary

/-!
# AxQM — polar form of measurement operators

This file proves **Nielsen–Chuang Exercise 2.63**. The exercise asks: given a measurement described
by measurement operators `Mₘ`, show that there exist *unitary* operators `Uₘ` such that
`Mₘ = Uₘ √Eₘ`, where `Eₘ = Mₘ† Mₘ` is the POVM element associated to the measurement
(eq. (2.117)).

This is exactly the **left polar decomposition** `Mₘ = Uₘ |Mₘ|` applied to each measurement
operator, together with the identification `|Mₘ| = √(Mₘ† Mₘ) = √Eₘ` of the positive factor with the
operator square root of the POVM element:

* `Measurement.exists_unitary_op_eq_comp_sqrt_toPOVM_elements` — the operator equation for a
  measurement: for each outcome `i` there is a unitary `U` with
  `m.op i = U ∘L √(m.toPOVM.elements i)`, where `√` is the continuous-functional-calculus square
  root `cfc Real.sqrt`.

The mathematical core is the existence-of-polar-unitary theorem
`ContinuousLinearMap.exists_mem_unitary_eq_comp_absoluteValue` (`A = U ∘L |A|` for a unitary `U`),
bridged to the POVM element `Eₘ = Mₘ† Mₘ` (`Measurement.toPOVM_elements`) through
`ContinuousLinearMap.absoluteValue_eq_cfc_sqrt` (`|A| = √(A† A)`).

The statement of Exercise 2.63 is in `AxQM/NC/Ch2/Exercise2_63.lean`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- **Nielsen–Chuang Exercise 2.63 (polar form of measurement operators).** For a measurement
`m : Measurement ι S` and outcome `i`, the measurement operator `Mᵢ = m.op i` factors as
`Mᵢ = Uᵢ √Eᵢ` for some **unitary** `Uᵢ`, where `Eᵢ = m.toPOVM.elements i = Mᵢ† Mᵢ` is the associated
POVM element and `√Eᵢ = cfc Real.sqrt Eᵢ` is its positive operator square root.

This is the left polar decomposition `Mᵢ = Uᵢ |Mᵢ|`
(`ContinuousLinearMap.exists_mem_unitary_eq_comp_absoluteValue`) with the positive factor rewritten
via `|Mᵢ| = √(Mᵢ† Mᵢ)` (`ContinuousLinearMap.absoluteValue_eq_cfc_sqrt`) and `Mᵢ† Mᵢ = Eᵢ`
(`Measurement.toPOVM_elements`). -/
theorem exists_unitary_op_eq_comp_sqrt_toPOVM_elements (m : Measurement ι S) (i : ι) :
    ∃ U ∈ unitary (S →L[ℂ] S), m.op i = U.comp (cfc Real.sqrt (m.toPOVM.elements i)) := by
  have : CompleteSpace S.space := FiniteDimensional.completeSpace ℂ S.space
  obtain ⟨U, hU, hUeq⟩ :=
    ContinuousLinearMap.exists_mem_unitary_eq_comp_absoluteValue (m.op i)
  refine ⟨U, hU, ?_⟩
  rw [toPOVM_elements, ← ContinuousLinearMap.absoluteValue_eq_cfc_sqrt]
  exact hUeq

end Measurement

end AxQM
