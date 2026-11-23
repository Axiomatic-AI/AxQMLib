/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Measurement

/-!
# Extensionality for measurements

A `Measurement ι S` is its family of operators `op : ι → (S →L[ℂ] S)` together with a
*completeness* proof (a `Prop`). Two measurements with the same operators are therefore equal —
the completeness proofs coincide by proof irrelevance. `Measurement.ext_op` packages this so a
measurement identity can be reduced to a pointwise operator identity (the analogue of function
extensionality).
-/

noncomputable section

namespace AxQM

namespace Measurement

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- **Extensionality for measurements.** Two measurements on the same system with the same outcome
set are equal as soon as their operators agree at every outcome: the completeness proofs are
propositions and coincide by proof irrelevance. -/
theorem ext_op {m₁ m₂ : Measurement ι S} (h : ∀ i, m₁.op i = m₂.op i) : m₁ = m₂ := by
  cases m₁ with
  | mk op₁ c₁ =>
    cases m₂ with
    | mk op₂ c₂ =>
      have hop : op₁ = op₂ := funext h
      subst hop
      rfl

end Measurement

end AxQM
