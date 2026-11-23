/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.StateSpace
import ToMathlib.Analysis.InnerProductSpace.StateDiscrimination

/-!
# AxQM.Postulates.API — unambiguous state discrimination by a POVM

The physics wrapper for Nielsen & Chuang, Exercise 2.64: given a family of **pure states**
`ψ : ι → PureState S` whose underlying vectors are linearly independent, there is a POVM whose
informative outcomes discriminate them *with certainty*.

* `AxQM.distinguishingPOVM` — the POVM on outcomes `Option ι` built from the pure
  states (the general `POVM.distinguishing` of
  `ToMathlib.Analysis.InnerProductSpace.StateDiscrimination`,
  instantiated at the state vectors). Outcome `some i` is "state `i` detected"; the single
  outcome `none` is "inconclusive".
* `AxQM.distinguishingPOVM_prob_eq_zero` — the Born-rule probability of outcome
  `some i` on state `ψ j` (`j ≠ i`) is zero.
* `AxQM.distinguishingPOVM_prob_pos` — the Born-rule probability of outcome `some i`
  on its own state `ψ i` is strictly positive (N&C's requirement `⟪ψᵢ, Eᵢ ψᵢ⟫ > 0`).
* `AxQM.distinguishingPOVM_certain` — the discrimination conclusion: if outcome
  `some i` has nonzero probability on state `ψ j`, then `j = i`; hence observing `some i`
  identifies the input as `ψ i` with certainty.

The Born probability is the POVM's `POVM.toPMF` on the pure state's density operator
`|ψ⟩⟨ψ| = (ψ).toState.op`; it reduces to `⟪ψ, Eᵢ ψ⟫ = (Eᵢ).reApplyInnerSelf ψ.vec` via
`POVM.toPMF_rankOne_self`. The statement of Exercise 2.64 is in
`AxQM/NC/Ch2/Exercise2_64.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- **Discriminating POVM (N&C Exercise 2.64).** For a family of pure states `ψ : ι → PureState S`,
the POVM on outcomes `Option ι` whose informative outcome `some i` detects state `ψ i` and whose
outcome `none` is inconclusive. It is the general `POVM.distinguishing` construction applied to
the state vectors `(ψ i).vec`. When those vectors are linearly independent the informative
outcomes discriminate the states with certainty (`distinguishingPOVM_certain`). -/
def distinguishingPOVM (ψ : ι → PureState S) : POVM (Option ι) ℂ S.space :=
  POVM.distinguishing ℂ (fun i => (ψ i).vec)

/-- The Born-rule probability of the informative outcome `some i` on a *different* state `ψ j`
(`j ≠ i`) is zero: outcome `some i` never occurs unless the input was `ψ i`. -/
theorem distinguishingPOVM_prob_eq_zero (ψ : ι → PureState S) {i j : ι} (hij : j ≠ i) :
    (distinguishingPOVM ψ).toPMF (ψ j).toState.op (some i) = 0 := by
  rw [distinguishingPOVM, PureState.toState_op, POVM.toPMF_rankOne_self]
  exact POVM.distinguishing_reApplyInnerSelf_eq_zero ℂ _ hij

/-- The Born-rule probability of the informative outcome `some i` on its own state `ψ i` is
strictly positive — Nielsen & Chuang's requirement `⟪ψᵢ, Eᵢ ψᵢ⟫ > 0`, ensuring the outcome can
actually occur for the intended state. Requires the state vectors to be linearly independent. -/
theorem distinguishingPOVM_prob_pos (ψ : ι → PureState S)
    (hψ : LinearIndependent ℂ (fun i => (ψ i).vec)) (i : ι) :
    0 < (distinguishingPOVM ψ).toPMF (ψ i).toState.op (some i) := by
  rw [distinguishingPOVM, PureState.toState_op, POVM.toPMF_rankOne_self]
  exact POVM.distinguishing_reApplyInnerSelf_pos ℂ hψ i

/-- **Discrimination with certainty.** If the informative outcome `some i` has nonzero
probability on state `ψ j`, then `j = i`: observing `some i` identifies the input as `ψ i`.
This is the contrapositive of `distinguishingPOVM_prob_eq_zero`. -/
theorem distinguishingPOVM_certain (ψ : ι → PureState S) {i j : ι}
    (h : (distinguishingPOVM ψ).toPMF (ψ j).toState.op (some i) ≠ 0) : j = i := by
  by_contra hij
  exact h (distinguishingPOVM_prob_eq_zero ψ hij)

end AxQM
