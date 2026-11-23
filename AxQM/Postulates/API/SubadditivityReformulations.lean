/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.StrongSubadditivity
import AxQM.Postulates.API.MutualInformation
import AxQM.Postulates.API.ReducedStateTransport
import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract

/-!
# AxQM — reformulations of strong subadditivity (N&C Theorem 11.15)

Two of the three elementary reformulations of strong subadditivity from Nielsen & Chuang,
Theorem 11.15 (p. 522):

* **(1) Conditioning reduces entropy** — `S(A|B,C) ≤ S(A|B)`
  (`State.conditioning_reduces_vonNeumannEntropy`);
* **(2) Discarding quantum systems never increases mutual information** — `S(A:B) ≤ S(A:B,C)`
  (`State.vonNeumannMutualInfo_le_of_discard`).

Both are *algebraic rearrangements* of strong subadditivity, `S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)`
(`State.vonNeumannEntropy_add_le_add`, N&C Theorem 11.14 eq. (11.73)), matching N&C's own proof on
p. 523: each reformulation is shown equivalent to strong subadditivity by moving the terms across
the inequality. The third reformulation — quantum *operations* never increase mutual information —
requires the environment (Stinespring) representation of a channel and is a separate development.

## The two marginal-consistency lemmas

The state lives on the right-nested composite `A ⊗ (B ⊗ C)`. The `A ⊗ B`-marginal is read off after
re-associating to `(A ⊗ B) ⊗ C` and tracing out `C`, i.e. as
`σ := (ρ.congr (QSystem.assoc A B C)).reducedLeft`. To relate `σ`'s own marginals back to `ρ`'s the
file proves that the two ways of computing the `S(A)`- and `S(B)`-marginals agree as **states**:

* `State.reducedLeft_reducedLeft_congr_assoc` — `σ`'s `A`-marginal is `ρ`'s `A`-marginal
  (trace out `B ⊗ C` at once vs. trace out `C` then `B` after re-association), via the
  commutation lemma
  `LinearMap.partialTraceRight_partialTraceRight_assocIsometry_symm_conjStarAlgEquiv`
  together with basis-independence of the partial trace;
* `State.reducedRight_reducedLeft_congr_assoc` — `σ`'s `B`-marginal is the `B`-marginal of `ρ`'s
  `B ⊗ C`-marginal (trace out `A` then `C` vs. trace out `C` then `A`), via
  `LinearMap.partialTraceLeft_partialTraceRight_assoc`.

## Hypotheses and notation

Every statement here carries the faithfulness hypothesis `IsStrictlyPositive ρ.op`, the finite,
real-valued requirement inherited from the strong-subadditivity theorem and Problem 11.4's
conditional strong subadditivity that they descend from. The statement of Theorem 11.15 is in
`AxQM/NC/Ch11/Theorem11_15.lean`.

Reformulation (1) is stated *inline* over von Neumann entropy differences rather than through the
conditional entropy `State.condVonNeumannEntropy`; its LHS/RHS are exactly `S(A|B,C)` and `S(A|B)`
by that definition. Reformulation (2) uses the mutual information `State.vonNeumannMutualInfo`
defined in `Postulates/API/MutualInformation`.

## Main results

* `AxQM.State.conditioning_reduces_vonNeumannEntropy` — N&C Theorem 11.15(1).
* `AxQM.State.vonNeumannMutualInfo_le_of_discard` — N&C Theorem 11.15(2).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C : QSystem}

/-- **`S(A)`-marginal consistency.** For a tripartite state `ρ` on `A ⊗ (B ⊗ C)`, the `A`-marginal
of the `A ⊗ B`-marginal `σ = (ρ.congr (QSystem.assoc A B C)).reducedLeft` equals the `A`-marginal of
`ρ` itself: tracing out `B ⊗ C` in one step is the same as re-associating, tracing out `C`, then
tracing out `B`. Reduces to the commutation lemma
`LinearMap.partialTraceRight_partialTraceRight_assocIsometry_symm_conjStarAlgEquiv` plus
basis-independence of the partial trace. -/
theorem State.reducedLeft_reducedLeft_congr_assoc (ρ : State (A ⊗ (B ⊗ C))) :
    ((ρ.congr (QSystem.assoc A B C)).reducedLeft).reducedLeft = ρ.reducedLeft := by
  -- The reverse face of the canonical associator–left-marginal lemma
  -- `State.reducedLeft_congr_assoc_symm` (`Postulates/API/ReducedStateTransport`), which applies
  -- the commutation fact once. Instantiate it at `ρ.congr (QSystem.assoc A B C)` and cancel
  -- the associator against its inverse via the transport unit/inverse laws.
  have h := State.reducedLeft_congr_assoc_symm (ρ.congr (QSystem.assoc A B C))
  rw [← State.congr_trans, QSystem.Iso.trans_symm_self, State.congr_refl] at h
  exact h.symm

/-- **`S(B)`-marginal consistency.** For a tripartite state `ρ` on `A ⊗ (B ⊗ C)`, the `B`-marginal
of the `A ⊗ B`-marginal `σ = (ρ.congr (QSystem.assoc A B C)).reducedLeft` equals the `B`-marginal of
the `B ⊗ C`-marginal of `ρ`: tracing out `A` then `C` is the same as tracing out `C` then `A`.
Reduces to the commutation lemma `LinearMap.partialTraceLeft_partialTraceRight_assoc` through
the bridge `LinearMap.assocIsometry_symm_conjStarAlgEquiv_toLinearMap`. -/
theorem State.reducedRight_reducedLeft_congr_assoc (ρ : State (A ⊗ (B ⊗ C))) :
    ((ρ.congr (QSystem.assoc A B C)).reducedLeft).reducedRight = ρ.reducedRight.reducedLeft := by
  apply State.ext
  -- Both operators are definitionally the displayed iterated partial traces; restate to that form,
  -- then bridge the isometry conjugation to the plain-`LinearEquiv` conjugation the
  -- commutation lemma is stated with, and commute the two partial traces (trace out `A` then `C`).
  change (LinearMap.partialTraceLeft (stdOrthonormalBasis ℂ A.space)
      (LinearMap.partialTraceRight (stdOrthonormalBasis ℂ C.space)
        (((TensorProduct.assocIsometry ℂ A.space B.space C.space).symm.conjStarAlgEquiv
          ρ.op).toLinearMap))).toContinuousLinearMap =
      (LinearMap.partialTraceRight (stdOrthonormalBasis ℂ C.space)
        (LinearMap.partialTraceLeft (stdOrthonormalBasis ℂ A.space)
          ρ.op.toLinearMap)).toContinuousLinearMap
  -- `(A ⊗ (B ⊗ C)).space` is only `rfl`-defeq (via `QSystem.compose`, twice-nested) to the
  -- generic `A.space ⊗[ℂ] (B.space ⊗[ℂ] C.space)` the tower lemmas need to match
  -- syntactically; restate `ρ.op` there via a `let` and bridge back with `exact`.
  let ρopCLM : A.space ⊗[ℂ] (B.space ⊗[ℂ] C.space) →L[ℂ] A.space ⊗[ℂ] (B.space ⊗[ℂ] C.space) :=
    ρ.op
  have hfull : LinearMap.partialTraceLeft (stdOrthonormalBasis ℂ A.space)
      (LinearMap.partialTraceRight (stdOrthonormalBasis ℂ C.space)
        (((TensorProduct.assocIsometry ℂ A.space B.space C.space).symm.conjStarAlgEquiv
          ρopCLM).toLinearMap)) =
      LinearMap.partialTraceRight (stdOrthonormalBasis ℂ C.space)
        (LinearMap.partialTraceLeft (stdOrthonormalBasis ℂ A.space) ρopCLM.toLinearMap) := by
    rw [LinearMap.assocIsometry_symm_conjStarAlgEquiv_toLinearMap,
      LinearMap.partialTraceLeft_partialTraceRight_assoc]
  exact congrArg LinearMap.toContinuousLinearMap hfull

/-- **N&C Theorem 11.15(1): conditioning reduces entropy.** For a faithful (strictly positive) state
`ρ` on the tripartite system `A ⊗ (B ⊗ C)`,

`S(A|B,C) ≤ S(A|B)`.

Written inline over von Neumann entropy differences: the left-hand side
`S(ρ) − S(ρ.reducedRight)` is `S(A,B,C) − S(B,C) = S(A|B,C)`, and the right-hand side
`S((ρ.congr (QSystem.assoc A B C)).reducedLeft) − S(ρ.reducedRight.reducedLeft)` is
`S(A,B) − S(B) = S(A|B)` (each side is the corresponding value of the conditional entropy
`State.condVonNeumannEntropy`). Immediate from strong
subadditivity `S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)` (`State.vonNeumannEntropy_add_le_add`) by moving
the marginal entropies across, matching N&C's proof on p. 523. -/
theorem State.conditioning_reduces_vonNeumannEntropy (ρ : State (A ⊗ (B ⊗ C)))
    (hρ : IsStrictlyPositive ρ.op) :
    ρ.vonNeumannEntropy - ρ.reducedRight.vonNeumannEntropy ≤
      (ρ.congr (QSystem.assoc A B C)).reducedLeft.vonNeumannEntropy -
        ρ.reducedRight.reducedLeft.vonNeumannEntropy := by
  have h := State.vonNeumannEntropy_add_le_add ρ hρ
  linarith

/-- **N&C Theorem 11.15(2): discarding quantum systems never increases mutual information.** For a
faithful (strictly positive) state `ρ` on the tripartite system `A ⊗ (B ⊗ C)`,

`S(A:B) ≤ S(A:B,C)`,

where `S(A:B)` is the mutual information of the `A ⊗ B`-marginal
`(ρ.congr (QSystem.assoc A B C)).reducedLeft` and `S(A:B,C)` is the mutual information of `ρ`
(read as a bipartite state on `A ⊗ (B ⊗ C)`). Equivalently, discarding the subsystem `C` from the
composite `B ⊗ C` cannot increase how much `A` and `B ⊗ C` know about each other. Immediate from
strong subadditivity once the shared `S(A)` and `S(B)` marginals are identified across the two
readings (`State.reducedLeft_reducedLeft_congr_assoc` and
`State.reducedRight_reducedLeft_congr_assoc`); matches N&C's proof on p. 523. -/
theorem State.vonNeumannMutualInfo_le_of_discard (ρ : State (A ⊗ (B ⊗ C)))
    (hρ : IsStrictlyPositive ρ.op) :
    ((ρ.congr (QSystem.assoc A B C)).reducedLeft).vonNeumannMutualInfo ≤
      ρ.vonNeumannMutualInfo := by
  have hSSA := State.vonNeumannEntropy_add_le_add ρ hρ
  rw [State.vonNeumannMutualInfo_def, State.vonNeumannMutualInfo_def,
    State.reducedLeft_reducedLeft_congr_assoc, State.reducedRight_reducedLeft_congr_assoc]
  linarith

end AxQM
