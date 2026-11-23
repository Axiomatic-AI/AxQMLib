/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MutualInformation
import AxQM.Postulates.API.SubadditivityReformulations
import AxQM.Postulates.API.SystemIsoComm
import AxQM.Postulates.API.EntropyComposite
import AxQM.Postulates.PartialTraceTensor

/-!
# AxQM — appending a pure product ancilla leaves the mutual information unchanged

Adjoining a subsystem `C` prepared in a **pure product** state to a bipartite state `ρ` on `A ⊗ B`
does not change the quantum mutual information between `A` and the (now enlarged) second party:

`S(A : B ⊗ C) = S(A : B)`   when `C` starts in a pure product state.

This is the third ingredient (labelled *(c)*) of Nielsen & Chuang's proof of **Theorem 11.15(3)**
(quantum operations never increase mutual information, p. 523): that proof models a channel on `B`
as a unitary interaction on `B ⊗ C` with the ancilla `C` initially pure, and uses that appending the
pure ancilla creates no correlations. It sits alongside the entropy-invariance ingredient *(a)*
(`State.vonNeumannEntropy_evolve`) and the local-unitary-invariance ingredient *(b)*
(`State.vonNeumannMutualInfo_evolve_id_tmul`).

## The ancilla-adjoined state and its marginals

For `ρ : State (A ⊗ B)` and `ω : State C`, the ancilla-adjoined state on `A ⊗ (B ⊗ C)` is
`σ := (ρ ⊗ ω).congr (QSystem.assoc A B C).symm` — the product `ρ ⊗ ω` (which lives on `(A ⊗ B) ⊗ C`)
re-associated to the `A ⊗ (B ⊗ C)` grouping the mutual-information reformulations use. Its three
marginals are read off:

* `State.reducedLeft_congr_symm_assoc_tmul` — the `A`-marginal is `ρ`'s `A`-marginal, `Tr_{B⊗C} σ =
  ρ_A` (via the `State.congr` roundtrip and the `S(A)`-marginal consistency lemma
  `State.reducedLeft_reducedLeft_congr_assoc`);
* `State.reducedRight_congr_symm_assoc_tmul` — the `B ⊗ C`-marginal is `ρ_B ⊗ ω`, `Tr_A σ =
  ρ.reducedRight ⊗ ω` (via the forward-associator partial-trace lemma
  `LinearMap.partialTraceLeft_assocIsometry_conjStarAlgEquiv_map`).

The statements need no faithfulness hypothesis (the result is positivity-free, like the invariance
ingredients). The marginal proofs go through partial traces of the re-associated density operator.

## Main results

* `AxQM.State.vonNeumannMutualInfo_tmul_pure_right` — `S(A : B ⊗ C) = S(A : B)` for a pure
  product ancilla.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C : QSystem}

/-- **`A`-marginal of the ancilla-adjoined state.** For `ρ : State (A ⊗ B)` and `ω : State C`, the
left marginal of the re-associated product `σ := (ρ ⊗ ω).congr (QSystem.assoc A B C).symm` on
`A ⊗ (B ⊗ C)` is `ρ`'s left marginal: tracing out `B ⊗ C` from `σ` recovers `Tr_B ρ`. Proved by the
`State.congr` roundtrip (`σ.congr (QSystem.assoc A B C) = ρ ⊗ ω`) fed to the `S(A)`-marginal
consistency lemma `State.reducedLeft_reducedLeft_congr_assoc`, then `State.reducedLeft_tmul`. -/
theorem State.reducedLeft_congr_symm_assoc_tmul (ρ : State (A ⊗ B)) (ω : State C) :
    (State.congr (QSystem.assoc A B C).symm (ρ.tmul ω)).reducedLeft = ρ.reducedLeft := by
  have h := State.reducedLeft_reducedLeft_congr_assoc
    (State.congr (QSystem.assoc A B C).symm (ρ.tmul ω))
  rw [State.congr_congr_symm, State.reducedLeft_tmul] at h
  exact h.symm

/-- **`B ⊗ C`-marginal of the ancilla-adjoined state.** For `ρ : State (A ⊗ B)` and `ω : State C`,
the right marginal of the re-associated product `σ := (ρ ⊗ ω).congr (QSystem.assoc A B C).symm` on
`A ⊗ (B ⊗ C)` is `ρ.reducedRight ⊗ ω`: tracing out `A` from `σ` leaves the `B`-marginal of `ρ`
tensored with the untouched ancilla. Reduces, after unfolding the density operator, to the
forward-associator partial-trace lemma
`LinearMap.partialTraceLeft_assocIsometry_conjStarAlgEquiv_map`. -/
theorem State.reducedRight_congr_symm_assoc_tmul (ρ : State (A ⊗ B)) (ω : State C) :
    (State.congr (QSystem.assoc A B C).symm (ρ.tmul ω)).reducedRight = ρ.reducedRight.tmul ω := by
  -- The re-associated product's operator is the *forward* associator conjugation of `ρ.op ⊗ ω.op`
  -- (`(A.assoc B C).symm.toIsometry = assocIsometry`, cancelling the two `.symm`s).
  apply State.ext
  rw [State.reducedRight_op, State.congr_op, QSystem.assoc_symm_toIsometry, State.tmul_op,
    State.tmul_op, State.reducedRight_op]
  apply ContinuousLinearMap.coe_injective
  rw [LinearMap.coe_toContinuousLinearMap, TensorProduct.toLinearMap_mapL,
    LinearMap.coe_toContinuousLinearMap]
  -- The `(A ⊗ B).space` factor of `mapL ρ.op ω.op` carries the bundled `QSystem.compose` instances,
  -- defeq-but-not-syntactic to the raw `A.space ⊗ B.space` of the lemma; close by `exact`.
  exact LinearMap.partialTraceLeft_assocIsometry_conjStarAlgEquiv_map
    (stdOrthonormalBasis ℂ A.space) ρ.op ω.op

/-- **N&C Theorem 11.15(3), ingredient (c): appending a pure product ancilla leaves the quantum
mutual information unchanged.** For a bipartite state `ρ` on `A ⊗ B` and a subsystem `C` prepared in
a pure product state `ω`, the mutual information between `A` and the enlarged second party `B ⊗ C`
equals the original mutual information between `A` and `B`:

`S(A : B ⊗ C) = S(A : B)`,

where the left-hand side is the mutual information of the ancilla-adjoined state
`σ := (ρ ⊗ ω).congr (QSystem.assoc A B C).symm`. Each term of `S(A:B⊗C) = S(A) + S(B⊗C) − S(A,B,C)`
matches: `S(A)` is unchanged (`State.reducedLeft_congr_symm_assoc_tmul`); `S(B ⊗ C) = S(B) + S(ω) =
S(B)` and `S(A,B,C) = S(A,B) + S(ω) = S(A,B)` because the ancilla is a pure product
(`State.reducedRight_congr_symm_assoc_tmul`, `State.vonNeumannEntropy_tmul`,
`PureState.vonNeumannEntropy_toState_eq_zero`, entropy transport-invariance
`State.vonNeumannEntropy_congr`). The pure product ancilla creates no correlations, matching N&C's
use of it in the dilation proof of Theorem 11.15(3). -/
theorem State.vonNeumannMutualInfo_tmul_pure_right (ρ : State (A ⊗ B)) (ω : PureState C) :
    (State.congr (QSystem.assoc A B C).symm (ρ.tmul ω.toState)).vonNeumannMutualInfo =
      ρ.vonNeumannMutualInfo := by
  rw [State.vonNeumannMutualInfo_def, State.vonNeumannMutualInfo_def,
    State.reducedLeft_congr_symm_assoc_tmul, State.reducedRight_congr_symm_assoc_tmul,
    State.vonNeumannEntropy_tmul, State.vonNeumannEntropy_congr, State.vonNeumannEntropy_tmul,
    PureState.vonNeumannEntropy_toState_eq_zero]
  ring

end AxQM
