/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SchmidtDecompositionExamples
import AxQM.Postulates.API.SchmidtDecompositionEntangledExample
import AxQM.Postulates.API.BellReducedState
import AxQM.NC.Ch2.Exercise2_74
import AxQM.NC.Ch2.Problem2_2

/-!
# Nielsen & Chuang, Exercise 2.79 (Schmidt decompositions of three specific two-qubit states)

Find the Schmidt decompositions of three specific two-qubit states.

What is formalised is the *Schmidt decomposition* (Nielsen–Chuang Theorem 2.7) of each concrete
two-qubit pure state `PureState (qubit ⊗ qubit)`.

## What "finding the Schmidt decomposition" is

For each state, *finding* its Schmidt decomposition means exhibiting the concrete Schmidt
coefficients and orthonormal Schmidt bases and proving `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩`. The explicit
decompositions are in `AxQM/Postulates/API/SchmidtDecompositionExamples.lean`, packaged through the
predicate `PureState.IsSchmidtDecomposition`:

* **State 1** — `bellPhiPlus_isSchmidtDecomposition`: the Bell state `(|00⟩ + |11⟩)/√2` is already
  in Schmidt form in the computational basis, with coefficients `1/√2, 1/√2` and bases `|0⟩, |1⟩`.
* **State 2** — `plusPlusState_isSchmidtDecomposition` (with `plusPlusState_vec_eq` proving
  `(|00⟩ + |01⟩ + |10⟩ + |11⟩)/2 = |+⟩ ⊗ |+⟩`): a *product* state, single Schmidt term
  `1 · |+⟩|+⟩`.

This file also states the complementary corollaries — the *Schmidt numbers*, in terms of
`PureState.schmidtNumber` (the number of nonzero Schmidt coefficients):

* `bellPhiPlus_schmidtNumber` — the Bell state has Schmidt number `2` (maximally entangled);
* `plusPlusState_schmidtNumber` — the product state has Schmidt number `1` (unentangled).

The Schmidt numbers are computed via `PureState.schmidtNumber_eq_rank_reducedLeft`
(Schmidt number = rank of the reduced density operator, Problem 2.2(1)): the Bell state's left
marginal is the maximally mixed `I/2` of full rank `2` (`bellState_reducedLeft_op`), while the
product state's left marginal is the *pure* state `|+⟩⟨+|` of rank `1`
(`reducedLeft_toState_tmul`, Exercise 2.74; `State.rank_eq_one_of_isPure`, Exercise 2.78).

## The third state

`(|00⟩ + |01⟩ + |10⟩)/√3` (`entangledThreeState`) is genuinely entangled: its reduced density
operator is `ρᴬ = (1/3)!![2, 1; 1, 1]`, with eigenvalues `(3 ± √5)/6`, so its Schmidt coefficients
are the irrational (golden-ratio) values `√((3 ± √5)/6)` and its Schmidt number is `2`. The
explicit decomposition, which needs a separate `√5` development (using Mathlib's
`Real.goldenRatio`), is in `AxQM/Postulates/API/SchmidtDecompositionEntangledExample.lean`:

* `entangledThree_isSchmidtDecomposition` — the explicit two-term decomposition with coefficients
  `√((3+√5)/6)`, `√((3−√5)/6)` and Schmidt bases the normalised eigenvectors `(φ,1)`, `(ψ,1)` of the
  coefficient matrix `!![1,1;1,0]` (the right basis carrying the sign `(ψ,1) ↦ −(ψ,1)`, folding the
  negative eigenvalue `ψ` into a positive coefficient).

This file also states the corollary `entangledThreeState_schmidtNumber` — the Schmidt number
`2` — via `PureState.schmidtNumber_eq_of_isSchmidtDecomposition` (the Schmidt number is the number
of terms of any reduced Schmidt decomposition).
-/

open scoped InnerProductSpace

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.79 (state 1, Schmidt number).** The Bell state
`|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` has **Schmidt number 2** — it is maximally entangled. Its explicit
two-term Schmidt decomposition (coefficients `1/√2, 1/√2`, computational basis) is
`bellPhiPlus_isSchmidtDecomposition`; here the *number* of Schmidt terms is computed as the rank
of the left reduced density operator (`schmidtNumber_eq_rank_reducedLeft`, N&C Problem 2.2(1)),
which for `|Φ⁺⟩` is the maximally mixed state `I/2` (`bellState_reducedLeft_op` at `β₀₀`), whose
range is all of the qubit space (rank `2`). -/
theorem bellPhiPlus_schmidtNumber : bellPhiPlus.schmidtNumber = 2 := by
  rw [PureState.schmidtNumber_eq_rank_reducedLeft, ← bellState_zero_zero, State.rank,
    bellState_reducedLeft_op, ContinuousLinearMap.toLinearMap_smul,
        ContinuousLinearMap.toLinearMap_one,
    LinearMap.range_smul _ _ (show (2 : ℂ)⁻¹ ≠ 0 by norm_num),
    Module.End.one_eq_id, LinearMap.range_id, finrank_top]
  exact finrank_qubit_space

/-- **Nielsen & Chuang, Exercise 2.79 (state 2, Schmidt number).** The product state
`(|00⟩ + |01⟩ + |10⟩ + |11⟩)/2 = |+⟩ ⊗ |+⟩` has **Schmidt number 1** — it is unentangled. Its
explicit single-term Schmidt decomposition is `plusPlusState_isSchmidtDecomposition`; here the
*number* of Schmidt terms is the rank of the left reduced density operator
(`schmidtNumber_eq_rank_reducedLeft`), which for a product state is the pure state `|+⟩⟨+|`
(`reducedLeft_toState_tmul`, Exercise 2.74), of rank `1` (`State.rank_eq_one_of_isPure`,
Exercise 2.78). -/
theorem plusPlusState_schmidtNumber : plusPlusState.schmidtNumber = 1 := by
  rw [plusPlusState, PureState.schmidtNumber_eq_rank_reducedLeft, reducedLeft_toState_tmul]
  exact State.rank_eq_one_of_isPure ⟨qubitPlus, rfl⟩

/-- **Nielsen & Chuang, Exercise 2.79 (state 3, Schmidt number).** The genuinely entangled state
`(|00⟩ + |01⟩ + |10⟩)/√3` has **Schmidt number 2** — like the Bell state it is entangled (Schmidt
number `> 1`), but here with the *irrational* Schmidt coefficients `√((3±√5)/6)`. The explicit
two-term Schmidt decomposition is `entangledThree_isSchmidtDecomposition`; the *number* of Schmidt
terms is read off it by `PureState.schmidtNumber_eq_of_isSchmidtDecomposition` (the Schmidt number
is the number of terms of any reduced Schmidt decomposition). -/
theorem entangledThreeState_schmidtNumber : entangledThreeState.schmidtNumber = 2 :=
  entangledThreeState.schmidtNumber_eq_of_isSchmidtDecomposition
    entangledThree_isSchmidtDecomposition

end AxQM
