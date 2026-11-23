/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# Nielsen & Chuang, Theorem 8.2 (Unitary freedom in the operator-sum representation)

*(N&C p. 372.)*

Unitary freedom: {E_i},{F_j} give the same quantum operation iff E_i=Σu_ij F_j for unitary u.

## Where this is formalised

Theorem 8.2 is, at its formal core, a statement of **finite-dimensional linear algebra**: for two
equal-size families of operators `E, F : ι → H →L[ℂ] H` on a finite-dimensional complex inner
product space, the operator-sum maps `ρ ↦ ∑ᵢ Eᵢ ρ Eᵢ†` and `ρ ↦ ∑ⱼ Fⱼ ρ Fⱼ†` agree **iff** the
`Eᵢ` are a unitary mixing of the `Fⱼ`. Its statement involves only operators `H →L[ℂ] H`,
rank-one operators, the matricization isomorphism and `Matrix.unitaryGroup`, over a *general* space
`H`. It is stated in `ToMathlib/`, exactly as the core of its ensemble analogue **Theorem 2.6**
(`InnerProductSpace.sum_rankOne_self_eq_iff_exists_mem_unitaryGroup`) is in
`ToMathlib/Analysis/InnerProductSpace/RankOneSum.lean`.

## The formalisation (in `ToMathlib/Analysis/InnerProductSpace/OperatorSum.lean`)

The unitary-freedom results share the file with N&C **Theorem 8.1**'s operator-sum map
`ContinuousLinearMap.krausSumₗ E ρ = ∑ᵢ Eᵢ ρ Eᵢ†` (the `ℂ`-linear Kraus map, built on the
per-outcome conjugation `ContinuousLinearMap.postOp`) and reuse it directly — "the same quantum
operation" is equality of these maps.

* `ContinuousLinearMap.krausSumₗ_eq_iff_exists_mem_unitaryGroup` — **the theorem**:
  `krausSumₗ E = krausSumₗ F ↔ ∃ u ∈ Matrix.unitaryGroup ι ℂ, ∀ i, Eᵢ = ∑ⱼ uᵢⱼ • Fⱼ`.
  The common index `ι` is N&C's padded form (`m = n`, appending zero operators), and equality of
  operator-sum maps is the faithful reading of "`E = F` as quantum operations" — the maps agree on
  every operator `ρ`. No trace-preservation / complete-positivity hypothesis is assumed, matching
  the generality of N&C's statement.
* `ContinuousLinearMap.krausSumₗ_eq_of_mem_unitaryGroup` — the `⟸` direction alone: a unitary
  mixing of the operation elements leaves the operator-sum map unchanged (the "simple algebra" half
  of N&C's proof).
* Supporting Choi/vectorization bridge: `ContinuousLinearMap.sum_rankOne_matricizeSymm_eq` (the
  Choi operator of a Kraus family as a fixed function of its operator-sum map `krausSumₗ`) and
  `ContinuousLinearMap.rankOne_matricizeSymm_eq`. The reusable tensor lemmas
  `InnerProductSpace.rankOne_tmul_tmul` (in `Mathlib.Analysis.InnerProductSpace.TensorProduct`,
  beside `rankOne_tmul_self`) and `InnerProductSpace.rankOne_sum_sum` (in
  `Mathlib.Analysis.InnerProductSpace.LinearMap`, beside `rankOne_sum_smul_sum_smul`) are general
  and live in their API homes.

Following N&C, the proof reduces Theorem 8.2 to Theorem 2.6 via the Choi/vectorization
correspondence: vectorizing the operation elements into `H ⊗ H`, the Choi operator
`∑ᵢ |vec Eᵢ⟩⟨vec Eᵢ|` depends on `E` only through its operator-sum map `krausSumₗ E`, so equal
operator-sum maps give equal Choi operators, and the vector form of Theorem 2.6 supplies the
relating unitary.
-/
