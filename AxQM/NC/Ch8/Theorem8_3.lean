/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.MinimalOperatorSum

/-!
# Nielsen & Chuang, Theorem 8.3 (minimal operator-sum representation)

Any quantum operation on dim-d system has operator-sum rep with at most d² elements.

The content is the linear-algebra bound behind N&C's Exercise 8.10 proof route: a quantum operation
given by an operator-sum representation `E(ρ) = Σᵢ Eᵢ ρ Eᵢ†` (with the index set arbitrarily large)
can always be re-expressed with at most `d²` operation elements, without changing the operation.
N&C's own proof appeals to the freedom in the operator-sum representation (Theorem 8.2); the
formalisation here reaches the same bound through the **Choi vectors** `vec Eᵢ ∈ H ⊗ H`, whose
ambient space has dimension `d²`: reducing the Choi operator `Σᵢ |vec Eᵢ⟩⟨vec Eᵢ|` to at most `d²`
rank-one terms and un-vectorizing yields the `≤ d²` operation elements. The "at most `M`, with
`1 ≤ M ≤ d²`" is captured in padded form: the produced family is indexed by `Fin (d²)`, some of
whose elements may be the zero operator (a zero operation element contributes nothing to the map).

The formalisation is in `ToMathlib/Analysis/InnerProductSpace/MinimalOperatorSum.lean` (the
minimal-representation results) with the general operator-sum "freedom" API it builds on in
`ToMathlib/Analysis/InnerProductSpace/OperatorSumFreedom.lean`:

* `ContinuousLinearMap.exists_krausSumₗ_eq_fin_finrank_sq` — **Theorem 8.3**: for a family
  `E : ι → (H →L[ℂ] H)` on a `d`-dimensional system (`d = finrank ℂ H`), there is a family
  `F : Fin (finrank ℂ H ^ 2) → (H →L[ℂ] H)` with `krausSumₗ F = krausSumₗ E` — an equal operator-sum
  map with at most `d²` operation elements.
* `ContinuousLinearMap.exists_krausSumₗ_eq_fin_finrank` — the `d`-to-`d′` generalization
  (N&C **Exercise 8.11**): for `E : ι → (H →L[ℂ] G)` the reduced family is indexed by
  `Fin (finrank ℂ G * finrank ℂ H)`, the `d · d′` bound.
* `ContinuousLinearMap.krausSumₗ_eq_of_choi_eq` — the key step: equal Choi operators
  `Σᵢ |vec Eᵢ⟩⟨vec Eᵢ| = Σₖ |vec Fₖ⟩⟨vec Fₖ|` (over possibly different index sets) give equal
  operator-sum maps.

The general `krausSumₗ` freedom lemmas these use live in `OperatorSumFreedom.lean`:
`krausSumₗ_eq_of_unitary_smul` (unitary freedom, the "⟸" direction of N&C Theorem 8.2:
a unitary mixing `Eₐ = Σ_b uₐ_b • F_b` leaves the operator-sum map unchanged),
`krausSumₗ_comp_equiv` (reindexing invariance), and `krausSumₗ_sumElim` (additivity, with the
zero-padding corollaries).

The reduction reuses `InnerProductSpace.exists_sum_rankOne_self_eq_fin_finrank` (the rank-one-sum
`≤ finrank` reduction) and the vector form of N&C Theorem 2.6
(`InnerProductSpace.sum_rankOne_self_eq_iff_exists_mem_unitaryGroup`).
-/
