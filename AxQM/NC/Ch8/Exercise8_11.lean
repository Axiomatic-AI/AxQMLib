/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.MinimalOperatorSum

/-!
# Nielsen & Chuang, Exercise 8.11 (operation-element count for `d → d′` operations)

*(N&C p. 373.)*

Show a quantum operation from d-dim to d'-dim space needs at most dd' operation elements.

This is the `d`-to-`d′` generalization of Theorem 8.3 (the square case
`d′ = d` giving the `d²` bound). N&C's own proof route (Exercise 8.10, via the Gram matrix
`Wⱼₖ = tr(Eⱼ† Eₖ)`) carries over verbatim: the reasoning nowhere uses that the input and output
spaces coincide, only that the operation elements `Eₖ : H →L[ℂ] G` live in the
`(dim G · dim H)`-dimensional operator space, so the count bound rises from `d²` to `dd′`.

## The formalisation

Start from any operator-sum representation of the operation, `E(ρ) = Σᵢ Eᵢ ρ Eᵢ†` — a finite family
`E : ι → (H →L[ℂ] G)` over an *arbitrarily large* index `ι` (this is exactly what "`E` is a quantum
operation given by operation elements" supplies, per N&C Theorem 8.1). The claim is that the same
operation is realized by a family indexed by `Fin (dim G · dim H)`, i.e. with at most `dd′`
operation elements:

`∃ F : Fin (finrank ℂ G · finrank ℂ H) → (H →L[ℂ] G), krausSumₗ F = krausSumₗ E`.

The mechanism is the **Choi vectors** `vec Eᵢ = (matricize b).symm Eᵢ ∈ G ⊗ H` (`b` an orthonormal
basis of the input `H`), whose ambient space `G ⊗ H` has `finrank = dim G · dim H = d′ · d`. The
Choi operator `Σᵢ |vec Eᵢ⟩⟨vec Eᵢ|` is a finite sum of rank-one projectors, so it reduces to at most
`finrank (G ⊗ H) = dd′` rank-one terms `Σₖ |Wₖ⟩⟨Wₖ|`; un-vectorizing `Fₖ = matricize b Wₖ` gives a
family whose Choi operator equals that of `E`, and equal Choi operators force equal operator-sum
maps. The bound `dd′` is precisely `dim (G ⊗ H)`, the operator-space dimension, matching N&C.

**Fidelity.** The statement is faithful to "`E` can be described using a set of at most `dd′`
operation elements": N&C's "at most `dd′`" (an inequality `1 ≤ M ≤ dd′`) is captured in *padded*
form — the produced family occupies exactly `dd′` slots, some of which may be the zero operator, and
a zero operation element contributes nothing to the map (`0 ρ 0† = 0`), so the nonzero elements form
a set of size `≤ dd′`. The input space, output space, and starting index set are all fully general:
nothing is specialized to `G = H` or to any particular dimension, and no trace-preservation
(channel) hypothesis is imposed — the reduction is about the operator-sum *map* and holds for any
quantum operation (trace-non-increasing included). The square case `G = H` is recovered as the
immediate corollary `exists_krausSumₗ_eq_fin_finrank_sq` (Theorem 8.3, `d²`); Theorem 8.3 is
derived from the `d → d′` form of this exercise.

## Relation to Theorems 8.1 and 8.3

The formal content of Exercise 8.11 is general operator/Hilbert-space linear algebra about the
operator-sum (Kraus) map `ρ ↦ Σᵢ Eᵢ ρ Eᵢ†` (`ContinuousLinearMap.krausSumₗ`), stated for operators
`H →L[ℂ] G`. Compare Theorem 8.3 (the square case). For a quantum operation `E`, the family `E`
above is the one given by the operator-sum representation theorem (N&C Theorem 8.1).

The formalisation is in the following results, which also give Theorem 8.3 (whose square-case
bound this generalizes).

* `ToMathlib/Analysis/InnerProductSpace/MinimalOperatorSum.lean`:
  * `ContinuousLinearMap.exists_krausSumₗ_eq_fin_finrank` — **Exercise 8.11**: for any finite family
    `E : ι → (H →L[ℂ] G)`, there is a family `F : Fin (finrank ℂ G * finrank ℂ H) → (H →L[ℂ] G)`
    with `krausSumₗ F = krausSumₗ E` — an equal operator-sum map with at most `dd′` operation
    elements.
  * `ContinuousLinearMap.exists_krausSumₗ_eq_fin_finrank_sq` — the `G = H` corollary (Theorem 8.3,
    the `d²` bound), derived from the above by reshaping `Fin (d · d)` to `Fin (d²)`.
  * `ContinuousLinearMap.krausSumₗ_eq_of_choi_eq` — the key step: equal Choi operators
    `Σᵢ |vec Eᵢ⟩⟨vec Eᵢ| = Σₖ |vec Fₖ⟩⟨vec Fₖ|` (over possibly different index sets) give equal
    operator-sum maps.

* Supporting results in `Mathlib/` that these build on:
  `InnerProductSpace.exists_sum_rankOne_self_eq_fin_finrank` (any finite sum of rank-one projectors
  equals one over `Fin (finrank)` — the reduction engine, applied to the Choi vectors),
  `TensorProduct.matricize` (the vectorization `(H →L G) ≃ₗ (G ⊗ H)`) with
  `Module.finrank_tensorProduct` (`finrank (G ⊗ H) = dim G · dim H`, the `dd′` count), and the
  operator-sum "freedom" lemmas of `ToMathlib.Analysis.InnerProductSpace.OperatorSumFreedom`
  (`krausSumₗ_eq_of_unitary_smul`, the "⟸" direction of N&C Theorem 8.2; `krausSumₗ_comp_equiv`,
  reindexing invariance; `krausSumₗ_sumElim_*`, zero-padding).

See the module docstring of `ToMathlib/Analysis/InnerProductSpace/MinimalOperatorSum.lean` for the
full argument, and Theorem 8.3 (`AxQM/NC/Ch8/Theorem8_3.lean`) for the square-case companion.
-/
