/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.RankOneSum
public import ToMathlib.Analysis.InnerProductSpace.RankOneProjector

/-! # The partial isometry identifying two orthonormal families

Given two orthonormal families `a : ι → E` and `b : ι → F` of the same finite size (in possibly
*different* inner product spaces `E`, `F`), this file introduces the **cross-synthesis operator**

`crossSynthesis 𝕜 a b = ∑ i, |a i⟩⟨b i| : F →L[𝕜] E`,

the operator that carries each `b i` to `a i` (and annihilates the orthogonal complement of the span
of `b`). It is the partial isometry realizing the identification `b i ↔ a i` of the two families.

The main facts:

* `crossSynthesis_apply_right` — `W (b j) = a j` (`b` orthonormal);
* `adjoint_crossSynthesis` — `W† = crossSynthesis 𝕜 b a = ∑ i, |b i⟩⟨a i|`;
* `crossSynthesis_adjoint_comp_self` — `W† W = ∑ i, |b i⟩⟨b i|`, the orthogonal projector onto
  `span b` (`a` orthonormal);
* `crossSynthesis_comp_adjoint` — `W W† = ∑ i, |a i⟩⟨a i|`, the orthogonal projector onto `span a`
  (`b` orthonormal);
* `crossSynthesis_comp_diagonal` — the **intertwining** `W ∘ D_b = D_a ∘ W`, where
  `D_v = ∑ i, c i • |v i⟩⟨v i|` is the operator diagonal in the family `v` with eigenvalues `c`
  (both `a`, `b` orthonormal). Applied to `c i = λ i ^ 2` this says `W` conjugates the reduced
  density operator `ρ_B = ∑ λ i² |b i⟩⟨b i|` into `ρ_A = ∑ λ i² |a i⟩⟨a i|`; applied to
  `c i = λ i` it conjugates their square roots.

## Motivation

These are the linear-algebra ingredients behind **Nielsen & Chuang, Proposition 12.14** (the LOCC
reduction): the map `|k_A⟩ ↔ |k_B⟩` identifying Alice's and Bob's Schmidt bases (`a` and `b` the
Schmidt vectors of a bipartite pure state) is exactly this partial isometry, and N&C's simulating
operators `N j` are built by transporting Bob's `M j` across it. The intertwining and projector
identities are what make the transported operators reproduce Bob's Born statistics
(via `W W† = P_A`) and post-measurement spectra (via `W ρ_B W† = ρ_A`). The construction and its
properties are pure inner-product-space mathematics.
-/

@[expose] public section

open scoped InnerProductSpace
open Finset

namespace InnerProductSpace

/-- The **cross-synthesis operator** `∑ i, |a i⟩⟨b i| : F →L[𝕜] E` of two finite families
`a : ι → E`, `b : ι → F`. When `a`, `b` are orthonormal of the same size it is the partial isometry
identifying the family `b` with the family `a` (`b i ↦ a i`), i.e. the operator whose "matrix" in
the bases `b`, `a` is the identity. Written as a sum of rank-one operators `|a i⟩⟨b i|`
(`rankOne`). -/
noncomputable def crossSynthesis (𝕜 : Type*) {E F ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [Fintype ι]
    (a : ι → E) (b : ι → F) : F →L[𝕜] E :=
  ∑ i, rankOne 𝕜 (a i) (b i)

variable {𝕜 : Type*} {E : Type*} {F : Type*} {ι : Type*}
  [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [Fintype ι]

/-! ### Real diagonal operators

Two elementary facts about a **real diagonal operator** `∑ i, (l i) • |v i⟩⟨v i|` (real weights
`l : ι → ℝ` coerced to `𝕜`) — self-adjointness and, for an orthonormal family, its square. They are
the building blocks used to identify the square roots `√ρ_A`, `√ρ_B` of the reduced density
operators with `crossSynthesis`-diagonal operators in Nielsen & Chuang Proposition 12.14. -/

/-- A **real diagonal operator** `∑ i, (l i) • |v i⟩⟨v i|` (real weights `l`) is self-adjoint:
adjoint swaps the two vectors of each rank-one — a no-op on the diagonal terms `|v i⟩⟨v i|` — and
conjugates the scalars, which is a no-op on the reals `l i`. -/
theorem adjoint_sum_smul_rankOne_self [CompleteSpace E] (v : ι → E) (l : ι → ℝ) :
    ContinuousLinearMap.adjoint (∑ i, (l i : 𝕜) • rankOne 𝕜 (v i) (v i))
      = ∑ i, (l i : 𝕜) • rankOne 𝕜 (v i) (v i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ, adjoint_rankOne, starRingEnd_apply, RCLike.star_def,
    RCLike.conj_ofReal]

/-- The **square of a real diagonal operator** `(∑ i, (l i) • |v i⟩⟨v i|)²` equals
`∑ i, (l i)² • |v i⟩⟨v i|` for an orthonormal family `v`: rank-one composition
`|v i⟩⟨v i| ∘ |v j⟩⟨v j| = ⟪v i, v j⟫ • |v i⟩⟨v j|` (`rankOne_comp_rankOne`) collapses via
orthonormality to the diagonal with squared weights. -/
theorem sum_smul_rankOne_self_comp_self {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → ℝ) :
    (∑ i, (l i : 𝕜) • rankOne 𝕜 (v i) (v i)).comp (∑ i, (l i : 𝕜) • rankOne 𝕜 (v i) (v i))
      = ∑ i, ((l i ^ 2 : ℝ) : 𝕜) • rankOne 𝕜 (v i) (v i) := by
  classical
  simp only [ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.finsetSum_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
    rankOne_comp_rankOne, orthonormal_iff_ite.mp hv, ite_smul, one_smul,
    zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_smul]
  push_cast
  ring_nf

/-- The cross-synthesis operator acts as `W x = ∑ i, ⟪b i, x⟫ • a i`. -/
theorem crossSynthesis_apply (a : ι → E) (b : ι → F) (x : F) :
    crossSynthesis 𝕜 a b x = ∑ i, (inner 𝕜 (b i) x) • a i := by
  simp only [crossSynthesis, _root_.sum_apply, rankOne_apply]

/-- The cross-synthesis operator carries each `b j` to `a j`, when `b` is orthonormal. This is the
defining property of the partial isometry `b i ↔ a i`. -/
@[simp]
theorem crossSynthesis_apply_right (a : ι → E) {b : ι → F} (hb : Orthonormal 𝕜 b) (j : ι) :
    crossSynthesis 𝕜 a b (b j) = a j := by
  classical
  rw [crossSynthesis_apply]
  simp only [orthonormal_iff_ite.mp hb, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The adjoint of the cross-synthesis operator swaps the two families:
`W† = ∑ i, |b i⟩⟨a i| = crossSynthesis 𝕜 b a`. -/
theorem adjoint_crossSynthesis [CompleteSpace E] [CompleteSpace F] (a : ι → E) (b : ι → F) :
    ContinuousLinearMap.adjoint (crossSynthesis 𝕜 a b) = crossSynthesis 𝕜 b a := by
  simp only [crossSynthesis, map_sum, adjoint_rankOne]

/-- `W† W = ∑ i, |b i⟩⟨b i|`, the orthogonal projector onto the span of `b`, when `a` is
orthonormal. Together with `crossSynthesis_comp_adjoint` this expresses that `W` is a partial
isometry with initial space `span b` and final space `span a`. -/
theorem crossSynthesis_adjoint_comp_self [CompleteSpace E] [CompleteSpace F] {a : ι → E}
    (ha : Orthonormal 𝕜 a) (b : ι → F) :
    (ContinuousLinearMap.adjoint (crossSynthesis 𝕜 a b)).comp (crossSynthesis 𝕜 a b)
      = orthonormalProjector 𝕜 b Finset.univ := by
  classical
  rw [adjoint_crossSynthesis]
  simp only [crossSynthesis, orthonormalProjector, ContinuousLinearMap.finsetSum_comp,
    ContinuousLinearMap.comp_finsetSum, rankOne_comp_rankOne, orthonormal_iff_ite.mp ha, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- `W W† = ∑ i, |a i⟩⟨a i|`, the orthogonal projector onto the span of `a`, when `b` is
orthonormal. -/
theorem crossSynthesis_comp_adjoint [CompleteSpace E] [CompleteSpace F] (a : ι → E) {b : ι → F}
    (hb : Orthonormal 𝕜 b) :
    (crossSynthesis 𝕜 a b).comp (ContinuousLinearMap.adjoint (crossSynthesis 𝕜 a b))
      = orthonormalProjector 𝕜 a Finset.univ := by
  classical
  rw [adjoint_crossSynthesis]
  simp only [crossSynthesis, orthonormalProjector, ContinuousLinearMap.finsetSum_comp,
    ContinuousLinearMap.comp_finsetSum, rankOne_comp_rankOne, orthonormal_iff_ite.mp hb, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The cross-synthesis operator post-composed with a rank-one family collapses:
`W ∘ (∑ i, c i • |b i⟩⟨b i|) = ∑ i, c i • |a i⟩⟨b i|` when `b` is orthonormal. -/
private theorem crossSynthesis_comp_sum_smul_rankOne_self_right {b : ι → F} (hb : Orthonormal 𝕜 b)
    (a : ι → E) (c : ι → 𝕜) :
    (crossSynthesis 𝕜 a b).comp (∑ i, c i • rankOne 𝕜 (b i) (b i))
      = ∑ i, c i • rankOne 𝕜 (a i) (b i) := by
  classical
  simp only [crossSynthesis, ContinuousLinearMap.finsetSum_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_finsetSum, rankOne_comp_rankOne,
    orthonormal_iff_ite.mp hb, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The cross-synthesis operator pre-composed with a rank-one family collapses:
`(∑ i, c i • |a i⟩⟨a i|) ∘ W = ∑ i, c i • |a i⟩⟨b i|` when `a` is orthonormal. -/
private theorem sum_smul_rankOne_self_comp_crossSynthesis {a : ι → E} (ha : Orthonormal 𝕜 a)
    (b : ι → F) (c : ι → 𝕜) :
    (∑ i, c i • rankOne 𝕜 (a i) (a i)).comp (crossSynthesis 𝕜 a b)
      = ∑ i, c i • rankOne 𝕜 (a i) (b i) := by
  classical
  simp only [crossSynthesis, ContinuousLinearMap.comp_finsetSum,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.finsetSum_comp, rankOne_comp_rankOne,
    orthonormal_iff_ite.mp ha, ite_smul, one_smul, zero_smul, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **Intertwining of the cross-synthesis operator with diagonal operators.** For orthonormal `a`,
`b` and any eigenvalue family `c : ι → 𝕜`, the partial isometry `W = crossSynthesis 𝕜 a b`
intertwines the operators diagonal in `b` and in `a` with the *same* eigenvalues:

`W ∘ (∑ i, c i • |b i⟩⟨b i|) = (∑ i, c i • |a i⟩⟨a i|) ∘ W`.

Both sides equal `∑ i, c i • |a i⟩⟨b i|`. Specialized to `c i = λ i ^ 2` this conjugates a density
operator diagonal in `b` into the one diagonal in `a`; to `c i = λ i` it conjugates their square
roots — the identities behind N&C's Schmidt-basis identification in Proposition 12.14. -/
theorem crossSynthesis_comp_diagonal {a : ι → E} (ha : Orthonormal 𝕜 a) {b : ι → F}
    (hb : Orthonormal 𝕜 b) (c : ι → 𝕜) :
    (crossSynthesis 𝕜 a b).comp (∑ i, c i • rankOne 𝕜 (b i) (b i))
      = (∑ i, c i • rankOne 𝕜 (a i) (a i)).comp (crossSynthesis 𝕜 a b) := by
  rw [crossSynthesis_comp_sum_smul_rankOne_self_right hb,
    sum_smul_rankOne_self_comp_crossSynthesis ha]

/-- **Conjugation of a diagonal operator by the cross-synthesis operator.** For orthonormal `b` and
any eigenvalue family `c : ι → 𝕜`, the partial isometry `W = crossSynthesis 𝕜 a b` conjugates the
operator diagonal in `b` into the one diagonal in `a` with the *same* eigenvalues:

`W ∘ (∑ i, c i • |b i⟩⟨b i|) ∘ W† = ∑ i, c i • |a i⟩⟨a i|`.

Since `W |b i⟩ = |a i⟩`, each `W |b i⟩⟨b i| W† = |a i⟩⟨a i|`. Specialized to `c i = λ i ^ 2` this
conjugates a bipartite pure state's *right* reduced density operator (diagonal in Bob's Schmidt
basis `b`) into its *left* reduced operator (diagonal in Alice's Schmidt basis `a`) — the state
identity `W ρ_B W† = ρ_A` behind Nielsen & Chuang's Proposition 12.14 measurement simulation. -/
theorem crossSynthesis_conj_diagonal [CompleteSpace E] [CompleteSpace F] (a : ι → E) {b : ι → F}
    (hb : Orthonormal 𝕜 b) (c : ι → 𝕜) :
    (crossSynthesis 𝕜 a b).comp ((∑ i, c i • rankOne 𝕜 (b i) (b i)).comp
        (ContinuousLinearMap.adjoint (crossSynthesis 𝕜 a b)))
      = ∑ i, c i • rankOne 𝕜 (a i) (a i) := by
  classical
  rw [← ContinuousLinearMap.comp_assoc, crossSynthesis_comp_sum_smul_rankOne_self_right hb,
    adjoint_crossSynthesis]
  simp only [crossSynthesis, ContinuousLinearMap.finsetSum_comp,
    ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.smul_comp, rankOne_comp_rankOne,
    orthonormal_iff_ite.mp hb, ite_smul, one_smul, zero_smul, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end InnerProductSpace
