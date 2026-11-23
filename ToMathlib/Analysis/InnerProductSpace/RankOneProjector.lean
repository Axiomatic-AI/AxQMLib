/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.LinearMap
public import ToMathlib.Analysis.InnerProductSpace.Adjoint
public import ToMathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import ToMathlib.LinearAlgebra.Eigenspace.Idempotent

/-!
# The orthogonal projector onto the span of an orthonormal family

Given a family of vectors `v : ι → E` in an inner product space `E` over `𝕜` (`ℝ` or `ℂ`) and a
finite index set `s : Finset ι`, this file introduces the **projector**

`orthonormalProjector 𝕜 v s = ∑ i ∈ s, |v i⟩⟨v i|`
(i.e. `∑ i ∈ s, InnerProductSpace.rankOne 𝕜 (v i) (v i)`)

and records its defining properties when the family is orthonormal. This is exactly Nielsen &
Chuang's projector (*Quantum Computation and Quantum Information*, eq. (2.35)): for an orthonormal
basis `|1⟩, …, |d⟩` of `V` whose first `k` vectors span a subspace `W`, the operator
`P ≡ ∑_{i=1}^{k} |i⟩⟨i|` is the projector onto `W` (here `s = {1, …, k}`).

## Main results

* `InnerProductSpace.orthonormalProjector_apply`: the action `P y = ∑ i ∈ s, ⟪v i, y⟫ • v i`.
* `InnerProductSpace.orthonormalProjector_apply_eq_ite`: for an orthonormal family, the action on a
  family vector is `P (v κ) = if κ ∈ s then v κ else 0`.
* `InnerProductSpace.isIdempotentElem_orthonormalProjector`: **Nielsen & Chuang, Exercise 2.16** —
  for an orthonormal family, `P` is idempotent, i.e. `P ∘ P = P` (`P² = P`).
* `InnerProductSpace.isSelfAdjoint_orthonormalProjector`: `P` is self-adjoint, `P† = P` (N&C's
  remark that a projector is Hermitian). This needs no orthonormality: each `|v i⟩⟨v i|` is already
  self-adjoint.
* `InnerProductSpace.isStarProjection_orthonormalProjector`: for an orthonormal family, `P` is a
  star projection (a self-adjoint idempotent) — a genuine orthogonal projector.
* `InnerProductSpace.spectrum_orthonormalProjector_subset`: **Nielsen & Chuang, Exercise 2.23**
  (spectrum form) — `spectrum 𝕜 P ⊆ {0, 1}`.
* `InnerProductSpace.orthonormalProjector_hasEigenvalue_eq_zero_or_one`: **Nielsen & Chuang,
  Exercise 2.23** (eigenvalue form) — every eigenvalue of `P` is `0` or `1`.
* `InnerProductSpace.orthonormalProjector_adjoint_comp_self`: `P† ∘ P = P` for an orthonormal
  family (`P` is a star projection).
* `InnerProductSpace.trace_orthonormalProjector`: for an orthonormal basis, `tr P = |s|`.
* `InnerProductSpace.trace_orthonormalProjector_comp`: `tr(P ∘ D) = ∑ i ∈ s, ⟪b i, D (b i)⟫`.

The idempotence proof is N&C's own computation: composing the sums bilinearly,
`(∑ i, |v i⟩⟨v i|)(∑ j, |v j⟩⟨v j|) = ∑ i ∑ j ⟪v i, v j⟫ |v i⟩⟨v j|`
(`InnerProductSpace.rankOne_comp_rankOne`), and orthonormality `⟪v i, v j⟫ = δ_{ij}` collapses the
double sum back to `∑ i, |v i⟩⟨v i|`. The single-vector case (`s` a singleton, `‖v i‖ = 1`) is the
existing `InnerProductSpace.isStarProjection_rankOne_self`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace InnerProductSpace

variable {𝕜 : Type*} {E : Type*} {ι : Type*}
  [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Nielsen & Chuang's projector** (eq. (2.35)). Given a family `v : ι → E` and a finite index set
`s : Finset ι`, the operator `∑ i ∈ s, |v i⟩⟨v i|`. This is genuinely a projector precisely when `v`
is orthonormal, in which case it is the orthogonal projector onto the span of `{v i | i ∈ s}` (see
`isStarProjection_orthonormalProjector`); the bare definition imposes no orthonormality. `𝕜` is an
explicit argument, matching the summand `rankOne 𝕜 …`. -/
noncomputable def orthonormalProjector (𝕜 : Type*) {E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (v : ι → E) (s : Finset ι) : E →L[𝕜] E :=
  ∑ i ∈ s, rankOne 𝕜 (v i) (v i)

/-- The projector `orthonormalProjector 𝕜 v s` is, by definition, the sum of rank-one projectors
`∑ i ∈ s, |v i⟩⟨v i|`. -/
theorem orthonormalProjector_eq_sum (v : ι → E) (s : Finset ι) :
    orthonormalProjector 𝕜 v s = ∑ i ∈ s, rankOne 𝕜 (v i) (v i) := rfl

/-- The action of the projector `∑ i ∈ s, |v i⟩⟨v i|` on a vector `y` is `∑ i ∈ s, ⟪v i, y⟫ • v i`:
each rank-one term `|v i⟩⟨v i|` contracts `y` against `v i` and scales `v i` by the result. -/
@[simp]
theorem orthonormalProjector_apply (v : ι → E) (s : Finset ι) (y : E) :
    orthonormalProjector 𝕜 v s y = ∑ i ∈ s, (inner 𝕜 (v i) y) • v i := by
  simp only [orthonormalProjector, sum_apply, rankOne_apply]

/-- **The projector applied to a member of its own orthonormal family.** For an orthonormal family
`v`, the projector `P = ∑ i ∈ s, |v i⟩⟨v i|` fixes `v κ` when `κ ∈ s` and annihilates it otherwise:
`P (v κ) = if κ ∈ s then v κ else 0`. Immediate from `orthonormalProjector_apply` and orthonormality
`⟪v i, v κ⟫ = δ_{iκ}` (`orthonormal_iff_ite`), which collapses the `s`-sum to its `i = κ` term
(`Finset.sum_ite_eq'`). This is the diagonalisation `P` is used through when the family is a
*spectral* eigenbasis (`P` and the diagonal operator commute and share eigenvectors). -/
theorem orthonormalProjector_apply_eq_ite [DecidableEq ι] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (s : Finset ι) (κ : ι) :
    orthonormalProjector 𝕜 v s (v κ) = if κ ∈ s then v κ else 0 := by
  rw [orthonormalProjector_apply]
  simp only [orthonormal_iff_ite.mp hv, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' s κ v]

/-- **Rank-one self-projections of an orthonormal family pairwise annihilate.** For an orthonormal
family `v : ι → E` and `i ≠ j`, the self-projectors compose to zero:
`|v i⟩⟨v i| · |v j⟩⟨v j| = ⟪v i, v j⟫ • |v i⟩⟨v j| = 0`, since `⟪v i, v j⟫ = 0`
(`rankOne_comp_rankOne` + orthonormality). This is the off-diagonal vanishing underlying
idempotence of `orthonormalProjector`, and the block-orthogonality input to the joint entropy
theorem (`AxQM.State.vonNeumannEntropy_jointEntropyTheorem` and its flag-right mirror). -/
theorem rankOne_self_mul_rankOne_self_eq_zero_of_orthonormal {v : ι → E}
    (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    rankOne 𝕜 (v i) (v i) * rankOne 𝕜 (v j) (v j) = 0 := by
  rw [ContinuousLinearMap.mul_def, rankOne_comp_rankOne, hv.2 hij, zero_smul]

/-- **Nielsen & Chuang, Exercise 2.16.** Any projector `P = ∑ i ∈ s, |v i⟩⟨v i|` of an orthonormal
family `v` satisfies `P² = P`, i.e. `P` is idempotent (`P ∘ P = P`).

Composing the two sums bilinearly gives `∑ i ∑ j ⟪v i, v j⟫ |v i⟩⟨v j|`
(`rankOne_comp_rankOne`); orthonormality `⟪v i, v j⟫ = δ_{ij}` kills all off-diagonal terms, leaving
`∑ i, |v i⟩⟨v i| = P`. -/
theorem isIdempotentElem_orthonormalProjector {v : ι → E} (hv : Orthonormal 𝕜 v) (s : Finset ι) :
    IsIdempotentElem (orthonormalProjector 𝕜 v s) := by
  classical
  have hb : ∀ i j : ι, (inner 𝕜 (v i) (v j) : 𝕜) = if i = j then (1 : 𝕜) else 0 :=
    fun i j => orthonormal_iff_ite.mp hv i j
  rw [IsIdempotentElem, ContinuousLinearMap.mul_def, orthonormalProjector]
  simp only [ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum,
    rankOne_comp_rankOne, hb, ite_smul, one_smul, zero_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_ite_eq', ite_eq_left hi]

/-- The projector `P = ∑ i ∈ s, |v i⟩⟨v i|` is self-adjoint, `P† = P` (Nielsen & Chuang's remark
that a projector is Hermitian). This holds for *any* family `v`: the adjoint of each rank-one term
`|v i⟩⟨v i|` is itself (`adjoint_rankOne`), so orthonormality is not needed here. -/
theorem isSelfAdjoint_orthonormalProjector [CompleteSpace E] (v : ι → E) (s : Finset ι) :
    IsSelfAdjoint (orthonormalProjector 𝕜 v s) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, orthonormalProjector, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [adjoint_rankOne]

/-- For an orthonormal family `v`, the projector `P = ∑ i ∈ s, |v i⟩⟨v i|` is a **star projection**
— a self-adjoint idempotent — hence a genuine orthogonal projector onto the span of `{v i | i ∈ s}`.
This combines idempotence (`isIdempotentElem_orthonormalProjector`, Nielsen & Chuang Exercise 2.16)
with self-adjointness (`isSelfAdjoint_orthonormalProjector`), and generalizes the single-vector
`isStarProjection_rankOne_self` from one unit vector to a sum over an orthonormal family. -/
theorem isStarProjection_orthonormalProjector [CompleteSpace E] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (s : Finset ι) : IsStarProjection (orthonormalProjector 𝕜 v s) :=
  ⟨isIdempotentElem_orthonormalProjector hv s, isSelfAdjoint_orthonormalProjector v s⟩

/-- **`P† ∘ P = P` for an orthonormal projector.** Since `P = ∑ i ∈ s, |v i⟩⟨v i|` of an orthonormal
family is a star projection (`isStarProjection_orthonormalProjector`) — self-adjoint and idempotent
— its adjoint-composed-with-itself collapses to `P`. This is the `re tr(P† P ρ)` Born-trace
simplification (`p(m) = re tr(Mₘ ρ Mₘ†)` for a projective `Mₘ = P`), routed through the
`IsStarProjection.star_mul_self` API. -/
theorem orthonormalProjector_adjoint_comp_self [CompleteSpace E] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (s : Finset ι) :
    (ContinuousLinearMap.adjoint (orthonormalProjector 𝕜 v s)).comp (orthonormalProjector 𝕜 v s)
      = orthonormalProjector 𝕜 v s := by
  have hp := isStarProjection_orthonormalProjector hv s
  rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def, hp.isSelfAdjoint]
  exact hp.isIdempotentElem

/-- **Nielsen & Chuang, Exercise 2.23** (spectrum form). The spectrum of the projector
`P = ∑ i ∈ s, |v i⟩⟨v i|` of an orthonormal family is contained in `{0, 1}`: every spectral value —
in particular every eigenvalue — of a projector is `0` or `1`.

`P` is idempotent (`isIdempotentElem_orthonormalProjector`, Exercise 2.16), and the spectrum of any
idempotent element of a `𝕜`-algebra lies in `{0, 1}` (`IsIdempotentElem.spectrum_subset`). -/
theorem spectrum_orthonormalProjector_subset {v : ι → E} (hv : Orthonormal 𝕜 v) (s : Finset ι) :
    spectrum 𝕜 (orthonormalProjector 𝕜 v s) ⊆ {0, 1} :=
  (isIdempotentElem_orthonormalProjector hv s).spectrum_subset 𝕜

/-- **Nielsen & Chuang, Exercise 2.23** (eigenvalue form). Every eigenvalue `μ` of the projector
`P = ∑ i ∈ s, |v i⟩⟨v i|` of an orthonormal family is either `0` or `1`.

This is the eigenvalue-predicate reading of the exercise: `P`, viewed as a linear map, is idempotent
(the idempotence of the continuous linear map from `isIdempotentElem_orthonormalProjector`,
Exercise 2.16, transported along the coercion `E →L[𝕜] E → E →ₗ[𝕜] E`), and every eigenvalue of an
idempotent operator is `0` or `1`
(`Module.End.HasEigenvalue.eq_zero_or_one_of_isIdempotentElem`). -/
theorem orthonormalProjector_hasEigenvalue_eq_zero_or_one {v : ι → E} (hv : Orthonormal 𝕜 v)
    (s : Finset ι) {μ : 𝕜}
    (h : Module.End.HasEigenvalue (orthonormalProjector 𝕜 v s : E →ₗ[𝕜] E) μ) :
    μ = 0 ∨ μ = 1 := by
  refine h.eq_zero_or_one_of_isIdempotentElem ?_
  rw [IsIdempotentElem, ← ContinuousLinearMap.toLinearMap_mul,
    (isIdempotentElem_orthonormalProjector hv s).eq]

/-- **The projector sandwich collapses to a scalar** when `M`'s matrix in the family is scalar. For
the projector `P = ∑ i ∈ s, |v i⟩⟨v i|` of *any* family `v`, if the matrix elements
`⟪v i, M (v j)⟫` of an operator `M` equal a constant `c` on the diagonal (`i = j`) and vanish off
it, for all `i, j ∈ s`, then `P M P = c • P`. No orthonormality is needed.

This is the Knill–Laflamme reduction: for a code projector `P` onto a family of codewords, the
operator identity `P M P = c • P` is equivalent to the finite matrix-element conditions
`⟪v i, M (v j)⟫ = c δ_{ij}` — the shape in which `P Eₐ† E_b P = α_{ab} P` is verified (with
`M = Eₐ† E_b`, `c = α_{ab}`). Proved by evaluating both sides at `y`, expanding
`P M P y = ∑ᵢ ⟪v i, M (∑ⱼ ⟪v j, y⟫ • v j)⟫ • v i` (`orthonormalProjector_apply`), and collapsing the
inner `j`-sum to its `j = i` term by the hypotheses. -/
theorem orthonormalProjector_comp_comp_orthonormalProjector_eq_smul {v : ι → E} (s : Finset ι)
    {M : E →L[𝕜] E} {c : 𝕜}
    (hdiag : ∀ i ∈ s, (inner 𝕜 (v i) (M (v i)) : 𝕜) = c)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (inner 𝕜 (v i) (M (v j)) : 𝕜) = 0) :
    orthonormalProjector 𝕜 v s ∘L M ∘L orthonormalProjector 𝕜 v s
      = c • orthonormalProjector 𝕜 v s := by
  ext y
  simp only [ContinuousLinearMap.comp_apply, orthonormalProjector_apply, map_sum, map_smul,
    smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single_of_mem i hi
    (fun j hj hji => by rw [hoff j hj i hi hji, zero_smul, smul_zero]),
    hdiag i hi, smul_comm]

/-- **Trace of the orthonormal projector.** For an orthonormal basis `b` of `E`, the trace of
`P = ∑ i ∈ s, |b i⟩⟨b i|` is the size of `s` — the dimension of the subspace it projects onto:
`tr P = |s|`. Computed in the basis `b` (`LinearMap.trace_eq_sum_inner`), where `P` is diagonal with
a `0/1` spectrum (`orthonormalProjector_apply_eq_ite`), so the trace counts the `1`-eigenvalues. -/
theorem trace_orthonormalProjector [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)
    (s : Finset ι) :
    LinearMap.trace 𝕜 E (orthonormalProjector 𝕜 (⇑b) s : E →ₗ[𝕜] E) = (s.card : 𝕜) := by
  classical
  rw [LinearMap.trace_eq_sum_inner _ b]
  have hd : ∀ x, inner 𝕜 (b x) (orthonormalProjector 𝕜 (⇑b) s (b x))
      = if x ∈ s then (1 : 𝕜) else 0 := by
    intro x
    rw [orthonormalProjector_apply_eq_ite b.orthonormal]
    split_ifs with h
    · rw [orthonormal_iff_ite.mp b.orthonormal]; simp
    · rw [inner_zero_right]
  simp only [ContinuousLinearMap.coe_coe]
  rw [Finset.sum_congr rfl (fun x _ => hd x), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Trace of an orthonormal projector composed with an operator.** For an orthonormal basis `b`,
`tr(P ∘ D) = ∑ i ∈ s, ⟪b i, D (b i)⟫` where `P = ∑ i ∈ s, |b i⟩⟨b i|`: left-composing with the
projector restricts the trace to the diagonal entries of `D` over the projected indices `s`. Uses
self-adjointness of `P` (`isSelfAdjoint_orthonormalProjector`) to move it into the left inner slot
(`adjoint_inner_left`), then `orthonormalProjector_apply_eq_ite` keeps only the `s`-diagonal.
Specialises to `trace_orthonormalProjector` at `D = 1`, and is the projector-diagonalisation step
of a Born probability `re tr(P ρ)`. -/
theorem trace_orthonormalProjector_comp [CompleteSpace E] [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) (s : Finset ι) (D : E →L[𝕜] E) :
    LinearMap.trace 𝕜 E ((orthonormalProjector 𝕜 (⇑b) s).comp D : E →ₗ[𝕜] E)
      = ∑ i ∈ s, inner 𝕜 (b i) (D (b i)) := by
  classical
  rw [LinearMap.trace_eq_sum_inner _ b]
  have hd : ∀ x, inner 𝕜 (b x) (((orthonormalProjector 𝕜 (⇑b) s).comp D) (b x))
      = if x ∈ s then inner 𝕜 (b x) (D (b x)) else 0 := by
    intro x
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint, (isSelfAdjoint_orthonormalProjector (⇑b) s).star_eq,
      orthonormalProjector_apply_eq_ite b.orthonormal]
    split_ifs with h
    · rfl
    · rw [inner_zero_left]
  simp only [ContinuousLinearMap.coe_coe]
  rw [Finset.sum_congr rfl (fun x _ => hd x), Finset.sum_ite_mem, Finset.univ_inter]

/-- **The rank of the orthonormal projector `∑_{i ∈ s} |bᵢ⟩⟨bᵢ|` is `s.card`.** Being an idempotent,
`P = orthonormalProjector 𝕜 b s` is a projection onto its range, so its trace equals
`finrank (range P)` (`LinearMap.IsProj.trace`); and its trace is `s.card`
(`trace_orthonormalProjector`). Equating the two casts gives the rank. The ambient space is
finite-dimensional because `b` is a finite orthonormal basis. -/
theorem finrank_range_orthonormalProjector [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)
    (s : Finset ι) :
    Module.finrank 𝕜 (LinearMap.range (orthonormalProjector 𝕜 (⇑b) s : E →ₗ[𝕜] E)) = s.card := by
  have : FiniteDimensional 𝕜 E := b.toBasis.finiteDimensional_of_finite
  have hproj : LinearMap.IsProj (LinearMap.range (orthonormalProjector 𝕜 (⇑b) s : E →ₗ[𝕜] E))
      (orthonormalProjector 𝕜 (⇑b) s : E →ₗ[𝕜] E) :=
    LinearMap.IsIdempotentElem.isProj_range _
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap
        (isIdempotentElem_orthonormalProjector b.orthonormal s))
  have hcast :
      (Module.finrank 𝕜 (LinearMap.range (orthonormalProjector 𝕜 (⇑b) s : E →ₗ[𝕜] E)) : 𝕜)
        = (s.card : 𝕜) :=
    hproj.trace.symm.trans (trace_orthonormalProjector b s)
  exact_mod_cast hcast

end InnerProductSpace
