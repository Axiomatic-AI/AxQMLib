/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.RankOneSum
public import ToMathlib.Analysis.InnerProductSpace.Matricization
public import ToMathlib.Analysis.InnerProductSpace.PostMeasurement
public import ToMathlib.Analysis.InnerProductSpace.TraceNorm
public import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract

/-!
# The operator-sum (Kraus) map, and unitary freedom in its representation

For a finite family of operators `E : ι → (H →L[ℂ] G)` — each mapping an input
space `H` to an output space `G` — the **operator-sum map** sends an operator `ρ`
on `H` to
`Σᵢ Eᵢ ρ Eᵢ†`
on `G`. This is the algebraic core of the operator-sum (Kraus) representation of a
quantum operation (Nielsen–Chuang §8.2, Theorem 8.1): a quantum operation admits
the form `E(ρ) = Σᵢ Eᵢ ρ Eᵢ†` with `Σᵢ Eᵢ† Eᵢ ≤ 1`.

This file introduces the map as a `ℂ`-linear map `krausSumₗ` in the operator
argument and records the structural properties the representation rests on:

* `ContinuousLinearMap.krausSumₗ_isPositive` — the map sends positive operators to
  positive operators, each summand `Eᵢ ρ Eᵢ†` being a conjugate of `ρ`;
* `ContinuousLinearMap.trace_krausSumₗ` — the trace identity
  `tr(Σᵢ Eᵢ ρ Eᵢ†) = tr((Σᵢ Eᵢ† Eᵢ) ρ)`,
  the cyclicity computation behind the operator-sum trace condition
  `Σᵢ Eᵢ† Eᵢ ≤ 1` (which controls `tr[E(ρ)]`, N&C axiom A1);
* `ContinuousLinearMap.re_trace_krausSumₗ_le` — **axiom A1**: under the trace condition
  `Σᵢ Eᵢ† Eᵢ ≤ 1` the map is trace-non-increasing on positive operators,
  `re tr(Σᵢ Eᵢ ρ Eᵢ†) ≤ re tr ρ`, obtained from the trace identity and the general fact
  `ContinuousLinearMap.re_trace_mul_nonneg_of_nonneg` that `re tr(A B) ≥ 0` for positive `A, B`.

The single-summand building block `Eₘ(ρ) = Mₘ ρ Mₘ†` (with equal input/output
space) is `ContinuousLinearMap.postOp`; this file is its finite-sum, possibly
space-changing, generalization.

## Unitary freedom in the operator-sum representation (Theorem 8.2)

Two equal-size families `E`, `F` of operation elements on a *single* space `H` (the
"padded" form — pad the shorter list with zero operators so both are indexed by the common
`ι`) give **the same operator-sum map** iff their elements are related by a unitary coefficient
matrix — Nielsen & Chuang, **Theorem 8.2**:

* `ContinuousLinearMap.krausSumₗ_eq_iff_exists_mem_unitaryGroup` — **the theorem**:
  `krausSumₗ E = krausSumₗ F ↔ ∃ u ∈ Matrix.unitaryGroup ι ℂ, ∀ i, Eᵢ = ∑ j, uᵢⱼ • Fⱼ`.
* `ContinuousLinearMap.krausSumₗ_eq_of_mem_unitaryGroup` — the `⟸` direction on its own: a
  unitary mixing of the operation elements leaves the operator-sum map unchanged.

The proof reduces Theorem 8.2 to its ensemble analogue **Theorem 2.6**
(`InnerProductSpace.sum_rankOne_self_eq_iff_exists_mem_unitaryGroup`) through the **Choi /
vectorization bridge**. Vectorizing an operator against an orthonormal basis via the
matricization isomorphism, `vec A = (TensorProduct.matricize b).symm A = ∑ₖ (A bₖ) ⊗ bₖ`, the
Choi operator `∑ᵢ |vec Eᵢ⟩⟨vec Eᵢ|` on `H ⊗ H` is a fixed linear function of the operator-sum
map's values on the basis rank-one operators
(`ContinuousLinearMap.sum_rankOne_matricizeSymm_eq`), so equal operator-sum maps give equal
Choi operators; Theorem 2.6 supplies the relating unitary, and applying the linear equivalence
`matricize` transports it back to the operation elements. The converse is a direct star-algebra
computation collapsing `∑ᵢ uᵢⱼ conj uᵢₖ = δⱼₖ` by unitarity. The tensor-side building blocks are
the general lemmas `InnerProductSpace.rankOne_tmul_tmul` (beside `rankOne_tmul_self` in
`Mathlib.Analysis.InnerProductSpace.TensorProduct`) and `InnerProductSpace.rankOne_sum_sum` (beside
`rankOne_sum_smul_sum_smul` in `Mathlib.Analysis.InnerProductSpace.LinearMap`).

## Operator-sum from a dilation isometry (`LinearMap`)

Where the map above *packages* given operation elements, `LinearMap.krausOp` *produces* them from a
dilation `V : Hin →ₗ[𝕜] E ⊗ F` and an orthonormal basis `b` of the factor `F` to be traced out:
`krausOp b V k = ⟨b k| V`. Then `LinearMap.partialTraceRight_conj_eq_sum_krausOp` recovers the
operator sum `partialTraceRight b (V ρ V†) = ∑ₖ Eₖ ρ Eₖ†` (N&C Eqs. (8.9)–(8.10)), and, when `V` is
an isometry, `LinearMap.sum_adjoint_krausOp_comp_krausOp` gives the completeness relation
`∑ₖ Eₖ† Eₖ = 1` (N&C Eq. (8.14)) — the different-input/output-space form (Exercise 8.3).

## Operator-sum from an ancilla in a fixed pure state (`LinearMap`)

Where the dilation half takes the isometry `V` as given, this last half *produces the dilation* from
the physical ingredients: an environment (ancilla) prepared in a fixed pure state `ω` and a joint
unitary interaction. The **ancilla embedding** `tmulRightVec ω = (x ↦ x ⊗ₜ ω) : E →ₗ E ⊗ F` is the
general-vector analogue of `embedRight` (`embedRight b k = tmulRightVec (b k)`), with contraction
adjoint `contractRightVec ω = (x ⊗ₜ y ↦ ⟪ω, y⟫ • x)`.

* `LinearMap.adjoint_tmulRightVec` — `(tmulRightVec ω)† = contractRightVec ω`;
* `LinearMap.adjoint_tmulRightVec_comp_self` — `(tmulRightVec ω)† ∘ₗ tmulRightVec ω = 1` for a unit
  vector `ω` (the ancilla embedding is an isometry);
* `LinearMap.map_rankOne_eq_conj_tmulRightVec` — the key **ancilla-conjugation identity**
  `map A |ω⟩⟨ω| = tmulRightVec ω ∘ₗ A ∘ₗ (tmulRightVec ω)†`: preparing the environment in `|ω⟩` and
  tensoring is a conjugation by the single map `tmulRightVec ω`, which is what introduces the
  dilation `V`.

Assembling these with the dilation half gives the **environment-model operator-sum representation**
for a joint map `W : Hin ⊗ Anc →ₗ Eout ⊗ Fdisc` (the unitary interaction composed with any
reindexing of the enlarged space into a kept factor `Eout` and a discarded factor `Fdisc`), with
dilation `V = W ∘ₗ tmulRightVec ω`:

* `LinearMap.partialTraceRight_conj_map_rankOne_eq_sum_krausOp` — discarding `Fdisc` from
  `W (ρ ⊗ |ω⟩⟨ω|) W†` returns `∑ₖ Eₖ ρ Eₖ†` with `Eₖ = krausOp b (W ∘ₗ tmulRightVec ω)` (any `W`);
* `LinearMap.partialTraceRight_conj_map_sum_rankOne_eq_sum_krausOp` — the mixed-environment
  generalization (Nielsen–Chuang Eqs. (8.33)–(8.35)): for an ancilla operator `∑ⱼ |wⱼ⟩⟨wⱼ|` the
  result is the double sum `∑ⱼ ∑ₖ Eⱼₖ ρ Eⱼₖ†` with `Eⱼₖ = krausOp b (W ∘ₗ tmulRightVec (wⱼ))`;
* `LinearMap.sum_adjoint_krausOp_tmulRightVec_comp_krausOp` — `∑ₖ Eₖ† Eₖ = 1` when `W` is an
  isometry and `‖ω‖ = 1`.

Input space `Hin` and output space `Eout` need not agree, so this is exactly the different
input/output space operator-sum derivation of Nielsen–Chuang Exercise 8.3.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §8.2 (Theorems 8.1, 8.2; Exercise 8.3).
-/

open scoped InnerProductSpace TensorProduct

@[expose] public section

namespace ContinuousLinearMap

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]
  {ι : Type*} [Fintype ι]

/-- The **operator-sum (Kraus) map** of a finite family `E : ι → (H →L[ℂ] G)`, as a
`ℂ`-linear map in the operator argument: `ρ ↦ Σᵢ Eᵢ ρ Eᵢ†`. The individual summand
`Eᵢ ρ Eᵢ†` is `ContinuousLinearMap.postOp` in the equal-space case. -/
noncomputable def krausSumₗ (E : ι → H →L[ℂ] G) :
    (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G) where
  toFun ρ := ∑ i, (E i) ∘L ρ ∘L adjoint (E i)
  map_add' ρ σ := by
    simp only [add_comp, comp_add, Finset.sum_add_distrib]
  map_smul' c ρ := by
    simp only [smul_comp, comp_smul, RingHom.id_apply, Finset.smul_sum]

omit [FiniteDimensional ℂ H] [FiniteDimensional ℂ G] in
@[simp]
theorem krausSumₗ_apply (E : ι → H →L[ℂ] G) (ρ : H →L[ℂ] H) :
    krausSumₗ E ρ = ∑ i, (E i) ∘L ρ ∘L adjoint (E i) := rfl

omit [FiniteDimensional ℂ H] in
/-- The operator-sum map written with the C⋆-algebra product and star on `H →L[ℂ] H` (composition
`*` and adjoint `star`): `krausSumₗ E ρ = Σᵢ Eᵢ ρ Eᵢ⋆`. The `*`/`star` form of `krausSumₗ_apply`,
convenient for operator-algebra manipulations of the Kraus sum (e.g. quantum error-correction). -/
theorem krausSumₗ_eq_sum_mul_star (E : ι → H →L[ℂ] H) (ρ : H →L[ℂ] H) :
    krausSumₗ E ρ = ∑ i, E i * ρ * star (E i) := by
  rw [krausSumₗ_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_eq_adjoint, ← mul_def, ← mul_def, mul_assoc]

omit [FiniteDimensional ℂ H] [FiniteDimensional ℂ G] in
/-- The operator-sum map preserves positivity: `ρ ≥ 0 ⟹ Σᵢ Eᵢ ρ Eᵢ† ≥ 0`, each
summand being the conjugate `Eᵢ ρ Eᵢ†` of the positive operator `ρ`
(`ContinuousLinearMap.IsPositive.conj_adjoint`). -/
theorem krausSumₗ_isPositive (E : ι → H →L[ℂ] G) {ρ : H →L[ℂ] H}
    (hρ : ρ.IsPositive) : (krausSumₗ E ρ).IsPositive := by
  rw [krausSumₗ_apply]
  exact isPositive_sum Finset.univ fun i _ => hρ.conj_adjoint (E i)

omit [FiniteDimensional ℂ H] [FiniteDimensional ℂ G] in
/-- The operator-sum map preserves positivity, stated in the Loewner order:
`0 ≤ ρ ⟹ 0 ≤ Σᵢ Eᵢ ρ Eᵢ†`. The `0 ≤ ·` form of `krausSumₗ_isPositive`, matching the
order used for the operator-sum trace condition `Σᵢ Eᵢ† Eᵢ ≤ 1`. -/
theorem krausSumₗ_nonneg (E : ι → H →L[ℂ] G) {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ) :
    0 ≤ krausSumₗ E ρ :=
  nonneg_iff_isPositive.2 (krausSumₗ_isPositive E (nonneg_iff_isPositive.1 hρ))

/-- Cyclicity of the trace for a single summand: `tr(E ρ E†) = tr(E† E ρ)`, moving
the output-space factor `E` around the cycle back to the input space. -/
theorem trace_conj_adjoint (E : H →L[ℂ] G) (ρ : H →L[ℂ] H) :
    LinearMap.trace ℂ G ((E ∘L ρ ∘L adjoint E : G →L[ℂ] G) : G →ₗ[ℂ] G)
      = LinearMap.trace ℂ H ((adjoint E ∘L E ∘L ρ : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  simp only [ContinuousLinearMap.toLinearMap_comp]
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.trace_comp_comm',
    LinearMap.comp_assoc]

/-- **The operator-sum trace identity.** The trace of `Σᵢ Eᵢ ρ Eᵢ†` on the output
space equals the trace of `(Σᵢ Eᵢ† Eᵢ) ρ` on the input space:
`tr(Σᵢ Eᵢ ρ Eᵢ†) = tr((Σᵢ Eᵢ† Eᵢ) ρ)`. This is the algebraic content behind the
operator-sum trace condition `Σᵢ Eᵢ† Eᵢ ≤ 1`: it recasts `tr[E(ρ)]` as the pairing
of `ρ` with `Σᵢ Eᵢ† Eᵢ`. -/
theorem trace_krausSumₗ (E : ι → H →L[ℂ] G) (ρ : H →L[ℂ] H) :
    LinearMap.trace ℂ G ((krausSumₗ E ρ : G →L[ℂ] G) : G →ₗ[ℂ] G)
      = LinearMap.trace ℂ H
          (((∑ i, adjoint (E i) ∘L E i) ∘L ρ : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  rw [krausSumₗ_apply, ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.toLinearMap_sum,
    map_sum, ContinuousLinearMap.toLinearMap_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trace_conj_adjoint (E i) ρ, ← ContinuousLinearMap.comp_assoc]

/-- **The Kraus map of a completeness-satisfying family sends density operators to density
operators.** If `∑ᵢ Eᵢ† Eᵢ = I` and `ρ` is a density operator, then `∑ᵢ Eᵢ ρ Eᵢ†` is again a
density operator: positivity is `krausSumₗ_isPositive`, and the trace is
`tr(∑ᵢ Eᵢ ρ Eᵢ†) = tr((∑ᵢ Eᵢ† Eᵢ) ρ) = tr ρ = 1` (`trace_krausSumₗ` with the completeness
relation). This is the density-operator core of the trace-preserving (`∑ᵢ Eᵢ† Eᵢ = I`) case of the
operator-sum (Kraus) representation (Nielsen & Chuang, Theorem 8.1). -/
theorem isDensityOp_krausSumₗ (E : ι → H →L[ℂ] H)
    (hE : ∑ i, adjoint (E i) ∘L E i = 1) {ρ : H →L[ℂ] H} (hρ : ρ.IsDensityOp) :
    (krausSumₗ E ρ).IsDensityOp := by
  rw [isDensityOp_iff]
  refine ⟨krausSumₗ_isPositive E hρ.isPositive, ?_⟩
  rw [trace_krausSumₗ, hE, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  exact hρ.trace_eq_one

/-- **The trace of a product of positive operators has nonnegative real part.** For positive
operators `A, B` on a finite-dimensional complex Hilbert space, `0 ≤ re tr(A B)`. Writing
`tr(A B) = tr(√B · A · √B)` by sqrt-sandwich cyclicity (`trace_cfc_sqrt_sandwich_eq_trace_mul`),
the sandwich `√B · A · √B` is the conjugate of the positive operator `A` by the self-adjoint
`√B`, hence positive (`IsPositive.conj_adjoint`), so its trace has nonnegative real part
(the trace norm of a positive operator, `traceNorm_eq_re_trace_of_isPositive`). This is the
algebraic sign fact behind the operator-sum trace bound (N&C axiom A1). -/
theorem re_trace_mul_nonneg_of_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [CompleteSpace E] {A B : E →L[ℂ] E} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ RCLike.re (LinearMap.trace ℂ E ((A * B : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
  rw [← trace_cfc_sqrt_sandwich_eq_trace_mul hB A]
  have hApos : A.IsPositive := nonneg_iff_isPositive.mp hA
  have hpos : (cfc Real.sqrt B * A * cfc Real.sqrt B : E →L[ℂ] E).IsPositive := by
    have h := hApos.conj_adjoint (cfc Real.sqrt B)
    rw [(IsSelfAdjoint.cfc (a := B)).adjoint_eq, ← comp_assoc] at h
    simpa only [← mul_def] using h
  rw [← traceNorm_eq_re_trace_of_isPositive hpos]
  exact traceNorm_nonneg _

/-- **Trace monotonicity of the pairing against a positive operator.** For operators `A ≤ B` and a
positive operator `Q` on a finite-dimensional complex Hilbert space, `re tr(A Q) ≤ re tr(B Q)`:
pairing against `Q ≥ 0` is monotone in the Loewner order. The gap `re tr((B − A) Q) ≥ 0` is
nonnegative because `B − A ≥ 0` and `Q ≥ 0` (`re_trace_mul_nonneg_of_nonneg`), and the trace of the
difference splits by linearity. -/
theorem re_trace_mul_mono_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [CompleteSpace E] {A B Q : E →L[ℂ] E} (hAB : A ≤ B) (hQ : 0 ≤ Q) :
    RCLike.re (LinearMap.trace ℂ E ((A * Q : E →L[ℂ] E) : E →ₗ[ℂ] E)) ≤
      RCLike.re (LinearMap.trace ℂ E ((B * Q : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
  rw [← sub_nonneg, ← map_sub, ← map_sub, ← ContinuousLinearMap.toLinearMap_sub, ← sub_mul]
  exact re_trace_mul_nonneg_of_nonneg (sub_nonneg.mpr hAB) hQ

/-- **Cyclicity of the operator trace on continuous linear maps.** For operators `X, Y` on a
finite-dimensional complex inner product space, `tr(X Y) = tr(Y X)` — the `ContinuousLinearMap`
wrapper of `LinearMap.trace_mul_comm`, so trace-cyclicity can be cited directly on `→L[ℂ]`
operators (the `re`-part follows by `congrArg RCLike.re`). -/
theorem trace_mul_comm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (X Y : E →L[ℂ] E) :
    LinearMap.trace ℂ E ((X * Y : E →L[ℂ] E) : E →ₗ[ℂ] E)
      = LinearMap.trace ℂ E ((Y * X : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
  rw [ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm,
    ← ContinuousLinearMap.toLinearMap_mul]

/-- **Cyclicity of the real operator trace.** The `re`-part of `trace_mul_comm`:
`re tr(X Y) = re tr(Y X)` for operators `X, Y` on a finite-dimensional complex inner product
space. -/
theorem re_trace_mul_comm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (X Y : E →L[ℂ] E) :
    RCLike.re (LinearMap.trace ℂ E ((X * Y : E →L[ℂ] E) : E →ₗ[ℂ] E))
      = RCLike.re (LinearMap.trace ℂ E ((Y * X : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
  rw [ContinuousLinearMap.trace_mul_comm]

/-- **Trace of `(1 − X)·A` splits as `tr A − tr(X·A)`** (real part), the "error term = `1 −`
fidelity" decomposition: `(1 − X)·A = A − X·A`, and both `LinearMap.trace` and `RCLike.re` are
additive. -/
theorem re_trace_one_sub_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (X A : E →L[ℂ] E) :
    RCLike.re (LinearMap.trace ℂ E (↑((1 - X) * A) : E →ₗ[ℂ] E))
      = RCLike.re (LinearMap.trace ℂ E (↑A : E →ₗ[ℂ] E))
        - RCLike.re (LinearMap.trace ℂ E (↑(X * A) : E →ₗ[ℂ] E)) := by
  rw [show ((1 - X) * A) = A - X * A from by rw [sub_mul, one_mul],
    ContinuousLinearMap.toLinearMap_sub, map_sub, map_sub]

/-- **A self-adjoint idempotent (an orthogonal projection) is `≤ 1`** in the Loewner order.
`1 − P` is again a self-adjoint idempotent, hence positive
(`IsIdempotentElem.isPositive_iff_isSelfAdjoint`), so `0 ≤ 1 − P`, i.e. `P ≤ 1`. -/
theorem IsIdempotentElem.le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsIdempotentElem P)
    (hPsa : IsSelfAdjoint P) : P ≤ 1 := by
  have hsa : IsSelfAdjoint (1 - P) := by
    change star (1 - P) = 1 - P; rw [star_sub, star_one, hPsa.star_eq]
  have hpos : (1 - P).IsPositive :=
    (ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint hP.one_sub).mpr hsa
  exact sub_nonneg.mp (nonneg_iff_isPositive.mpr hpos)

/-- **A scalar Loewner bound gives a scalar trace bound.** If `A ≤ c • 1` and `Q ≥ 0` then
`re tr(A Q) ≤ c · re tr Q`. Immediate from `re_trace_mul_mono_left` (with `B = c • 1`) together with
`(c • 1) Q = c • Q` and `re tr(c • Q) = c · re tr Q`. Applied with `A = P ρ^⊗ⁿ P` the
equipartition-bounded compression of `ρ^⊗ⁿ` to its typical subspace, this is the false-decoding
decay `tr(P σ̄^⊗ⁿ P · Q) ≤ 2^{−n(S−ε)} tr Q` of the HSW random-coding error estimate
(Nielsen & Chuang, eq. 12.82). -/
theorem re_trace_mul_le_smul_of_le_smul_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E] {A Q : E →L[ℂ] E} {c : ℝ}
    (hA : A ≤ c • (1 : E →L[ℂ] E)) (hQ : 0 ≤ Q) :
    RCLike.re (LinearMap.trace ℂ E ((A * Q : E →L[ℂ] E) : E →ₗ[ℂ] E)) ≤
      c * RCLike.re (LinearMap.trace ℂ E ((Q : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
  refine (re_trace_mul_mono_left hA hQ).trans ?_
  rw [smul_mul_assoc, one_mul, ← Complex.coe_smul, ContinuousLinearMap.toLinearMap_smul, map_smul,
    smul_eq_mul]
  exact (RCLike.re_ofReal_mul c _).le

/-- **A sub-unital positive operator is below its own square root.** For `0 ≤ A ≤ 1` on a
complex Hilbert space, `A ≤ √A` (with `√· = cfc Real.sqrt ·`). Since `A` and
`√A` are both functions of `A` (hence commute), the Loewner order between them is the pointwise
order of the underlying scalar functions on `spectrum ℝ A`, and `x ≤ √x` holds on `[0, 1]`
(`Real.le_sqrt_of_sq_le`, reducing to `x² ≤ x` for `0 ≤ x ≤ 1`). The spectral hypotheses are `0 ≤ x`
(`spectrum_nonneg_of_nonneg`) and `x ≤ 1` (`le_algebraMap_iff_spectrum_le`, from `A ≤ 1`), and the
lift is `cfc_mono` against `cfc_id`. -/
theorem le_cfc_real_sqrt_of_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A : E →L[ℂ] E} (hA : 0 ≤ A) (hA1 : A ≤ 1) :
    A ≤ cfc Real.sqrt A := by
  have hspec_le : ∀ x ∈ spectrum ℝ A, x ≤ 1 :=
    (le_algebraMap_iff_spectrum_le (R := ℝ) (A := E →L[ℂ] E) (r := 1) (a := A)).mp
      (by simpa using hA1)
  have hpt : ∀ x ∈ spectrum ℝ A, (id x : ℝ) ≤ Real.sqrt x := by
    intro x hx
    simp only [id_eq]
    exact Real.le_sqrt_of_sq_le (by nlinarith [spectrum_nonneg_of_nonneg hA hx, hspec_le x hx])
  calc A = cfc id A := (cfc_id ℝ A).symm
    _ ≤ cfc Real.sqrt A := cfc_mono hpt

/-- **The Hilbert–Schmidt overlap of two sub-unital positive operators is at most their affinity.**
For `0 ≤ A ≤ 1` and `0 ≤ B ≤ 1` on a finite-dimensional complex Hilbert space,
`re tr(A B) ≤ re tr(√A √B)` (with `√· = cfc Real.sqrt ·`). Each operator is below its own square
root (`le_cfc_real_sqrt_of_le_one`, as `A, B ≤ 1`), so pairing against the positive `B` and then
against the positive `√A` and applying trace monotonicity (`re_trace_mul_mono_left`) twice — with
`re_trace_mul_comm` cycling the second pairing to the correct side — replaces `A` by `√A` and `B` by
`√B` in turn:
`re tr(A B) ≤ re tr(√A B) = re tr(B √A) ≤ re tr(√B √A) = re tr(√A √B)`.
Applied to two density operators (each `≤ 1`, `IsDensityOp.le_one`), this is the statement that the
Hilbert–Schmidt overlap `tr(ρ σ)` is dominated by the quantum affinity `tr(√ρ √σ)`. -/
theorem re_trace_mul_le_re_trace_cfc_sqrt_mul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E] {A B : E →L[ℂ] E}
    (hA : 0 ≤ A) (hA1 : A ≤ 1) (hB : 0 ≤ B) (hB1 : B ≤ 1) :
    RCLike.re (LinearMap.trace ℂ E ((A * B : E →L[ℂ] E) : E →ₗ[ℂ] E)) ≤
      RCLike.re (LinearMap.trace ℂ E
        ((cfc Real.sqrt A * cfc Real.sqrt B : E →L[ℂ] E) : E →ₗ[ℂ] E)) :=
  calc RCLike.re (LinearMap.trace ℂ E ((A * B : E →L[ℂ] E) : E →ₗ[ℂ] E))
      ≤ RCLike.re (LinearMap.trace ℂ E ((cfc Real.sqrt A * B : E →L[ℂ] E) : E →ₗ[ℂ] E)) :=
        re_trace_mul_mono_left (le_cfc_real_sqrt_of_le_one hA hA1) hB
    _ = RCLike.re (LinearMap.trace ℂ E ((B * cfc Real.sqrt A : E →L[ℂ] E) : E →ₗ[ℂ] E)) :=
        re_trace_mul_comm _ _
    _ ≤ RCLike.re (LinearMap.trace ℂ E
          ((cfc Real.sqrt B * cfc Real.sqrt A : E →L[ℂ] E) : E →ₗ[ℂ] E)) :=
        re_trace_mul_mono_left (le_cfc_real_sqrt_of_le_one hB hB1) (cfc_real_sqrt_nonneg A)
    _ = RCLike.re (LinearMap.trace ℂ E
          ((cfc Real.sqrt A * cfc Real.sqrt B : E →L[ℂ] E) : E →ₗ[ℂ] E)) :=
        re_trace_mul_comm _ _

/-- **Operator-sum trace bound — Nielsen–Chuang axiom A1.** If the operator-sum trace condition
`Σᵢ Eᵢ† Eᵢ ≤ 1` holds and `ρ` is positive, then the operator-sum map is trace-non-increasing:
`re tr(Σᵢ Eᵢ ρ Eᵢ†) ≤ re tr ρ`. Together with `tr ρ ≤ 1` this yields the physical bound
`tr[E(ρ)] ≤ 1`. Proof: `trace_krausSumₗ` recasts the left-hand trace as `tr((Σᵢ Eᵢ† Eᵢ) ρ)`;
with `A = Σᵢ Eᵢ† Eᵢ`, the operators `A ρ` and `(1 − A) ρ` sum to `ρ`, and `re tr((1 − A) ρ) ≥ 0`
by `re_trace_mul_nonneg_of_nonneg` (as `1 − A ≥ 0`), so `re tr(A ρ) ≤ re tr ρ`. -/
theorem re_trace_krausSumₗ_le (E : ι → H →L[ℂ] G) {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ)
    (hE : ∑ i, adjoint (E i) ∘L E i ≤ 1) :
    RCLike.re (LinearMap.trace ℂ G ((krausSumₗ E ρ : G →L[ℂ] G) : G →ₗ[ℂ] G))
      ≤ RCLike.re (LinearMap.trace ℂ H ((ρ : H →L[ℂ] H) : H →ₗ[ℂ] H)) := by
  rw [trace_krausSumₗ]
  set A := ∑ i, adjoint (E i) ∘L E i
  rw [← mul_def]
  have hcrux : 0 ≤ RCLike.re (LinearMap.trace ℂ H (((1 - A) * ρ : H →L[ℂ] H) : H →ₗ[ℂ] H)) :=
    re_trace_mul_nonneg_of_nonneg (sub_nonneg.mpr hE) hρ
  have hsum : (A * ρ + (1 - A) * ρ : H →L[ℂ] H) = ρ := by noncomm_ring
  have htr : RCLike.re (LinearMap.trace ℂ H ((A * ρ : H →L[ℂ] H) : H →ₗ[ℂ] H))
        + RCLike.re (LinearMap.trace ℂ H (((1 - A) * ρ : H →L[ℂ] H) : H →ₗ[ℂ] H))
      = RCLike.re (LinearMap.trace ℂ H ((ρ : H →L[ℂ] H) : H →ₗ[ℂ] H)) := by
    rw [← map_add, ← map_add, ← ContinuousLinearMap.toLinearMap_add, hsum]
  linarith [hcrux, htr]

omit [FiniteDimensional ℂ H] in
/-- **A trace-preserving Kraus family preserves the squared norm of every vector.** If the
operation elements satisfy the completeness relation `Σᵢ Eᵢ† Eᵢ = 1`, then `Σᵢ ‖Eᵢ ψ‖² = ‖ψ‖²`.
Each summand is `‖Eᵢ ψ‖² = re ⟪ψ, (Eᵢ† Eᵢ) ψ⟫` (`apply_norm_sq_eq_inner_adjoint_right`), and the
completeness relation collapses the sum to `re ⟪ψ, ψ⟫ = ‖ψ‖²`. -/
theorem sum_normSq_apply_of_sum_adjoint_mul_self_eq_one
    (E : ι → H →L[ℂ] H) (hE : ∑ i, adjoint (E i) * E i = 1) (ψ : H) :
    ∑ i, ‖E i ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  have key : ∑ i, ‖E i ψ‖ ^ 2 = RCLike.re (inner ℂ ψ ((∑ i, adjoint (E i) * E i) ψ)) := by
    rw [sum_apply, inner_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => apply_norm_sq_eq_inner_adjoint_right (E i) ψ
  rw [key, hE, one_apply_eq_self, inner_self_eq_norm_sq]

/-! ### Unitary freedom in the operator-sum representation (Nielsen–Chuang Theorem 8.2)

The results below are on a **single** space (`G = H`): two equal-size Kraus families give the same
operator-sum map iff they are unitarily related. -/

omit [CompleteSpace H] in
/-- **Choi expansion of a vectorized rank-one operator.** For an operator `A` and an orthonormal
basis `b`, the rank-one projector of the vectorization `vec A = (matricize b).symm A = ∑ₖ (A bₖ) ⊗
bₖ` expands, by bi-additivity and the tensor rank-one factorization, into a double sum of
tensor-product maps `∑ₖ ∑ₗ mapL |A bₖ⟩⟨A bₗ| |bₖ⟩⟨bₗ|`. -/
theorem rankOne_matricizeSymm_eq {κ : Type*} [Fintype κ] (b : OrthonormalBasis κ ℂ H)
    (A : H →L[ℂ] H) :
    (InnerProductSpace.rankOne ℂ ((TensorProduct.matricize b).symm A)
        ((TensorProduct.matricize b).symm A) : (H ⊗[ℂ] H) →L[ℂ] (H ⊗[ℂ] H))
      = ∑ k, ∑ l, TensorProduct.mapL (InnerProductSpace.rankOne ℂ (A (b k)) (A (b l)))
          (InnerProductSpace.rankOne ℂ (b k) (b l)) := by
  rw [TensorProduct.matricize_symm_apply, InnerProductSpace.rankOne_sum_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    InnerProductSpace.rankOne_tmul_tmul (A (b k)) (A (b l)) (b k) (b l)

/-- **The Choi operator of a Kraus family in terms of its operator-sum map.** Summing the rank-one
projectors of the vectorized operation elements produces the Choi operator on `H ⊗ H`, which equals
a fixed linear function of the operator-sum map evaluated on the basis rank-one operators:
`∑ᵢ |vec Eᵢ⟩⟨vec Eᵢ| = ∑ₖ ∑ₗ mapL (krausSumₗ E |bₖ⟩⟨bₗ|) |bₖ⟩⟨bₗ|`. This is the bridge that
makes the Choi operator depend on `E` **only through** its operator-sum map, so equal operator-sum
maps give equal Choi operators. -/
theorem sum_rankOne_matricizeSymm_eq {κ : Type*} [Fintype κ] (b : OrthonormalBasis κ ℂ H)
    (E : ι → H →L[ℂ] H) :
    (∑ i, InnerProductSpace.rankOne ℂ ((TensorProduct.matricize b).symm (E i))
        ((TensorProduct.matricize b).symm (E i)) : (H ⊗[ℂ] H) →L[ℂ] (H ⊗[ℂ] H))
      = ∑ k, ∑ l, TensorProduct.mapL (krausSumₗ E (InnerProductSpace.rankOne ℂ (b k) (b l)))
          (InnerProductSpace.rankOne ℂ (b k) (b l)) := by
  have hpost : ∀ (i : ι) (k l : κ),
      (E i) ∘L (InnerProductSpace.rankOne ℂ (b k) (b l)) ∘L adjoint (E i)
        = InnerProductSpace.rankOne ℂ (E i (b k)) (E i (b l)) := fun i k l => by
    simp only [InnerProductSpace.comp_rankOne, InnerProductSpace.rankOne_comp,
      ContinuousLinearMap.adjoint_adjoint]
  simp only [rankOne_matricizeSymm_eq, krausSumₗ_apply, TensorProduct.mapL_sum_left, hpost]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_comm]

omit [FiniteDimensional ℂ H] in
/-- **Unitary freedom, `⟸` direction (Nielsen & Chuang Theorem 8.2).** If the operation elements of
`E` are a unitary mixing of those of `F`, `Eᵢ = ∑ⱼ uᵢⱼ Fⱼ` for `u ∈ Matrix.unitaryGroup ι ℂ`, then
`E` and `F` have the same operator-sum map, `krausSumₗ E = krausSumₗ F`. Direct star-algebra
computation: expanding `∑ᵢ Eᵢ ρ Eᵢ†` bilinearly gives `∑ⱼ ∑ₖ (∑ᵢ uᵢⱼ conj uᵢₖ) • Fⱼ ρ Fₖ†`, and
`∑ᵢ uᵢⱼ conj uᵢₖ = (u⋆ u)ₖⱼ = δₖⱼ` by unitarity, leaving `∑ⱼ Fⱼ ρ Fⱼ†`. The operator analogue of
`sum_rankOne_self_eq_of_mem_unitaryGroup`. -/
theorem krausSumₗ_eq_of_mem_unitaryGroup [DecidableEq ι] {u : Matrix ι ι ℂ}
    (hu : u ∈ Matrix.unitaryGroup ι ℂ) {E F : ι → H →L[ℂ] H}
    (hEF : ∀ i, E i = ∑ j, u i j • F j) :
    krausSumₗ E = krausSumₗ F := by
  have key : ∀ j k : ι,
      (∑ i, u i j * (starRingEnd ℂ) (u i k)) = if k = j then (1 : ℂ) else 0 := by
    intro j k
    have h1 : (star u * u : Matrix ι ι ℂ) = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
    have h2 := congrFun (congrFun h1 k) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.star_apply, starRingEnd_apply]; ring
  refine LinearMap.ext fun ρ => ?_
  have hcomp : ∀ f : H →L[ℂ] H, f.comp (ρ.comp (adjoint f)) = f * ρ * star f :=
    fun f => by rw [star_eq_adjoint]; rfl
  calc krausSumₗ E ρ
      = ∑ i, (∑ j, u i j • F j) * ρ * star (∑ j, u i j • F j) := by
        simp only [krausSumₗ_apply, hcomp, hEF]
    _ = ∑ i, ∑ j, ∑ k, (u i j * (starRingEnd ℂ) (u i k)) • (F j * ρ * star (F k)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [star_sum]
        simp only [Finset.sum_mul, Finset.mul_sum, star_smul, RCLike.star_def, smul_mul_assoc,
          mul_smul_comm, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]
    _ = ∑ j, ∑ k, ∑ i, (u i j * (starRingEnd ℂ) (u i k)) • (F j * ρ * star (F k)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ k, (∑ i, u i j * (starRingEnd ℂ) (u i k)) • (F j * ρ * star (F k)) := by
        simp only [Finset.sum_smul]
    _ = ∑ j, ∑ k, (if k = j then (1 : ℂ) else 0) • (F j * ρ * star (F k)) := by simp only [key]
    _ = ∑ i, F i * ρ * star (F i) := by
        simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ = krausSumₗ F ρ := by simp only [krausSumₗ_apply, hcomp]

/-- **Unitary freedom in the operator-sum representation** (Nielsen & Chuang, *Quantum Computation
and Quantum Information*, **Theorem 8.2**). Two equal-size families `E`, `F` of operation elements
on a single finite-dimensional complex inner product space (the "padded" form — pad the shorter
list with zero operators so both are indexed by the common `ι`) give **the same operator-sum map**,
`krausSumₗ E = krausSumₗ F` (i.e. `∀ ρ, ∑ᵢ Eᵢ ρ Eᵢ† = ∑ⱼ Fⱼ ρ Fⱼ†`), **iff** their operation
elements are related by a unitary coefficient matrix `u ∈ Matrix.unitaryGroup ι ℂ`:
`Eᵢ = ∑ⱼ uᵢⱼ Fⱼ`.

The `⟸` direction is `krausSumₗ_eq_of_mem_unitaryGroup`. For `⟹`: the Choi operators
`∑ᵢ |vec Eᵢ⟩⟨vec Eᵢ|` and `∑ⱼ |vec Fⱼ⟩⟨vec Fⱼ|` on `H ⊗ H` (with `vec = (matricize b).symm` against
`b := stdOrthonormalBasis ℂ H`) are equal, since by `sum_rankOne_matricizeSymm_eq` each is the same
linear function of the (equal) operator-sum maps; the vector form of Theorem 2.6
(`InnerProductSpace.sum_rankOne_self_eq_iff_exists_mem_unitaryGroup`) then yields a unitary `u` with
`vec Eᵢ = ∑ⱼ uᵢⱼ vec Fⱼ`, and applying the linear equivalence `matricize b` gives
`Eᵢ = ∑ⱼ uᵢⱼ Fⱼ`. -/
theorem krausSumₗ_eq_iff_exists_mem_unitaryGroup [DecidableEq ι] {E F : ι → H →L[ℂ] H} :
    krausSumₗ E = krausSumₗ F ↔
      ∃ u ∈ Matrix.unitaryGroup ι ℂ, ∀ i, E i = ∑ j, u i j • F j := by
  refine ⟨fun h => ?_, fun ⟨u, hu, hEF⟩ => krausSumₗ_eq_of_mem_unitaryGroup hu hEF⟩
  have : CompleteSpace (H ⊗[ℂ] H) := FiniteDimensional.completeSpace ℂ _
  set b := stdOrthonormalBasis ℂ H with hb
  have hchoi : (∑ i, InnerProductSpace.rankOne ℂ ((TensorProduct.matricize b).symm (E i))
        ((TensorProduct.matricize b).symm (E i)) : (H ⊗[ℂ] H) →L[ℂ] (H ⊗[ℂ] H))
      = ∑ i, InnerProductSpace.rankOne ℂ ((TensorProduct.matricize b).symm (F i))
        ((TensorProduct.matricize b).symm (F i)) := by
    rw [sum_rankOne_matricizeSymm_eq b E, sum_rankOne_matricizeSymm_eq b F, h]
  obtain ⟨u, hu, hrel⟩ :=
    (InnerProductSpace.sum_rankOne_self_eq_iff_exists_mem_unitaryGroup _ _).mp hchoi
  refine ⟨u, hu, fun i => ?_⟩
  refine (TensorProduct.matricize b).symm.injective ?_
  rw [map_sum]
  simp only [map_smul]
  exact hrel i

end ContinuousLinearMap

namespace LinearMap

section KrausFromDilation

variable {𝕜 Hin E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Hin] [InnerProductSpace 𝕜 Hin] [FiniteDimensional 𝕜 Hin]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {ι : Type*} [Fintype ι]

/-- The `k`-th **operation element** (Kraus operator) of a dilation `V : Hin →ₗ E ⊗ F` relative to
an orthonormal basis `b` of the traced-out factor `F`: `Eₖ = ⟨b k| V`, that is
`restrictRight b k ∘ₗ V : Hin →ₗ E`, the map `V` followed by contracting the `F`-slot against `b k`.
Its input space `Hin` and output space `E` need not agree. -/
noncomputable def krausOp (b : OrthonormalBasis ι 𝕜 F) (V : Hin →ₗ[𝕜] E ⊗[𝕜] F) (k : ι) :
    Hin →ₗ[𝕜] E :=
  restrictRight b k ∘ₗ V

omit [FiniteDimensional 𝕜 Hin] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
@[simp]
theorem krausOp_apply (b : OrthonormalBasis ι 𝕜 F) (V : Hin →ₗ[𝕜] E ⊗[𝕜] F) (k : ι) (x : Hin) :
    krausOp b V k x = restrictRight b k (V x) := rfl

/-- The adjoint of the `k`-th operation element: `Eₖ† = V† ∘ₗ embedRight b k`. Since `restrictRight`
and `embedRight` are mutual adjoints (`adjoint_restrictRight`), `Eₖ† = (restrictRight b k ∘ₗ V)†`
distributes to `V† ∘ₗ (restrictRight b k)† = V† ∘ₗ embedRight b k`. -/
theorem adjoint_krausOp (b : OrthonormalBasis ι 𝕜 F) (V : Hin →ₗ[𝕜] E ⊗[𝕜] F) (k : ι) :
    adjoint (krausOp b V k) = adjoint V ∘ₗ embedRight b k := by
  rw [krausOp, adjoint_comp, adjoint_restrictRight]

/-- **Operator-sum representation from a dilation** (Nielsen–Chuang Eqs. (8.9)–(8.10)). Tracing out
the factor `F` from the conjugation `V ρ V†` returns the operator sum `∑ₖ Eₖ ρ Eₖ†` over the
operation elements `Eₖ = krausOp b V k`:
`partialTraceRight b (V ∘ₗ ρ ∘ₗ V†) = ∑ k, krausOp b V k ∘ₗ ρ ∘ₗ (krausOp b V k)†`.
No hypothesis on `V` is required. Unfolding `partialTraceRight` as
`∑ k, restrictRight b k ∘ₗ · ∘ₗ embedRight b k`, each summand is `Eₖ ρ Eₖ†` after re-associating and
rewriting `V† ∘ₗ embedRight b k` as `Eₖ†` via `adjoint_krausOp`. -/
theorem partialTraceRight_conj_eq_sum_krausOp (b : OrthonormalBasis ι 𝕜 F)
    (V : Hin →ₗ[𝕜] E ⊗[𝕜] F) (ρ : Hin →ₗ[𝕜] Hin) :
    partialTraceRight b (V ∘ₗ ρ ∘ₗ adjoint V) =
      ∑ k, krausOp b V k ∘ₗ ρ ∘ₗ adjoint (krausOp b V k) := by
  rw [partialTraceRight_eq_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [adjoint_krausOp, krausOp]
  simp only [comp_assoc]

/-- **Completeness relation** (Nielsen–Chuang Eq. (8.14)). If the dilation `V` is an isometry
(`V† ∘ₗ V = 1`) then the operation elements satisfy `∑ₖ Eₖ† Eₖ = 1`; this is precisely the condition
that makes `ρ ↦ partialTraceRight b (V ρ V†)` trace preserving. Writing `Eₖ† Eₖ =
V† ∘ₗ (embedRight b k ∘ₗ restrictRight b k) ∘ₗ V` and summing, the resolution of identity
`∑ k, embedRight b k ∘ₗ restrictRight b k = 1` (`sum_embedRight_restrictRight_eq_self`) collapses
the middle factor, leaving `V† ∘ₗ V = 1`. -/
theorem sum_adjoint_krausOp_comp_krausOp (b : OrthonormalBasis ι 𝕜 F)
    (V : Hin →ₗ[𝕜] E ⊗[𝕜] F) (hV : adjoint V ∘ₗ V = id) :
    ∑ k, adjoint (krausOp b V k) ∘ₗ krausOp b V k = id := by
  simp only [krausOp, adjoint_comp, adjoint_restrictRight]
  ext x
  simp only [LinearMap.sum_apply, comp_apply, id_apply]
  rw [← map_sum, sum_embedRight_restrictRight_eq_self]
  exact LinearMap.congr_fun hV x

/-! ### The projected environment operator-sum (block-selected operation elements)

Refining `partialTraceRight_conj_eq_sum_krausOp`: conjugating `V ρ V†` by an *environment block
projector* `P_S = ∑_{σ∈S} |b σ⟩⟨b σ|` (as `1 ⊗ P_S`) before tracing out the environment selects
exactly the operation elements indexed by a subset `S ⊆ ι`, `∑_{σ∈S} Eₖ ρ Eₖ†`. This is the
algebraic content of *measuring the block projector `P_S` on the environment, then discarding it*
(Nielsen–Chuang Exercise 8.9). The dilation `krausDilation` that assembles `V` from a prescribed
Kraus family — the converse construction shared with Exercise 8.8 — lives in
`ToMathlib.Analysis.InnerProductSpace.OperatorSumDilation`. -/

omit [FiniteDimensional 𝕜 Hin] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- **Contracting a block projector against a basis vector.** For the environment block projector
`P_S = ∑_{σ∈S} embedRight b σ ∘ₗ restrictRight b σ` (i.e. `1 ⊗ ∑_{σ∈S} |b σ⟩⟨b σ|`),
`restrictRight b τ ∘ₗ P_S = restrictRight b τ` when `τ ∈ S` and `0` otherwise. Each summand
`restrictRight b τ ∘ₗ embedRight b σ ∘ₗ restrictRight b σ` collapses to `if τ = σ then restrictRight
b τ else 0` (`restrictRight_comp_embedRight`), and summing over `σ ∈ S` keeps only `σ = τ`. -/
theorem restrictRight_comp_proj [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 F) (S : Finset ι)
    (τ : ι) :
    (restrictRight b τ : E ⊗[𝕜] F →ₗ[𝕜] E) ∘ₗ (∑ σ ∈ S, embedRight b σ ∘ₗ restrictRight b σ)
      = if τ ∈ S then restrictRight b τ else 0 := by
  refine LinearMap.ext fun w => ?_
  rw [comp_apply, LinearMap.sum_apply, map_sum]
  simp only [comp_apply]
  have hterm : ∀ σ, restrictRight b τ (embedRight b σ (restrictRight b σ w))
      = if τ = σ then restrictRight b τ w else 0 := by
    intro σ
    rw [← comp_apply (restrictRight b τ) (embedRight b σ), restrictRight_comp_embedRight]
    by_cases h : τ = σ <;> simp [h]
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ), Finset.sum_ite_eq]
  by_cases hτ : τ ∈ S <;> simp [hτ]

omit [FiniteDimensional 𝕜 Hin] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- **The block-diagonal environment projector as a tensor map.** The summand
`embedRight b σ ∘ₗ restrictRight b σ` is `1 ⊗ |b σ⟩⟨b σ|`, i.e.
`TensorProduct.map id (rankOne 𝕜 (b σ) (b σ))`. The bridge from the `embedRight`/`restrictRight`
form used here to the `TensorProduct.map`/rank-one form a physical measurement operator takes. -/
theorem embedRight_comp_restrictRight_eq_map_rankOne (b : OrthonormalBasis ι 𝕜 F) (σ : ι) :
    (embedRight b σ ∘ₗ restrictRight b σ : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F)
      = TensorProduct.map LinearMap.id (InnerProductSpace.rankOne 𝕜 (b σ) (b σ)).toLinearMap := by
  refine TensorProduct.ext' fun x y => ?_
  simp only [comp_apply, restrictRight_tmul, map_smul, embedRight_apply, TensorProduct.map_tmul,
    id_coe, id_eq, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
    TensorProduct.tmul_smul]

/-- **The environment block projector is self-adjoint.** For the block projector
`P_S = ∑_{σ∈S} embedRight b σ ∘ₗ restrictRight b σ` (`= 1 ⊗ ∑_{σ∈S} |b σ⟩⟨b σ|`), `P_S† = P_S`.
Each block `embedRight b σ ∘ₗ restrictRight b σ = 1 ⊗ |b σ⟩⟨b σ|` is a self-adjoint rank-one
projector on the environment factor (`embedRight`/`restrictRight` are mutual adjoints,
`adjoint_restrictRight`), and adjoint distributes over the sum. -/
theorem adjoint_sum_embedRight_comp_restrictRight (b : OrthonormalBasis ι 𝕜 F) (S : Finset ι) :
    adjoint (∑ σ ∈ S, (embedRight b σ ∘ₗ restrictRight b σ : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F))
      = ∑ σ ∈ S, (embedRight b σ ∘ₗ restrictRight b σ : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [adjoint_comp, adjoint_restrictRight, ← adjoint_restrictRight b σ, adjoint_adjoint]

/-- **Projected environment operator-sum** (Nielsen–Chuang Exercise 8.9). Conjugating `V ρ V†` by
the environment block projector `P_S = ∑_{σ∈S} embedRight b σ ∘ₗ restrictRight b σ`
(`= 1 ⊗ ∑_{σ∈S} |b σ⟩⟨b σ|`) on both sides and tracing out the environment returns the operator sum
over the *selected* operation elements only:
`partialTraceRight b (P_S (V ρ V†) P_S) = ∑_{σ∈S} Eₖ ρ Eₖ†` with `Eₖ = krausOp b V σ`. This is what
"measure the block projector `P_S`, then discard the environment" computes. Proof: `P_S` is
self-adjoint, so `P_S (V ρ V†) P_S = (P_S V) ρ (P_S V)†`; the operation elements of `P_S V` are
`if σ ∈ S then krausOp b V σ else 0` (`restrictRight_comp_proj`), so
`partialTraceRight_conj_eq_sum_krausOp` yields the sum over all `σ` of the block-restricted
elements, and the `σ ∉ S` terms vanish. -/
theorem partialTraceRight_conj_sum_proj_eq_sum_krausOp
    (b : OrthonormalBasis ι 𝕜 F) (V : Hin →ₗ[𝕜] E ⊗[𝕜] F) (ρ : Hin →ₗ[𝕜] Hin) (S : Finset ι) :
    partialTraceRight b
        ((∑ σ ∈ S, embedRight b σ ∘ₗ restrictRight b σ) ∘ₗ (V ∘ₗ ρ ∘ₗ adjoint V) ∘ₗ
          (∑ σ ∈ S, embedRight b σ ∘ₗ restrictRight b σ))
      = ∑ σ ∈ S, krausOp b V σ ∘ₗ ρ ∘ₗ adjoint (krausOp b V σ) := by
  classical
  set P : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F := ∑ σ ∈ S, embedRight b σ ∘ₗ restrictRight b σ with hP
  have hPsa : adjoint P = P := hP ▸ adjoint_sum_embedRight_comp_restrictRight b S
  have hkraus : ∀ τ, krausOp b (P ∘ₗ V) τ = if τ ∈ S then krausOp b V τ else 0 := fun τ => by
    rw [krausOp, ← comp_assoc, hP, restrictRight_comp_proj]
    by_cases hτ : τ ∈ S <;> simp [hτ, krausOp]
  have hconj : P ∘ₗ (V ∘ₗ ρ ∘ₗ adjoint V) ∘ₗ P = (P ∘ₗ V) ∘ₗ ρ ∘ₗ adjoint (P ∘ₗ V) := by
    rw [adjoint_comp, hPsa]; simp only [comp_assoc]
  rw [hconj, partialTraceRight_conj_eq_sum_krausOp]
  have hpush : ∀ τ, krausOp b (P ∘ₗ V) τ ∘ₗ ρ ∘ₗ adjoint (krausOp b (P ∘ₗ V) τ)
      = if τ ∈ S then krausOp b V τ ∘ₗ ρ ∘ₗ adjoint (krausOp b V τ) else 0 := fun τ => by
    rw [hkraus τ]; by_cases hτ : τ ∈ S <;> simp [hτ]
  rw [Finset.sum_congr rfl (fun τ _ => hpush τ), Finset.sum_ite_mem, Finset.univ_inter]

end KrausFromDilation

section AncillaDilation

/-! ### The dilation from an ancilla in a fixed pure state

The dilation `V` of the operator-sum representation arises physically from an ancilla (environment)
prepared in a fixed pure state `|ω⟩` and a joint unitary. This subsection isolates the two
facts that turn "conjugate by a joint isometry, with the ancilla slot occupied by `|ω⟩⟨ω|`" into the
dilation form `V ρ V†` of `KrausFromDilation`: the ancilla embedding `x ↦ x ⊗ₜ ω` and its
conjugation identity.
-/

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The **ancilla embedding**: tensoring with a fixed vector `ω : F`, `x ↦ x ⊗ₜ ω`, as a linear map
`E →ₗ E ⊗ F`. The general-vector analogue of `embedRight` (`embedRight b k = tmulRightVec (b k)`):
it packages a fixed environment state `ω` alongside the principal input. -/
noncomputable def tmulRightVec (ω : F) : E →ₗ[𝕜] E ⊗[𝕜] F :=
  (TensorProduct.mk 𝕜 E F).flip ω

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
@[simp]
theorem tmulRightVec_apply (ω : F) (x : E) : tmulRightVec ω x = x ⊗ₜ[𝕜] ω := rfl

/-- The **contraction against a fixed vector** `ω : F`, `x ⊗ₜ y ↦ ⟪ω, y⟫ • x`, as a linear map
`E ⊗ F →ₗ E`. The general-vector analogue of `restrictRight`; it is the adjoint of `tmulRightVec ω`
(`adjoint_tmulRightVec`). -/
noncomputable def contractRightVec (ω : F) : E ⊗[𝕜] F →ₗ[𝕜] E :=
  (TensorProduct.rid 𝕜 E).toLinearMap ∘ₗ TensorProduct.map LinearMap.id (innerSL 𝕜 ω).toLinearMap

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
@[simp]
theorem contractRightVec_tmul (ω : F) (x : E) (y : F) :
    contractRightVec ω (x ⊗ₜ[𝕜] y) = ⟪ω, y⟫_𝕜 • x := rfl

/-- **Adjoint of the ancilla embedding** is the contraction:
`(tmulRightVec ω)† = contractRightVec ω`. Mirrors `adjoint_embedRight`; proved by the inner-product
characterization on pure tensors, `⟪x ⊗ₜ ω, a ⊗ₜ b⟫ = ⟪x, ⟪ω, b⟫ • a⟫`. -/
theorem adjoint_tmulRightVec (ω : F) :
    adjoint (tmulRightVec ω : E →ₗ[𝕜] E ⊗[𝕜] F) = contractRightVec ω := by
  rw [eq_comm, LinearMap.eq_adjoint_iff]
  intro v u
  refine v.inductionOn ?_ ?_
  · intro x y
    simp [tmulRightVec_apply, contractRightVec_tmul, TensorProduct.inner_tmul, inner_smul_left,
      mul_comm]
  · intro a b ha hb
    simp [inner_add_left, map_add, ha, hb]

/-- **The ancilla embedding is an isometry** when `ω` is a unit vector:
`(tmulRightVec ω)† ∘ₗ tmulRightVec ω = 1`. This is what makes the assembled dilation `V` an
isometry, hence the operation elements complete
(`sum_adjoint_krausOp_tmulRightVec_comp_krausOp`). -/
theorem adjoint_tmulRightVec_comp_self {ω : F} (hω : ‖ω‖ = 1) :
    adjoint (tmulRightVec ω : E →ₗ[𝕜] E ⊗[𝕜] F) ∘ₗ tmulRightVec ω = LinearMap.id := by
  rw [adjoint_tmulRightVec]
  ext x
  simp only [coe_comp, Function.comp_apply, tmulRightVec_apply, contractRightVec_tmul, id_coe,
    id_eq]
  rw [inner_self_eq_norm_sq_to_K, hω]
  simp

/-- **Ancilla conjugation as a dilation.** Tensoring an operator `A` on `E` with the rank-one
projector `|ω⟩⟨ω|` on the ancilla factor `F` equals conjugation of `A` by the ancilla embedding:
`map A |ω⟩⟨ω| = tmulRightVec ω ∘ₗ A ∘ₗ (tmulRightVec ω)†`. Preparing the environment in the fixed
pure state `|ω⟩` and conjugating is therefore a conjugation by the single map `tmulRightVec ω` — the
algebraic step that introduces the dilation `V`. Proved by evaluation on pure tensors. -/
theorem map_rankOne_eq_conj_tmulRightVec (A : E →ₗ[𝕜] E) (ω : F) :
    TensorProduct.map A (InnerProductSpace.rankOne 𝕜 ω ω).toLinearMap
      = tmulRightVec ω ∘ₗ A ∘ₗ adjoint (tmulRightVec ω) := by
  rw [adjoint_tmulRightVec]
  refine TensorProduct.ext' fun x y ↦ ?_
  simp only [TensorProduct.map_tmul, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
    coe_comp, Function.comp_apply, contractRightVec_tmul, map_smul, tmulRightVec_apply,
    TensorProduct.tmul_smul]

end AncillaDilation

section EnvironmentModel

/-! ### The environment-model operator-sum representation

Combining the ancilla embedding with `KrausFromDilation`: for a joint map
`W : Hin ⊗ Anc →ₗ Eout ⊗ Fdisc` (the unitary interaction followed by any reindexing of the enlarged
space into a "kept" factor `Eout` and a "discarded" factor `Fdisc`) and an environment prepared in a
fixed pure state `ω : Anc`, the dilation is `V = W ∘ₗ tmulRightVec ω : Hin →ₗ Eout ⊗ Fdisc`. Input
space `Hin` and output space `Eout` need not agree — the general operator-sum derivation of
Nielsen–Chuang §8.2 / Exercise 8.3.
-/

variable {𝕜 Hin Anc Eout Fdisc : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Hin] [InnerProductSpace 𝕜 Hin] [FiniteDimensional 𝕜 Hin]
  [NormedAddCommGroup Anc] [InnerProductSpace 𝕜 Anc] [FiniteDimensional 𝕜 Anc]
  [NormedAddCommGroup Eout] [InnerProductSpace 𝕜 Eout] [FiniteDimensional 𝕜 Eout]
  [NormedAddCommGroup Fdisc] [InnerProductSpace 𝕜 Fdisc] [FiniteDimensional 𝕜 Fdisc]
  {ι : Type*} [Fintype ι]

/-- **Operator-sum representation of the environment model** (Nielsen–Chuang Eqs. (8.9)–(8.10), the
different input/output space case). Discarding the factor `Fdisc` from the conjugation of the
ancilla-extended input `ρ ⊗ |ω⟩⟨ω|` by a joint map `W : Hin ⊗ Anc →ₗ Eout ⊗ Fdisc` returns the
operator sum over the operation elements `Eₖ = krausOp b (W ∘ₗ tmulRightVec ω)`:
`partialTraceRight b (W (map ρ |ω⟩⟨ω|) W†) = ∑ₖ Eₖ ρ Eₖ†`. No hypothesis on `W` or `ω`. Folds the
ancilla conjugation into `V = W ∘ₗ tmulRightVec ω` via `map_rankOne_eq_conj_tmulRightVec`, then
applies `partialTraceRight_conj_eq_sum_krausOp`. -/
theorem partialTraceRight_conj_map_rankOne_eq_sum_krausOp
    (b : OrthonormalBasis ι 𝕜 Fdisc) (W : (Hin ⊗[𝕜] Anc) →ₗ[𝕜] Eout ⊗[𝕜] Fdisc)
    (ω : Anc) (ρ : Hin →ₗ[𝕜] Hin) :
    partialTraceRight b
        (W ∘ₗ TensorProduct.map ρ (InnerProductSpace.rankOne 𝕜 ω ω).toLinearMap ∘ₗ adjoint W)
      = ∑ k, krausOp b (W ∘ₗ tmulRightVec ω) k ∘ₗ ρ ∘ₗ
          adjoint (krausOp b (W ∘ₗ tmulRightVec ω) k) := by
  rw [← partialTraceRight_conj_eq_sum_krausOp]
  congr 1
  rw [map_rankOne_eq_conj_tmulRightVec, adjoint_comp]
  simp only [comp_assoc]

/-- **Projected environment-model operator-sum** (Nielsen–Chuang Exercise 8.9): the block-selected
(`partialTraceRight_conj_sum_proj_eq_sum_krausOp`) *and* ancilla-prepared
(`partialTraceRight_conj_map_rankOne_eq_sum_krausOp`) form. Prepare the ancilla in the fixed pure
state `|ω⟩`, conjugate the ancilla-extended input `ρ ⊗ |ω⟩⟨ω|` by a joint map
`W : Hin ⊗ Anc →ₗ Eout ⊗ Fdisc`, then measure the environment block projector
`P_S = ∑_{σ∈S} embedRight b σ ∘ₗ restrictRight b σ` (`= 1 ⊗ ∑_{σ∈S} |b σ⟩⟨b σ|`) and discard
`Fdisc`; this returns the operator sum over exactly the *selected* operation elements
`Eₖ = krausOp b (W ∘ₗ tmulRightVec ω)`:
`partialTraceRight b (P_S (W (ρ ⊗ |ω⟩⟨ω|) W†) P_S) = ∑_{σ∈S} E_σ ρ E_σ†`. No hypothesis on `W`/`ω`.
Folds the ancilla conjugation into the dilation `V = W ∘ₗ tmulRightVec ω`
(`map_rankOne_eq_conj_tmulRightVec`), then applies the projected dilation lemma
`partialTraceRight_conj_sum_proj_eq_sum_krausOp`. This is the tool behind Exercise 8.9's
measurement model: "perform `U` on `ρ ⊗ |e₀⟩⟨e₀|`, then measure the environment projector `Pₘ`". -/
theorem partialTraceRight_conj_sum_proj_map_rankOne_eq_sum_krausOp
    (b : OrthonormalBasis ι 𝕜 Fdisc) (W : (Hin ⊗[𝕜] Anc) →ₗ[𝕜] Eout ⊗[𝕜] Fdisc)
    (ω : Anc) (ρ : Hin →ₗ[𝕜] Hin) (S : Finset ι) :
    partialTraceRight b
        ((∑ σ ∈ S, embedRight b σ ∘ₗ restrictRight b σ) ∘ₗ
          (W ∘ₗ TensorProduct.map ρ (InnerProductSpace.rankOne 𝕜 ω ω).toLinearMap ∘ₗ adjoint W) ∘ₗ
          (∑ σ ∈ S, embedRight b σ ∘ₗ restrictRight b σ))
      = ∑ σ ∈ S, krausOp b (W ∘ₗ tmulRightVec ω) σ ∘ₗ ρ ∘ₗ
          adjoint (krausOp b (W ∘ₗ tmulRightVec ω) σ) := by
  have hmix :
      W ∘ₗ TensorProduct.map ρ (InnerProductSpace.rankOne 𝕜 ω ω).toLinearMap ∘ₗ adjoint W
        = (W ∘ₗ tmulRightVec ω) ∘ₗ ρ ∘ₗ adjoint (W ∘ₗ tmulRightVec ω) := by
    rw [map_rankOne_eq_conj_tmulRightVec, adjoint_comp]
    simp only [comp_assoc]
  rw [hmix, partialTraceRight_conj_sum_proj_eq_sum_krausOp]

/-- **Operator-sum representation of the environment model for a mixed environment state**
(Nielsen–Chuang Eqs. (8.33)–(8.35)). The mixed generalization of
`partialTraceRight_conj_map_rankOne_eq_sum_krausOp`: when the environment carries a positive
operator written as a finite sum of rank-one terms `∑ⱼ |wⱼ⟩⟨wⱼ|` (an ensemble decomposition of the
density operator, with the weights `√qⱼ` absorbed into the `wⱼ`), discarding `Fdisc` from the
conjugation of `ρ ⊗ (∑ⱼ |wⱼ⟩⟨wⱼ|)` by a joint map `W : Hin ⊗ Anc →ₗ Eout ⊗ Fdisc` returns the double
operator sum over the operation elements `Eⱼₖ = krausOp b (W ∘ₗ tmulRightVec (wⱼ))`:
`partialTraceRight b (W (map ρ (∑ⱼ |wⱼ⟩⟨wⱼ|)) W†) = ∑ⱼ ∑ₖ Eⱼₖ ρ Eⱼₖ†`. No hypothesis on `W` or the
`wⱼ`. Distributes the sum through `TensorProduct.map`, the outer conjugation, and the (linear)
partial trace, then applies the pure-state case termwise. -/
theorem partialTraceRight_conj_map_sum_rankOne_eq_sum_krausOp {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι 𝕜 Fdisc) (W : (Hin ⊗[𝕜] Anc) →ₗ[𝕜] Eout ⊗[𝕜] Fdisc)
    (w : κ → Anc) (ρ : Hin →ₗ[𝕜] Hin) :
    partialTraceRight b
        (W ∘ₗ TensorProduct.map ρ (∑ j, (InnerProductSpace.rankOne 𝕜 (w j) (w j)).toLinearMap)
          ∘ₗ adjoint W)
      = ∑ j, ∑ k, krausOp b (W ∘ₗ tmulRightVec (w j)) k ∘ₗ ρ
          ∘ₗ adjoint (krausOp b (W ∘ₗ tmulRightVec (w j)) k) := by
  rw [← partialTraceRightLM_apply]
  have hcomp : W ∘ₗ TensorProduct.map ρ (∑ j, (InnerProductSpace.rankOne 𝕜 (w j) (w j)).toLinearMap)
        ∘ₗ adjoint W
      = ∑ j, (W ∘ₗ TensorProduct.map ρ (InnerProductSpace.rankOne 𝕜 (w j) (w j)).toLinearMap
          ∘ₗ adjoint W) := by
    have hmap : TensorProduct.map ρ (∑ j, (InnerProductSpace.rankOne 𝕜 (w j) (w j)).toLinearMap)
        = ∑ j, TensorProduct.map ρ (InnerProductSpace.rankOne 𝕜 (w j) (w j)).toLinearMap := by
      simp only [← TensorProduct.mapBilinear_apply, map_sum]
    rw [hmap]
    ext x
    simp [LinearMap.sum_apply, map_sum]
  rw [hcomp, map_sum]
  simp only [partialTraceRightLM_apply, partialTraceRight_conj_map_rankOne_eq_sum_krausOp]

/-- **Completeness relation for the environment model** (Nielsen–Chuang Eq. (8.14)). When the joint
map `W` is an isometry (`W† ∘ₗ W = 1`) and the environment state `ω` is a unit vector, the operation
elements `Eₖ = krausOp b (W ∘ₗ tmulRightVec ω)` satisfy `∑ₖ Eₖ† Eₖ = 1`, so the environment-model
map `ρ ↦ partialTraceRight b (W (ρ ⊗ |ω⟩⟨ω|) W†)` is trace preserving. The dilation
`V = W ∘ₗ tmulRightVec ω` is an isometry (a composition of the isometries `W` and `tmulRightVec ω`),
whence `sum_adjoint_krausOp_comp_krausOp`. -/
theorem sum_adjoint_krausOp_tmulRightVec_comp_krausOp
    (b : OrthonormalBasis ι 𝕜 Fdisc) (W : (Hin ⊗[𝕜] Anc) →ₗ[𝕜] Eout ⊗[𝕜] Fdisc)
    {ω : Anc} (hW : adjoint W ∘ₗ W = LinearMap.id) (hω : ‖ω‖ = 1) :
    ∑ k, adjoint (krausOp b (W ∘ₗ tmulRightVec ω) k) ∘ₗ krausOp b (W ∘ₗ tmulRightVec ω) k
      = LinearMap.id := by
  refine sum_adjoint_krausOp_comp_krausOp b _ ?_
  have h : adjoint (W ∘ₗ tmulRightVec ω) ∘ₗ (W ∘ₗ tmulRightVec ω)
      = adjoint (tmulRightVec ω) ∘ₗ (adjoint W ∘ₗ W) ∘ₗ tmulRightVec ω := by
    rw [adjoint_comp]; simp only [comp_assoc]
  rw [h, hW, id_comp, adjoint_tmulRightVec_comp_self hω]

end EnvironmentModel

end LinearMap
