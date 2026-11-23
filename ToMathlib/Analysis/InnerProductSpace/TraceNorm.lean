/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Dual
public import ToMathlib.Analysis.InnerProductSpace.HSPairing
public import ToMathlib.Analysis.InnerProductSpace.Polar
public import ToMathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
# Trace norm of a linear operator on a finite-dimensional inner product space

For a linear map `T : E →ₗ[𝕜] F` between finite-dimensional inner product spaces over `𝕜`
(where `𝕜` is `ℝ` or `ℂ`), the **trace norm** (also known as the nuclear norm or
Schatten 1-norm) is the sum of the singular values of `T`:

`‖T‖₁ := ∑ i, T.singularValues i`

Equivalently, it is the real part of the trace of `|T| := √(T† ∘ T)`:

`‖T‖₁ = re (trace |T|)`

## Main definitions

- `LinearMap.traceNorm` — the trace norm as an `ℝ`-valued function.
- `ContinuousLinearMap.traceNorm` — the CLM-coerced sibling.

## Main results

- `LinearMap.traceNorm_zero`, `LinearMap.traceNorm_nonneg`, `LinearMap.traceNorm_eq_zero_iff`:
  basic API.
- `LinearMap.traceNorm_eq_re_trace_absoluteValue` and
  `LinearMap.ofReal_traceNorm_eq_trace_absoluteValue`: connect `traceNorm` to the trace of
  the absolute value of the operator.
- `LinearMap.traceNorm_rankOne`: `traceNorm (rankOne 𝕜 x y) = ‖x‖ * ‖y‖`.
- `LinearMap.opNorm_le_traceNorm` (and CLM sibling): `‖T‖_op ≤ ‖T‖₁`.
- `LinearMap.norm_hsPairing_le_opNorm_mul_traceNorm` (and CLM sibling): the Hölder-type
  bound `‖hsPairing T W‖ ≤ ‖W‖_op * ‖T‖₁`.
- `ContinuousLinearMap.hsPairing_polarPart_eq_ofReal_traceNorm` and
  `ContinuousLinearMap.re_hsPairing_polarPart_eq_traceNorm`: achievability of the
  variational characterization at `W = polarPart T`.
- `ContinuousLinearMap.re_hsPairing_le_traceNorm_of_opNorm_le_one`: combined with
  achievability, the variational characterization `‖T‖₁ = sup_{‖W‖_op ≤ 1} re (hsPairing T W)`.
- `ContinuousLinearMap.traceNorm_add_le`: the triangle inequality
  `‖T + S‖₁ ≤ ‖T‖₁ + ‖S‖₁`, derived from the two halves of the variational
  characterization; `traceNorm_sub_le` and `traceNorm_sum_le` are the subtraction
  and finite-sum forms.
- `ContinuousLinearMap.traceNorm_comp_le` and `traceNorm_comp_le'`:
  sub-multiplicativity in both directions, `‖S ∘ T‖₁ ≤ ‖S‖_op · ‖T‖₁` and
  `‖S ∘ T‖₁ ≤ ‖S‖₁ · ‖T‖_op`. Derived from the move-adjoint identities in
  `HSPairing.lean` + the Hölder bound + `polarPart_opNorm_le_one`.

## Implementation notes

The definition uses a finite sum over `Fin (finrank 𝕜 E)`, mirroring
`HilbertSchmidt.norm_sq_eq_sum_sq_singularValues`. Even though singular values past
`finrank (range T)` are zero, the Fin-sum form composes cleanly with the rest of the
singular-value API.

The trace norm requires both `[FiniteDimensional 𝕜 E]` and `[FiniteDimensional 𝕜 F]` because
`LinearMap.singularValues` does. `[CompleteSpace _]` is **not** required at the definition
level — it appears only on lemmas that explicitly invoke `adjoint`.

The definition is RCLike-generic. The trace norm itself doesn't depend on the continuous
functional calculus chain (which currently requires complex C*-algebra structure for the
self-adjoint CFC instance); any future Schatten-p generalization that does would need to
match its surroundings accordingly.
-/

@[expose] public section

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The **trace norm** (Schatten 1-norm) of a linear map between finite-dimensional inner
product spaces: the sum of the singular values of `T`. -/
noncomputable def traceNorm (T : E →ₗ[𝕜] F) : ℝ :=
  ∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i.val

theorem traceNorm_eq (T : E →ₗ[𝕜] F) :
    T.traceNorm = ∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i.val := rfl

@[simp]
theorem traceNorm_zero : traceNorm (0 : E →ₗ[𝕜] F) = 0 := by
  simp [traceNorm_eq]

theorem traceNorm_nonneg (T : E →ₗ[𝕜] F) : 0 ≤ T.traceNorm := by
  exact Finset.sum_nonneg fun i _ ↦ T.singularValues_nonneg i.val

@[simp]
theorem traceNorm_neg (T : E →ₗ[𝕜] F) : (-T).traceNorm = T.traceNorm := by
  simp [traceNorm_eq, singularValues_neg]

/-- The trace norm scales by the norm of the scalar:
`(c • T).traceNorm = ‖c‖ * T.traceNorm`. Direct consequence of `singularValues_smul` +
`Finset.mul_sum`. -/
@[simp]
theorem traceNorm_smul (c : 𝕜) (T : E →ₗ[𝕜] F) :
    (c • T).traceNorm = ‖c‖ * T.traceNorm := by
  simp only [traceNorm_eq, singularValues_smul, Finset.mul_sum]

/-- **Trace norm is invariant under left-composition with a linear isometry.** Direct
consequence of `singularValues_linearIsometry_comp`: both sums range over the same
`Fin (finrank E)` (since the source is preserved under left-composition). -/
theorem traceNorm_linearIsometry_comp
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    (U : F →ₗᵢ[𝕜] G) (T : E →ₗ[𝕜] F) :
    (U.toLinearMap ∘ₗ T).traceNorm = T.traceNorm := by
  simp [traceNorm_eq, singularValues_linearIsometry_comp]

/-- **Trace norm is invariant under right-composition with a linear isometry equivalence.**
Routes through `singularValues_comp_linearIsometryEquiv` + `Fintype.sum_equiv` to bridge the
`Fin (finrank E')` vs `Fin (finrank E)` summation domains via `Fin.castOrderIso`. -/
theorem traceNorm_comp_linearIsometryEquiv
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
    (V : E' ≃ₗᵢ[𝕜] E) (T : E →ₗ[𝕜] F) :
    (T ∘ₗ V.toLinearEquiv.toLinearMap).traceNorm = T.traceNorm := by
  rw [traceNorm_eq, traceNorm_eq, singularValues_comp_linearIsometryEquiv]
  exact Fintype.sum_equiv (Fin.castOrderIso V.toLinearEquiv.finrank_eq).toEquiv _ _ (fun _ ↦ rfl)

/-- The trace norm is invariant under adjoint: `T†.traceNorm = T.traceNorm`. Direct consequence
of `singularValues_adjoint`: the singular-value sequences agree pointwise, and both sums
restrict (via `sum_singularValues_eq_sum_range_finrank_range`) to a sum over
`Finset.range (finrank T.range)` (= `Finset.range (finrank T†.range)` by `finrank_range_adjoint`),
bridging the `Fin (finrank F)` vs `Fin (finrank E)` summation domains. -/
theorem traceNorm_adjoint (T : E →ₗ[𝕜] F) : T.adjoint.traceNorm = T.traceNorm := by
  rw [traceNorm_eq, traceNorm_eq, singularValues_adjoint,
      sum_singularValues_eq_sum_range_finrank_range T (Submodule.finrank_le _),
      sum_singularValues_eq_sum_range_finrank_range T
        ((finrank_range_adjoint T).symm.le.trans (Submodule.finrank_le _))]

theorem traceNorm_eq_zero_iff {T : E →ₗ[𝕜] F} : T.traceNorm = 0 ↔ T = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ traceNorm_zero⟩
  rw [traceNorm_eq, Finset.sum_eq_zero_iff_of_nonneg
    fun i _ ↦ T.singularValues_nonneg i.val] at h
  refine T.singularValues_eq_zero_iff.mp ?_
  ext i
  rcases lt_or_ge i (Module.finrank 𝕜 E) with hi | hi
  · simpa using h ⟨i, hi⟩ (Finset.mem_univ _)
  · exact T.singularValues_of_finrank_le hi

/-- For a positive endomorphism `S : E →ₗ[𝕜] E`, the trace norm equals the real part of the
trace. Routes through `IsPositive.singularValues_eq_eigenvalues` (singular values = eigenvalues
for positive operators) + `IsSymmetric.re_trace_eq_sum_eigenvalues`. -/
theorem traceNorm_eq_re_trace_of_isPositive
    {S : E →ₗ[𝕜] E} (hS : S.IsPositive) :
    S.traceNorm = RCLike.re (LinearMap.trace 𝕜 E S) := by
  rw [traceNorm_eq, hS.isSymmetric.re_trace_eq_sum_eigenvalues rfl]
  exact Finset.sum_congr rfl fun i _ ↦ hS.singularValues_eq_eigenvalues rfl i

/-- For a symmetric endomorphism `T : E →ₗ[𝕜] E`, the trace norm equals the sum of absolute
values of the eigenvalues. Companion to `IsPositive.singularValues_eq_eigenvalues`: extends
beyond the positive case at the cost of dropping pointwise sort alignment (the absolute values
of symmetric eigenvalues form the same multiset as the singular values, but not in the same
order). -/
theorem IsSymmetric.traceNorm_eq_sum_abs_eigenvalues
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank 𝕜 E = n) :
    T.traceNorm = ∑ i : Fin n, |hT.eigenvalues hn i| := by
  subst hn
  have h2 : (T.adjoint ∘ₗ T).IsSymmetric := T.isSymmetric_adjoint_comp_self
  -- Eigenbasis recognition: T*T has eigenbasis (hT.eigenvectorBasis) with squared eigenvalues.
  have hms : Multiset.map (h2.eigenvalues rfl) Finset.univ.val =
      Multiset.map (fun i => (hT.eigenvalues rfl i) ^ 2) Finset.univ.val :=
    (h2.eigenvalues_multiset_map_eq_of_eigenbasis rfl (hT.eigenvectorBasis rfl).toBasis
      fun i => by simpa using hT.adjoint_comp_self_apply_eigenvectorBasis rfl i).symm
  -- Convert both sides to `∑ √(...)`; reduce to multiset equality.
  rw [LinearMap.traceNorm_eq]
  simp_rw [fun i : Fin (Module.finrank 𝕜 E) => T.singularValues_of_lt rfl i.is_lt,
    Fin.eta,
    fun i : Fin (Module.finrank 𝕜 E) => (Real.sqrt_sq_eq_abs (hT.eigenvalues rfl i)).symm]
  -- Both sides are ∑ √(f i) where the f's are multiset-equal.
  change (Multiset.map (Real.sqrt ∘ h2.eigenvalues rfl) Finset.univ.val).sum =
         (Multiset.map (Real.sqrt ∘ fun i => (hT.eigenvalues rfl i) ^ 2) Finset.univ.val).sum
  rw [← Multiset.map_map Real.sqrt (h2.eigenvalues rfl),
    ← Multiset.map_map Real.sqrt (fun i => (hT.eigenvalues rfl i) ^ 2), hms]

/-- For a symmetric `T : E →ₗ[𝕜] E`, the trace norm equals the sum of `𝕜`-norms of the
characteristic polynomial's roots. Composes `IsSymmetric.traceNorm_eq_sum_abs_eigenvalues`
with `IsSymmetric.roots_charpoly_eq_eigenvalues` via `‖(x : 𝕜)‖ = |x|` for real `x`. -/
theorem IsSymmetric.traceNorm_eq_sum_norm_charpoly_roots
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    T.traceNorm = (T.charpoly.roots.map (‖·‖)).sum := by
  rw [hT.traceNorm_eq_sum_abs_eigenvalues rfl, Finset.sum_eq_multiset_sum,
    hT.roots_charpoly_eq_eigenvalues rfl, Multiset.map_map]
  refine congr_arg Multiset.sum (Multiset.map_congr rfl fun _ _ => ?_)
  exact (RCLike.norm_ofReal _).symm

/-- The trace of `|T|` equals the ℝ-cast sum of singular values of `T`. The substantive
identity behind `LinearMap.ofReal_traceNorm_eq_trace_absoluteValue`. -/
theorem trace_absoluteValue_eq_ofReal_sum_singularValues (T : E →L[𝕜] F) :
    LinearMap.trace 𝕜 E T.toLinearMap.absoluteValue =
      ((∑ i : Fin (Module.finrank 𝕜 E), T.toLinearMap.singularValues i.val : ℝ) : 𝕜) := by
  rw [← ContinuousLinearMap.toLinearMap_absoluteValue, T.absoluteValue_eq_sum,
    ContinuousLinearMap.toLinearMap_sum, map_sum, RCLike.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.map_smul_of_tower,
      InnerProductSpace.trace_rankOne,
    inner_self_eq_norm_sq_to_K, (T.toLinearMap.svdRight).orthonormal.1, RCLike.ofReal_one,
    one_pow, smul_eq_mul, mul_one]

/-- The `(traceNorm T : 𝕜) = trace |T|` form is `simp`-eligible. -/
@[simp]
theorem ofReal_traceNorm_eq_trace_absoluteValue (T : E →L[𝕜] F) :
    (T.toLinearMap.traceNorm : 𝕜) =
      LinearMap.trace 𝕜 E T.toLinearMap.absoluteValue :=
  (trace_absoluteValue_eq_ofReal_sum_singularValues T).symm

/-- The trace norm equals the real part of the trace of the absolute value `|T| = √(T† ∘ T)`. -/
theorem traceNorm_eq_re_trace_absoluteValue (T : E →L[𝕜] F) :
    T.toLinearMap.traceNorm =
      RCLike.re (LinearMap.trace 𝕜 E T.toLinearMap.absoluteValue) := by
  rw [trace_absoluteValue_eq_ofReal_sum_singularValues, RCLike.ofReal_re, traceNorm_eq]

/-- The trace norm of `|T|` equals the trace norm of `T` itself. Since `|T|` is positive,
its trace norm equals `re tr |T|`, which by `traceNorm_eq_re_trace_absoluteValue` is
`T.traceNorm`. -/
theorem traceNorm_absoluteValue (T : E →L[𝕜] F) :
    T.toLinearMap.absoluteValue.traceNorm = T.toLinearMap.traceNorm := by
  rw [← ContinuousLinearMap.toLinearMap_absoluteValue,
    traceNorm_eq_re_trace_of_isPositive T.absoluteValue_isPositive.toLinearMap,
    ContinuousLinearMap.toLinearMap_absoluteValue, ← traceNorm_eq_re_trace_absoluteValue]

/-- The largest singular value is bounded above by the trace norm. The trace norm is a
sum of nonneg singular values, so any one of them — in particular the largest — is
dominated. For trivial domain `E`, both sides are `0`. -/
theorem singularValues_zero_le_traceNorm (T : E →ₗ[𝕜] F) :
    T.singularValues 0 ≤ T.traceNorm := by
  rcases Nat.eq_zero_or_pos (Module.finrank 𝕜 E) with hE | hE
  · have : Subsingleton E := Module.finrank_zero_iff.mp hE
    have hT : T = 0 := Subsingleton.elim T 0
    simp [hT]
  · rw [traceNorm_eq]
    exact Finset.single_le_sum (f := fun i : Fin (Module.finrank 𝕜 E) ↦ T.singularValues i.val)
      (fun i _ ↦ T.singularValues_nonneg i.val) (Finset.mem_univ (⟨0, hE⟩ : Fin _))

/-- **Operator norm bound by trace norm.** `‖T‖_op ≤ ‖T‖₁` — the largest singular value
(operator norm via `opNorm_eq_singularValues_zero`) is dominated by the sum of all of them
(the trace norm). -/
theorem opNorm_le_traceNorm (T : E →ₗ[𝕜] F) :
    ‖T.toContinuousLinearMap‖ ≤ T.traceNorm := by
  rw [T.opNorm_eq_singularValues_zero]
  exact T.singularValues_zero_le_traceNorm

/-- The HS pairing of `T` against `W` expands over the SVD of `T`:
`hsPairing T W = ∑ᵢ σᵢ * ⟨W (svdRight i), svdLeft i⟩`. The trace
`trace_E (W† ∘ T)` is evaluated on the SVD-right orthonormal basis of `E`, using
`apply_svdRight : T (svdRight i) = σᵢ • svdLeft i` and `adjoint_inner_right` to move
`W†` to the other inner-product slot. -/
theorem hsPairing_eq_sum_singularValues_mul_inner (T W : E →ₗ[𝕜] F) :
    T.hsPairing W = ∑ i : Fin (Module.finrank 𝕜 E),
      (T.singularValues i.val : 𝕜) * inner 𝕜 (W (T.svdRight i)) (T.svdLeft i) := by
  rw [LinearMap.hsPairing_eq, LinearMap.trace_eq_sum_inner _ T.svdRight]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.apply_svdRight, map_smul, inner_smul_right,
    LinearMap.adjoint_inner_right]

/-- **Hölder-type bound for the HS pairing vs the trace norm.**
`‖hsPairing T W‖ ≤ ‖W.toContinuousLinearMap‖ * traceNorm T`. Proof:
expand `hsPairing T W` via the SVD of `T`, apply Cauchy–Schwarz on each summand,
bound `‖W (svdRight i)‖ ≤ ‖W‖_op` (since `‖svdRight i‖ = 1`), and bound
`‖svdLeft i‖ ≤ 1` (via `norm_svdLeft_le_one`). This is the upper-bound direction of the
variational characterization `traceNorm T = ⨆_{‖W‖_op ≤ 1} re (hsPairing T W)`. -/
theorem norm_hsPairing_le_opNorm_mul_traceNorm (T W : E →ₗ[𝕜] F) :
    ‖T.hsPairing W‖ ≤ ‖W.toContinuousLinearMap‖ * T.traceNorm := by
  rw [T.hsPairing_eq_sum_singularValues_mul_inner W, LinearMap.traceNorm_eq, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (T.singularValues_nonneg _), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (T.singularValues_nonneg _)
  calc ‖inner 𝕜 (W (T.svdRight i)) (T.svdLeft i)‖
      ≤ ‖W (T.svdRight i)‖ * ‖T.svdLeft i‖ := norm_inner_le_norm _ _
    _ ≤ ‖W.toContinuousLinearMap‖ * 1 := by
        gcongr
        · simpa [T.svdRight.orthonormal.1 i]
            using W.toContinuousLinearMap.le_opNorm (T.svdRight i)
        · exact T.norm_svdLeft_le_one i
    _ = ‖W.toContinuousLinearMap‖ := mul_one _

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The trace norm of a continuous linear map, defined as the trace norm of its underlying
linear map. -/
noncomputable def traceNorm (T : E →L[𝕜] F) : ℝ :=
  T.toLinearMap.traceNorm

@[simp]
theorem traceNorm_toLinearMap (T : E →L[𝕜] F) : T.toLinearMap.traceNorm = T.traceNorm := rfl

@[simp]
theorem traceNorm_zero : traceNorm (0 : E →L[𝕜] F) = 0 := LinearMap.traceNorm_zero

theorem traceNorm_nonneg (T : E →L[𝕜] F) : 0 ≤ T.traceNorm := T.toLinearMap.traceNorm_nonneg

@[simp]
theorem traceNorm_neg (T : E →L[𝕜] F) : (-T).traceNorm = T.traceNorm := by
  rw [← traceNorm_toLinearMap, ← traceNorm_toLinearMap T, toLinearMap_neg,
      LinearMap.traceNorm_neg]

/-- CLM sibling of `LinearMap.traceNorm_smul`:
`(c • T).traceNorm = ‖c‖ * T.traceNorm`. -/
@[simp]
theorem traceNorm_smul (c : 𝕜) (T : E →L[𝕜] F) :
    (c • T).traceNorm = ‖c‖ * T.traceNorm := by
  rw [← traceNorm_toLinearMap, ← traceNorm_toLinearMap T, toLinearMap_smul,
      LinearMap.traceNorm_smul]

/-- CLM sibling of `LinearMap.traceNorm_adjoint` (requires `[CompleteSpace E]` and
`[CompleteSpace F]` to invoke the CLM adjoint): `T†.traceNorm = T.traceNorm`. -/
theorem traceNorm_adjoint [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F) :
    T.adjoint.traceNorm = T.traceNorm := by
  rw [← traceNorm_toLinearMap, ← traceNorm_toLinearMap T,
      ← ContinuousLinearMap.adjoint_toLinearMap, LinearMap.traceNorm_adjoint]

/-- CLM sibling of `LinearMap.traceNorm_linearIsometry_comp`: trace norm is invariant under
left-composition with a linear isometry. -/
theorem traceNorm_linearIsometry_comp
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    (U : F →ₗᵢ[𝕜] G) (T : E →L[𝕜] F) :
    (U.toContinuousLinearMap ∘L T).traceNorm = T.traceNorm :=
  LinearMap.traceNorm_linearIsometry_comp U T.toLinearMap

/-- CLM sibling of `LinearMap.traceNorm_comp_linearIsometryEquiv`: trace norm is invariant
under right-composition with a linear isometry equivalence. -/
theorem traceNorm_comp_linearIsometryEquiv
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
    (V : E' ≃ₗᵢ[𝕜] E) (T : E →L[𝕜] F) :
    (T ∘L (V : E' →L[𝕜] E)).traceNorm = T.traceNorm :=
  LinearMap.traceNorm_comp_linearIsometryEquiv V T.toLinearMap

/-- CLM sibling of `LinearMap.traceNorm_absoluteValue`: `|T|.traceNorm = T.traceNorm`.
The trace norm of the absolute value coincides with the trace norm of the original
operator, since `|T|` is positive and shares the singular values of `T`. -/
theorem traceNorm_absoluteValue (T : E →L[𝕜] F) :
    T.absoluteValue.traceNorm = T.traceNorm := by
  rw [← traceNorm_toLinearMap, ← traceNorm_toLinearMap T,
    ContinuousLinearMap.toLinearMap_absoluteValue, LinearMap.traceNorm_absoluteValue]

theorem traceNorm_eq_zero_iff {T : E →L[𝕜] F} : T.traceNorm = 0 ↔ T = 0 := by
  rw [← traceNorm_toLinearMap, LinearMap.traceNorm_eq_zero_iff,
    ← ContinuousLinearMap.toLinearMap_zero, coe_inj]

/-- CLM sibling of `LinearMap.traceNorm_eq_re_trace_of_isPositive`: for a positive endomorphism
`S : E →L[𝕜] E`, the trace norm equals the real part of the trace. -/
theorem traceNorm_eq_re_trace_of_isPositive
    {S : E →L[𝕜] E} (hS : S.IsPositive) :
    S.traceNorm = RCLike.re (LinearMap.trace 𝕜 E (S : E →ₗ[𝕜] E)) :=
  LinearMap.traceNorm_eq_re_trace_of_isPositive hS

/-- **Operator norm bound by trace norm**, CLM sibling of `LinearMap.opNorm_le_traceNorm`.
`‖T‖_op ≤ ‖T‖₁`. -/
theorem opNorm_le_traceNorm (T : E →L[𝕜] F) : ‖T‖ ≤ T.traceNorm := by
  simpa using T.toLinearMap.opNorm_le_traceNorm

/-- **Hölder-type bound for the HS pairing vs the trace norm**, CLM sibling of
`LinearMap.norm_hsPairing_le_opNorm_mul_traceNorm`. -/
theorem norm_hsPairing_le_opNorm_mul_traceNorm (T W : E →L[𝕜] F) :
    ‖T.hsPairing W‖ ≤ ‖W‖ * T.traceNorm := by
  simpa using T.toLinearMap.norm_hsPairing_le_opNorm_mul_traceNorm W.toLinearMap

section VariationalCharacterization

/-- **Achievability of the variational characterization.** The HS pairing of `T` with its
polar part equals the (`𝕜`-cast of the) trace norm:
`hsPairing T (polarPart T) = (traceNorm T : 𝕜)`. Evaluating the trace on the
`svdRight` ONB and applying `polarPart_apply_svdRight : polarPart T (svdRight i) = svdLeft i`
makes each summand reduce to `σᵢ` (the `i`-th singular value). -/
theorem hsPairing_polarPart_eq_ofReal_traceNorm (T : E →L[𝕜] F) :
    T.toLinearMap.hsPairing T.toLinearMap.polarPart = (T.toLinearMap.traceNorm : 𝕜) := by
  rw [← ContinuousLinearMap.toLinearMap_polarPart,
    T.toLinearMap.hsPairing_eq_sum_singularValues_mul_inner T.polarPart.toLinearMap,
    LinearMap.traceNorm_eq, RCLike.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [ContinuousLinearMap.coe_coe, T.polarPart_apply_svdRight i,
    T.toLinearMap.inner_svdLeft_svdLeft_full, true_and]
  by_cases hi : T.toLinearMap.singularValues i.val = 0
  · simp [hi]
  · rw [ite_eq_left hi, mul_one]

/-- Real-part form of achievability:
`re (hsPairing T (polarPart T)) = traceNorm T`. The HS pairing of `T` with its polar
part is `𝕜`-cast real (equal to `(traceNorm T : 𝕜)`), so taking the real part recovers
the trace norm. -/
theorem re_hsPairing_polarPart_eq_traceNorm (T : E →L[𝕜] F) :
    RCLike.re (T.hsPairing T.polarPart) = T.traceNorm := by
  rw [← hsPairing_toLinearMap, ContinuousLinearMap.toLinearMap_polarPart,
    T.hsPairing_polarPart_eq_ofReal_traceNorm, RCLike.ofReal_re, traceNorm_toLinearMap]

/-- **Variational characterization of the trace norm, upper bound on the supremum side.**
For any contraction `W` (`‖W‖ ≤ 1`), `re (hsPairing T W) ≤ traceNorm T`. Follows from the
Hölder bound `norm_hsPairing_le_opNorm_mul_traceNorm` + `RCLike.re ≤ ‖·‖`. Combined with the
achievability lemma `re_hsPairing_polarPart_eq_traceNorm`, this gives the variational
characterization without committing to a particular `iSup` formulation in `ℝ`. -/
theorem re_hsPairing_le_traceNorm_of_opNorm_le_one (T : E →L[𝕜] F) {W : E →L[𝕜] F}
    (hW : ‖W‖ ≤ 1) :
    RCLike.re (T.hsPairing W) ≤ T.traceNorm :=
  calc RCLike.re (T.hsPairing W)
      ≤ ‖T.hsPairing W‖ := RCLike.re_le_norm _
    _ ≤ ‖W‖ * T.traceNorm := T.norm_hsPairing_le_opNorm_mul_traceNorm W
    _ ≤ 1 * T.traceNorm := by gcongr; exact T.traceNorm_nonneg
    _ = T.traceNorm := one_mul _

/-- **Norm-sibling of `re_hsPairing_le_traceNorm_of_opNorm_le_one`**: for any contraction
`W` (`‖W‖ ≤ 1`), `‖hsPairing T W‖ ≤ traceNorm T`. Direct from
`norm_hsPairing_le_opNorm_mul_traceNorm` + `1 * x = x`. -/
theorem norm_hsPairing_le_traceNorm_of_opNorm_le_one (T : E →L[𝕜] F) {W : E →L[𝕜] F}
    (hW : ‖W‖ ≤ 1) :
    ‖T.hsPairing W‖ ≤ T.traceNorm :=
  calc ‖T.hsPairing W‖
      ≤ ‖W‖ * T.traceNorm := T.norm_hsPairing_le_opNorm_mul_traceNorm W
    _ ≤ 1 * T.traceNorm := by gcongr; exact T.traceNorm_nonneg
    _ = T.traceNorm := one_mul _

/-- **Triangle inequality for the trace norm.** Derived directly from the two halves of the
variational characterization: achievability at `polarPart (T + S)` gives
`traceNorm (T + S) = re (hsPairing (T+S) polarPart(T+S))`; bilinearity of `re ∘ hsPairing`
in the first slot splits this into two pieces; the Hölder corollary then bounds each piece
by the corresponding trace norm (using `polarPart_opNorm_le_one`). -/
theorem traceNorm_add_le (T S : E →L[𝕜] F) :
    (T + S).traceNorm ≤ T.traceNorm + S.traceNorm := by
  have := FiniteDimensional.completeSpace 𝕜 E
  have := FiniteDimensional.completeSpace 𝕜 F
  have hPP : ‖(T + S).polarPart‖ ≤ 1 := (T + S).polarPart_opNorm_le_one
  rw [← (T + S).re_hsPairing_polarPart_eq_traceNorm,
    ContinuousLinearMap.hsPairing_add_left, map_add]
  exact add_le_add (T.re_hsPairing_le_traceNorm_of_opNorm_le_one hPP)
    (S.re_hsPairing_le_traceNorm_of_opNorm_le_one hPP)

/-- **Triangle inequality for the trace norm, subtraction form**:
`‖T − S‖₁ ≤ ‖T‖₁ + ‖S‖₁`. The direct companion to `traceNorm_add_le`, obtained by rewriting
`T − S = T + (−S)` and using `traceNorm_neg`. -/
theorem traceNorm_sub_le (T S : E →L[𝕜] F) :
    (T - S).traceNorm ≤ T.traceNorm + S.traceNorm := by
  rw [sub_eq_add_neg, ← traceNorm_neg S]
  exact traceNorm_add_le T (-S)

/-- **Triangle inequality for the trace norm over a finite sum**:
`‖∑ᵢ Tᵢ‖₁ ≤ ∑ᵢ ‖Tᵢ‖₁`. The `Finset` generalization of `traceNorm_add_le`, proved by
induction on the index set (base case `traceNorm_zero`, inductive step `traceNorm_add_le`). -/
theorem traceNorm_sum_le {ι : Type*} (s : Finset ι) (T : ι → E →L[𝕜] F) :
    (∑ i ∈ s, T i).traceNorm ≤ ∑ i ∈ s, (T i).traceNorm := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine (traceNorm_add_le _ _).trans ?_
    gcongr

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- **Sub-multiplicativity of the trace norm, left form**:
`traceNorm (S ∘L T) ≤ ‖S‖_op * traceNorm T`. Derived from achievability +
`hsPairing_comp_left` (moving `S` to the second slot as `S.adjoint`) + the Hölder bound on
the resulting pairing, then bounding `‖S.adjoint ∘L polarPart(S∘T)‖ ≤ ‖S‖ * 1` via
`opNorm_comp_le` + `polarPart_opNorm_le_one` + `adjoint.norm_map`. -/
theorem traceNorm_comp_le (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    (S ∘L T).traceNorm ≤ ‖S‖ * T.traceNorm := by
  have := FiniteDimensional.completeSpace 𝕜 E
  have := FiniteDimensional.completeSpace 𝕜 F
  have := FiniteDimensional.completeSpace 𝕜 G
  rw [← (S ∘L T).re_hsPairing_polarPart_eq_traceNorm,
    ContinuousLinearMap.hsPairing_comp_left]
  calc RCLike.re (T.hsPairing (S.adjoint ∘L (S ∘L T).polarPart))
      ≤ ‖T.hsPairing (S.adjoint ∘L (S ∘L T).polarPart)‖ := RCLike.re_le_norm _
    _ ≤ ‖S.adjoint ∘L (S ∘L T).polarPart‖ * T.traceNorm :=
        T.norm_hsPairing_le_opNorm_mul_traceNorm _
    _ ≤ ‖S.adjoint‖ * ‖(S ∘L T).polarPart‖ * T.traceNorm := by
        gcongr
        · exact T.traceNorm_nonneg
        · exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖S.adjoint‖ * 1 * T.traceNorm := by
        gcongr
        · exact T.traceNorm_nonneg
        · exact (S ∘L T).polarPart_opNorm_le_one
    _ = ‖S‖ * T.traceNorm := by
        rw [mul_one, ContinuousLinearMap.adjoint.norm_map]

/-- **Sub-multiplicativity of the trace norm, right form**:
`traceNorm (S ∘L T) ≤ traceNorm S * ‖T‖_op`. Dual of `traceNorm_comp_le`: uses
`hsPairing_comp_right` to move `T` to the second slot as `T.adjoint`. -/
theorem traceNorm_comp_le' (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    (S ∘L T).traceNorm ≤ S.traceNorm * ‖T‖ := by
  have := FiniteDimensional.completeSpace 𝕜 E
  have := FiniteDimensional.completeSpace 𝕜 F
  have := FiniteDimensional.completeSpace 𝕜 G
  rw [← (S ∘L T).re_hsPairing_polarPart_eq_traceNorm,
    ContinuousLinearMap.hsPairing_comp_right]
  calc RCLike.re (S.hsPairing ((S ∘L T).polarPart ∘L T.adjoint))
      ≤ ‖S.hsPairing ((S ∘L T).polarPart ∘L T.adjoint)‖ := RCLike.re_le_norm _
    _ ≤ ‖(S ∘L T).polarPart ∘L T.adjoint‖ * S.traceNorm :=
        S.norm_hsPairing_le_opNorm_mul_traceNorm _
    _ ≤ ‖(S ∘L T).polarPart‖ * ‖T.adjoint‖ * S.traceNorm := by
        gcongr
        · exact S.traceNorm_nonneg
        · exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T.adjoint‖ * S.traceNorm := by
        gcongr
        · exact S.traceNorm_nonneg
        · exact (S ∘L T).polarPart_opNorm_le_one
    _ = S.traceNorm * ‖T‖ := by
        rw [one_mul, ContinuousLinearMap.adjoint.norm_map, mul_comm]

/-- **Trace-norm right-invariance under a linear isometry equivalence**: composing on
the right with a LIE preserves the trace norm. Combines `traceNorm_comp_le'` (forward
≤ via op-norm ≤ 1) with the reverse application on `W.symm` (backward ≤ via the same
bound applied to `T ∘L W.toCLM` and `W.symm`). -/
theorem traceNorm_compL_linearIsometryEquiv [CompleteSpace E] [CompleteSpace F]
    [CompleteSpace G] (T : E →L[𝕜] F) (W : G ≃ₗᵢ[𝕜] E) :
    (T ∘L (W : G →L[𝕜] E)).traceNorm = T.traceNorm := by
  refine le_antisymm ?_ ?_
  · calc (T ∘L (W : G →L[𝕜] E)).traceNorm
        ≤ T.traceNorm * ‖(W : G →L[𝕜] E)‖ := traceNorm_comp_le' _ _
      _ ≤ T.traceNorm * 1 := by
          gcongr
          · exact T.traceNorm_nonneg
          · exact W.toLinearIsometry.norm_toContinuousLinearMap_le
      _ = T.traceNorm := mul_one _
  · calc T.traceNorm
        = ((T ∘L (W : G →L[𝕜] E)) ∘L (W.symm : E →L[𝕜] G)).traceNorm := by
          congr 1; ext x; simp
      _ ≤ (T ∘L (W : G →L[𝕜] E)).traceNorm * ‖(W.symm : E →L[𝕜] G)‖ :=
          traceNorm_comp_le' _ _
      _ ≤ (T ∘L (W : G →L[𝕜] E)).traceNorm * 1 := by
          gcongr
          · exact (T ∘L _).traceNorm_nonneg
          · exact W.symm.toLinearIsometry.norm_toContinuousLinearMap_le
      _ = (T ∘L (W : G →L[𝕜] E)).traceNorm := mul_one _

/-- **Bundled variational characterization of the trace norm.** The trace norm equals the
supremum over contractions `W` (`‖W‖_op ≤ 1`) of `re (hsPairing T W)`. Combines achievability
(`re_hsPairing_polarPart_eq_traceNorm`, witnessed at `W = polarPart T`) with the Hölder upper
bound (`re_hsPairing_le_traceNorm_of_opNorm_le_one`, established for every contraction). The
pre-bundled halves remain available for proofs that prefer a specific witness over the
`iSup` form. -/
theorem traceNorm_eq_iSup (T : E →L[𝕜] F) :
    T.traceNorm =
      ⨆ W : {W : E →L[𝕜] F // ‖W‖ ≤ 1}, RCLike.re (T.hsPairing W.val) := by
  have := FiniteDimensional.completeSpace 𝕜 E
  have := FiniteDimensional.completeSpace 𝕜 F
  have : Nonempty {W : E →L[𝕜] F // ‖W‖ ≤ 1} := ⟨0, by simp⟩
  have hbdd : BddAbove (Set.range
      (fun W : {W : E →L[𝕜] F // ‖W‖ ≤ 1} ↦ RCLike.re (T.hsPairing W.val))) :=
    ⟨T.traceNorm, by rintro _ ⟨W, rfl⟩; exact T.re_hsPairing_le_traceNorm_of_opNorm_le_one W.2⟩
  refine le_antisymm ?_ ?_
  · rw [← T.re_hsPairing_polarPart_eq_traceNorm]
    exact le_ciSup hbdd ⟨T.polarPart, T.polarPart_opNorm_le_one⟩
  · exact ciSup_le fun W ↦ T.re_hsPairing_le_traceNorm_of_opNorm_le_one W.2

end VariationalCharacterization

/-- The trace norm of a rank-one operator. Smoke test for the API: the only non-zero
singular value of `rankOne x y` is `‖x‖ * ‖y‖`, so the trace norm equals this product. -/
theorem traceNorm_rankOne (x : F) (y : E) :
    ((InnerProductSpace.rankOne 𝕜 x) y).traceNorm = ‖x‖ * ‖y‖ := by
  rw [← traceNorm_toLinearMap, LinearMap.traceNorm_eq]
  rcases Nat.eq_zero_or_pos (Module.finrank 𝕜 E) with hE | hE
  · -- E is trivial: y = 0, so RHS = 0; LHS is empty sum = 0.
    have : Subsingleton E := Module.finrank_zero_iff.mp hE
    simp [Subsingleton.eq_zero y]
  · -- Singular values past index 0 are zero (rank ≤ 1).
    rw [Finset.sum_eq_single (⟨0, hE⟩ : Fin _)
      (fun i _ hi ↦
        (LinearMap.singularValues_eq_zero_iff_le_finrank_range _).mpr
          ((InnerProductSpace.finrank_range_rankOne_le_one x y).trans
            (Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_iff.mpr hi))))
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    -- The 0-th singular value equals the operator norm `‖x‖ * ‖y‖`.
    rw [← LinearMap.opNorm_eq_singularValues_zero]
    exact InnerProductSpace.norm_rankOne x y

/-- **Trace norm is invariant under conjugation by a linear isometry equivalence.**
Routes through `singularValues_conjStarAlgEquiv` + `Fintype.sum_equiv` to bridge the
`Fin (finrank E)` vs `Fin (finrank F)` summation domains via `Fin.castOrderIso`. -/
theorem traceNorm_conjStarAlgEquiv [CompleteSpace E] [CompleteSpace F]
    (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    (e.conjStarAlgEquiv T).traceNorm = T.traceNorm := by
  rw [← traceNorm_toLinearMap, ← traceNorm_toLinearMap T,
      LinearMap.traceNorm_eq, LinearMap.traceNorm_eq,
      singularValues_conjStarAlgEquiv e T]
  exact Fintype.sum_equiv (Fin.castOrderIso e.toLinearEquiv.finrank_eq.symm).toEquiv
    _ _ (fun _ ↦ rfl)

end ContinuousLinearMap

/-!
### Jordan–Hahn decomposition and the trace-norm split

For a self-adjoint operator `A` on a finite-dimensional complex inner product space, the
continuous functional calculus splits `A = A⁺ - A⁻` into nonnegative parts of orthogonal
support, the operator absolute value coincides with `A⁺ + A⁻`, and the trace norm splits as
`‖A‖₁ = re tr A⁺ + re tr A⁻` (Nielsen & Chuang, Exercise 9.7).

These are stated over `ℂ`: the operator CFC `posPart`/`negPart` and `CFC.sqrt` require
`CStarAlgebra (E →L[ℂ] E)`, which Mathlib provides only for `ℂ` (real/`RCLike` operator-CFC is
blocked upstream by `spectrum.nonempty`).
-/

section JordanDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

omit [FiniteDimensional ℂ E] in
/-- **Operator Jordan–Hahn decomposition** (N&C Ex 9.7): a self-adjoint operator splits as
`A = A⁺ - A⁻` into nonnegative parts of orthogonal support (`A⁺ * A⁻ = 0`). -/
theorem IsSelfAdjoint.jordanDecomposition (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    A = A⁺ - A⁻ ∧ (0 ≤ A⁺) ∧ (0 ≤ A⁻) ∧ A⁺ * A⁻ = 0 :=
  ⟨(CFC.posPart_sub_negPart A hA).symm, CFC.posPart_nonneg A, CFC.negPart_nonneg A,
    CFC.posPart_mul_negPart A⟩

/-- For self-adjoint `A`, the SVD-based operator absolute value `|A|`
(`ContinuousLinearMap.absoluteValue`) equals the CFC sum `A⁺ + A⁻`. Both are the unique
nonnegative square root of `A† ∘ A`, via `CFC.sqrt_unique`. -/
theorem IsSelfAdjoint.absoluteValue_eq_posPart_add_negPart (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) : A.absoluteValue = A⁺ + A⁻ := by
  rw [CFC.posPart_add_negPart A]
  refine (CFC.sqrt_unique ?_ A.absoluteValue_nonneg).symm
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.absoluteValue_sq,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]

/-- **Trace-norm Jordan split** (N&C Ex 9.7): for self-adjoint `A`,
`‖A‖₁ = re tr A⁺ + re tr A⁻`. -/
theorem IsSelfAdjoint.traceNorm_eq_re_trace_posPart_add (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    A.traceNorm = RCLike.re (LinearMap.trace ℂ E (A⁺ : E →L[ℂ] E))
      + RCLike.re (LinearMap.trace ℂ E (A⁻ : E →L[ℂ] E)) := by
  rw [← ContinuousLinearMap.traceNorm_absoluteValue,
    IsSelfAdjoint.absoluteValue_eq_posPart_add_negPart A hA]
  have hpos : (0 : E →L[ℂ] E) ≤ A⁺ + A⁻ :=
    add_nonneg (CFC.posPart_nonneg A) (CFC.negPart_nonneg A)
  rw [ContinuousLinearMap.traceNorm_eq_re_trace_of_isPositive
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hpos),
    ContinuousLinearMap.toLinearMap_add, map_add, map_add]

end JordanDecomposition

section Contractive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- **Trace-preserving positive maps contract the trace norm** — the operator-theoretic heart of
Nielsen & Chuang Theorem 9.2. If a `ℂ`-linear superoperator `Φ` between the operator algebras of
two finite-dimensional complex inner product spaces preserves positivity
(`A.IsPositive → (Φ A).IsPositive`) and preserves the trace (`tr (Φ A) = tr A`), then it does not
increase the trace norm of any self-adjoint operator: `‖Φ A‖₁ ≤ ‖A‖₁`.

The proof splits `A` into its nonnegative Jordan parts `A = A⁺ - A⁻`
(`IsSelfAdjoint.jordanDecomposition`); the triangle inequality gives
`‖Φ A‖₁ = ‖Φ A⁺ - Φ A⁻‖₁ ≤ ‖Φ A⁺‖₁ + ‖Φ A⁻‖₁`. Each of `Φ A⁺`, `Φ A⁻` is positive, so its trace
norm equals its trace (`traceNorm_eq_re_trace_of_isPositive`); trace preservation rewrites these to
`re tr A⁺ + re tr A⁻`, which is exactly `‖A‖₁` for self-adjoint `A`
(`IsSelfAdjoint.traceNorm_eq_re_trace_posPart_add`). Only positivity and trace preservation of `Φ`
are used — complete positivity is not needed. -/
theorem ContinuousLinearMap.traceNorm_map_le_of_isPositive_of_trace_eq
    (Φ : (E →L[ℂ] E) →ₗ[ℂ] (F →L[ℂ] F))
    (hpos : ∀ A : E →L[ℂ] E, A.IsPositive → (Φ A).IsPositive)
    (htrace : ∀ A : E →L[ℂ] E, LinearMap.trace ℂ F ↑(Φ A) = LinearMap.trace ℂ E ↑A)
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) :
    (Φ A).traceNorm ≤ A.traceNorm := by
  obtain ⟨hAeq, hApos, hAneg, -⟩ := IsSelfAdjoint.jordanDecomposition A hA
  have hΦp : (Φ A⁺).IsPositive := hpos _ (ContinuousLinearMap.nonneg_iff_isPositive.mp hApos)
  have hΦn : (Φ A⁻).IsPositive := hpos _ (ContinuousLinearMap.nonneg_iff_isPositive.mp hAneg)
  have hΦA : Φ A = Φ A⁺ - Φ A⁻ := by rw [← map_sub, ← hAeq]
  calc (Φ A).traceNorm
      = (Φ A⁺ - Φ A⁻).traceNorm := by rw [hΦA]
    _ ≤ (Φ A⁺).traceNorm + (Φ A⁻).traceNorm := ContinuousLinearMap.traceNorm_sub_le _ _
    _ = RCLike.re (LinearMap.trace ℂ F ↑(Φ A⁺)) + RCLike.re (LinearMap.trace ℂ F ↑(Φ A⁻)) := by
        rw [ContinuousLinearMap.traceNorm_eq_re_trace_of_isPositive hΦp,
          ContinuousLinearMap.traceNorm_eq_re_trace_of_isPositive hΦn]
    _ = RCLike.re (LinearMap.trace ℂ E ↑A⁺) + RCLike.re (LinearMap.trace ℂ E ↑A⁻) := by
        rw [htrace A⁺, htrace A⁻]
    _ = A.traceNorm := (IsSelfAdjoint.traceNorm_eq_re_trace_posPart_add A hA).symm

end Contractive
