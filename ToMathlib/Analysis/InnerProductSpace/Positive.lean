/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Algebra.Algebra.StrictPositivity
public import ToMathlib.Analysis.InnerProductSpace.Spectrum
public import ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Positive operators: additional API

This file collects additional facts about positive operators on (finite-dimensional) Hilbert
spaces beyond `Mathlib.Analysis.InnerProductSpace.Positive`:

* A spectral characterisation of positivity for symmetric operators
  (`LinearMap.IsSymmetric.isPositive_iff_eigenvalues_nonneg`), the squared-eigenvalue formula
  `LinearMap.IsPositive.eigenvalues_sq`, and the operator-norm-equals-top-eigenvalue formulas
  `LinearMap.IsSymmetric.norm_eq_iSup_eigenvalues_abs` /
  `LinearMap.IsPositive.norm_eq_eigenvalues_zero`.
* Topological closedness of the set of positive continuous endomorphisms
  (`ContinuousLinearMap.isClosed_setOf_isPositive`).
* Uniqueness-of-square-root style eigenvector lemmas for positive operators
  (`ContinuousLinearMap.IsPositive.apply_eq_zero_of_apply_apply_eq_zero`,
  `ContinuousLinearMap.IsPositive.apply_eq_of_isPositive_sq_apply_eq`).
* Invariance of positivity, non-negativity, and strict positivity under conjugation by a linear
  isometry equivalence, and consequences of strict positivity for the operator kernel and its
  eigenvalues, together with the `HasSupportLE` support-inclusion relation used to state
  preconditions for the quantum relative entropy.
-/

@[expose] public section

open InnerProductSpace RCLike LinearMap ContinuousLinearMap

open scoped InnerProduct ComplexConjugate ComplexOrder

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

namespace LinearMap

/-- Reverse of `IsPositive.nonneg_eigenvalues`: a symmetric operator with all-nonnegative
eigenvalues is positive. -/
theorem IsSymmetric.isPositive_of_eigenvalues_nonneg [FiniteDimensional 𝕜 E]
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    (h : ∀ i, 0 ≤ hT.eigenvalues hn i) : T.IsPositive := by
  refine ⟨hT, fun x ↦ ?_⟩
  rw [hT.spectral_sum_apply hn, sum_inner, map_sum]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  rw [smul_smul, inner_smul_left, (starRingEnd 𝕜).map_mul, RCLike.conj_ofReal, mul_assoc,
    RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
  exact mul_nonneg (h i) (by positivity)

/-- **Spectral characterisation of positive operators**: a symmetric operator on a
finite-dimensional inner product space is positive iff its eigenvalues are all nonnegative. -/
theorem IsSymmetric.isPositive_iff_eigenvalues_nonneg [FiniteDimensional 𝕜 E]
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank 𝕜 E = n) :
    T.IsPositive ↔ ∀ i, 0 ≤ hT.eigenvalues hn i :=
  ⟨fun hP ↦ hP.nonneg_eigenvalues hn, hT.isPositive_of_eigenvalues_nonneg hn⟩

/-- For positive `T`, the eigenvalues of `T * T` are pointwise the squares of the eigenvalues of
`T`. The eigenbasis of `T` is also an eigenbasis of `T * T` with squared eigenvalues; for positive
`T` both eigenvalue sequences are antitone (nonneg + sorted nonincreasingly), so multiset
equality upgrades to pointwise equality. -/
theorem IsPositive.eigenvalues_sq [FiniteDimensional 𝕜 E]
    {T : E →ₗ[𝕜] E} (hT : T.IsPositive) {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    (h2_sym : (T * T).IsSymmetric) :
    h2_sym.eigenvalues hn = hT.isSymmetric.eigenvalues hn ^ 2 := by
  symm
  apply antitone_eq_of_multiset_map_eq (g := h2_sym.eigenvalues hn)
  · intro i j hij
    exact pow_le_pow_left₀ (hT.nonneg_eigenvalues hn j)
      (hT.isSymmetric.eigenvalues_antitone hn hij) 2
  · exact h2_sym.eigenvalues_antitone hn
  · exact IsSymmetric.eigenvalues_multiset_map_eq_of_eigenbasis h2_sym hn
      (hT.isSymmetric.eigenvectorBasis hn).toBasis fun i ↦ by
        simp only [OrthonormalBasis.coe_toBasis, Pi.pow_apply]
        rw [mul_apply_eq_comp, hT.isSymmetric.apply_eigenvectorBasis hn i,
            LinearMap.map_smul, hT.isSymmetric.apply_eigenvectorBasis hn i, smul_smul]
        push_cast
        ring_nf

/-- The norm of a symmetric operator applied to its `i`-th eigenvector equals the absolute
value of the `i`-th eigenvalue. Direct corollary of `apply_eigenvectorBasis`. -/
theorem IsSymmetric.norm_apply_eigenvectorBasis [FiniteDimensional 𝕜 E]
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : ‖T (hT.eigenvectorBasis hn i)‖ = |hT.eigenvalues hn i| := by
  rw [hT.apply_eigenvectorBasis hn, norm_smul, RCLike.norm_ofReal,
    (hT.eigenvectorBasis hn).orthonormal.1, mul_one]

/-- **Spectral identity for `‖T v‖²`**: for symmetric `T` on a finite-dimensional inner
product space, `‖T v‖² = ∑ i, eigenvalues_i² · ‖⟨eigenvectorBasis i, v⟩‖²`. The key
quantitative fact behind `norm_eq_iSup_eigenvalues_abs` and any spectral perturbation
argument; stated as a named identity for reuse. -/
theorem IsSymmetric.norm_apply_sq_eq [FiniteDimensional 𝕜 E]
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank 𝕜 E = n) (v : E) :
    ‖T v‖ ^ 2 = ∑ i, hT.eigenvalues hn i ^ 2 * ‖⟪hT.eigenvectorBasis hn i, v⟫_𝕜‖ ^ 2 := by
  rw [hT.spectral_sum_apply hn v]
  simp_rw [smul_smul]
  rw [← @inner_self_eq_norm_sq 𝕜,
    (hT.eigenvectorBasis hn).orthonormal.inner_sum
      (fun i => (hT.eigenvalues hn i : 𝕜) * ⟪hT.eigenvectorBasis hn i, v⟫_𝕜)
      (fun i => (hT.eigenvalues hn i : 𝕜) * ⟪hT.eigenvectorBasis hn i, v⟫_𝕜) Finset.univ,
    map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re, norm_mul, RCLike.norm_ofReal,
    mul_pow, sq_abs]

/-- **Operator norm of a symmetric operator on a finite-dimensional inner product space
equals the maximum absolute eigenvalue.** This is the spectral-radius-equals-norm fact
specialized to the finite-dimensional self-adjoint case. -/
theorem IsSymmetric.norm_eq_iSup_eigenvalues_abs [FiniteDimensional 𝕜 E] [Nontrivial E]
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    ‖T.toContinuousLinearMap‖ = ⨆ i : Fin (Module.finrank 𝕜 E), |hT.eigenvalues rfl i| := by
  have : NeZero (Module.finrank 𝕜 E) := ⟨Module.finrank_pos.ne'⟩
  set b := hT.eigenvectorBasis (rfl : Module.finrank 𝕜 E = Module.finrank 𝕜 E)
  set f : Fin (Module.finrank 𝕜 E) → ℝ := fun i ↦ |hT.eigenvalues rfl i|
  have hbdd : BddAbove (Set.range f) := Set.Finite.bddAbove (Set.finite_range _)
  have h_le_iSup : ∀ i, f i ≤ ⨆ j, f j := fun i ↦ le_ciSup hbdd i
  have h_iSup_nonneg : 0 ≤ ⨆ j, f j :=
    (abs_nonneg _).trans (h_le_iSup ⟨0, Module.finrank_pos⟩)
  refine le_antisymm ?_ ?_
  · -- Upper bound: ‖T v‖² ≤ (⨆ |λᵢ|)² · ‖v‖² via the spectral identity for ‖T v‖².
    refine T.toContinuousLinearMap.opNorm_le_bound h_iSup_nonneg fun v ↦ ?_
    simp only [LinearMap.coe_toContinuousLinearMap']
    have hnorm_sq : ‖T v‖ ^ 2 ≤ ((⨆ j, f j) * ‖v‖) ^ 2 := by
      rw [hT.norm_apply_sq_eq rfl v, mul_pow]
      have h_sq : ∀ i, hT.eigenvalues rfl i ^ 2 ≤ (⨆ j, f j) ^ 2 := fun i ↦ by
        rw [← sq_abs (hT.eigenvalues rfl i)]
        exact pow_le_pow_left₀ (abs_nonneg _) (h_le_iSup i) 2
      calc ∑ i, hT.eigenvalues rfl i ^ 2 * ‖⟪b i, v⟫_𝕜‖ ^ 2
          ≤ ∑ i, (⨆ j, f j) ^ 2 * ‖⟪b i, v⟫_𝕜‖ ^ 2 := Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_right (h_sq i) (sq_nonneg _)
        _ = (⨆ j, f j) ^ 2 * ‖v‖ ^ 2 := by rw [← Finset.mul_sum, b.sum_sq_norm_inner_right]
    exact (abs_le_of_sq_le_sq' hnorm_sq (mul_nonneg h_iSup_nonneg (norm_nonneg v))).2
  · -- Lower bound: ‖T (b i)‖ = |λᵢ| ≤ ‖T‖_op; take iSup.
    refine ciSup_le fun i ↦ ?_
    have := T.toContinuousLinearMap.le_opNorm (b i)
    simp only [LinearMap.coe_toContinuousLinearMap'] at this
    rw [hT.norm_apply_eigenvectorBasis rfl i, b.orthonormal.1, mul_one] at this
    exact this

/-- For a positive symmetric operator on a finite-dimensional inner product space (with
nontrivial domain so the eigenvalue list is nonempty), the operator norm equals the
largest eigenvalue (at index `0`, since eigenvalues are sorted descending). Corollary
of `IsSymmetric.norm_eq_iSup_eigenvalues_abs`: for positive operators all eigenvalues are
non-negative, so `|λᵢ| = λᵢ` and the iSup is attained at the antitone-sorted top. -/
theorem IsPositive.norm_eq_eigenvalues_zero [FiniteDimensional 𝕜 E] [Nontrivial E]
    {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    ‖T.toContinuousLinearMap‖ =
      hT.isSymmetric.eigenvalues rfl ⟨0, Module.finrank_pos⟩ := by
  have : NeZero (Module.finrank 𝕜 E) := ⟨Module.finrank_pos.ne'⟩
  rw [hT.isSymmetric.norm_eq_iSup_eigenvalues_abs]
  simp_rw [abs_of_nonneg (hT.nonneg_eigenvalues rfl _)]
  exact le_antisymm
    (ciSup_le fun i ↦ hT.isSymmetric.eigenvalues_antitone rfl (Fin.zero_le _))
    (le_ciSup (Set.Finite.bddAbove (Set.finite_range _)) _)

end LinearMap

namespace ContinuousLinearMap

theorem IsPositive.reApplyInnerSelf_nonneg {T : E →L[𝕜] E} (hT : T.IsPositive) (x : E) :
    0 ≤ T.reApplyInnerSelf x := hT.2 x

/-- The set of positive continuous endomorphisms is closed in the operator-norm topology:
its defining conditions are self-adjointness (closed by isometry of `adjoint`) and pointwise
non-negativity of `reApplyInnerSelf` (closed by `fun_prop` continuity of the map). -/
theorem isClosed_setOf_isPositive [CompleteSpace E] :
    IsClosed {T : E →L[𝕜] E | T.IsPositive} := by
  simp_rw [isPositive_def', Set.ofPred_and, Set.ofPred_forall, reApplyInnerSelf_apply]
  refine IsClosed.inter ?_ (isClosed_iInter fun x ↦ ?_)
  · exact isClosed_eq ContinuousLinearMap.adjoint.isometry.continuous continuous_id
  · exact isClosed_le continuous_const (by fun_prop)

/-- For a positive operator `B` (which is in particular self-adjoint), `B (B x) = 0 → B x = 0`.
Equivalent to `ker (B ∘L B) = ker B`, which for self-adjoint `B` follows from
`ker_adjoint_comp_self` since `B† ∘L B = B ∘L B`. -/
theorem IsPositive.apply_eq_zero_of_apply_apply_eq_zero [CompleteSpace E] {B : E →L[𝕜] E}
    (hB : B.IsPositive) {x : E} (hBBx : B (B x) = 0) : B x = 0 := by
  have hmem : x ∈ (B† ∘L B).ker := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      hB.isSelfAdjoint.adjoint_eq]
    exact hBBx
  rwa [B.ker_adjoint_comp_self, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hmem

/-- **Uniqueness of positive square root, eigenvector form**: for two positive operators
`A, B` with `A ∘L A = B ∘L B`, if `A x = c • x` for nonneg real `c`, then `B x = c • x`.
The proof uses `v := B x - c • x`: a calculation shows `B v = -c • v`, so
`re ⟨B v, v⟩ = -c ‖v‖²`. Combined with `re ⟨B v, v⟩ ≥ 0` (positivity of `B`) and `c ≥ 0`,
this forces `c · ‖v‖² = 0`, giving `c = 0` or `v = 0`; both cases yield `B x = c • x`. -/
theorem IsPositive.apply_eq_of_isPositive_sq_apply_eq [CompleteSpace E] {A B : E →L[𝕜] E}
    (hB : B.IsPositive) (hAB : A ∘L A = B ∘L B)
    {c : ℝ} (hc : 0 ≤ c) {x : E} (hAx : A x = (c : 𝕜) • x) : B x = (c : 𝕜) • x := by
  set v := B x - (c : 𝕜) • x with hv_def
  have hBsq_x : B (B x) = ((c : 𝕜) * c) • x := by
    have h1 : (A ∘L A) x = ((c : 𝕜) * c) • x := by
      rw [ContinuousLinearMap.comp_apply, hAx, ContinuousLinearMap.map_smul, hAx, smul_smul]
    rwa [hAB] at h1
  have hBv : B v = -((c : 𝕜)) • v := by
    rw [hv_def, ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul, hBsq_x]
    module
  have h_re : RCLike.re ⟪B v, v⟫_𝕜 = -c * ‖v‖ ^ 2 := by
    rw [hBv, inner_smul_left, ← inner_self_eq_norm_sq (𝕜 := 𝕜)]
    simp [map_neg, RCLike.conj_ofReal, neg_mul]
  have h_nn : 0 ≤ RCLike.re ⟪B v, v⟫_𝕜 := hB.2 v
  have hzero : c * ‖v‖ ^ 2 = 0 := by
    have h1 : 0 ≤ -c * ‖v‖ ^ 2 := h_re ▸ h_nn
    have h2 : 0 ≤ c * ‖v‖ ^ 2 := mul_nonneg hc (sq_nonneg _)
    linarith
  rcases mul_eq_zero.mp hzero with hc0 | hv0
  · subst hc0
    rw [hB.apply_eq_zero_of_apply_apply_eq_zero (by simpa using hBsq_x),
      RCLike.ofReal_zero, zero_smul]
  · have hv : v = 0 := norm_eq_zero.mp (pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hv0)
    exact sub_eq_zero.mp hv

/-- Positivity of an operator is preserved under conjugation by a linear isometry equivalence.
CLM-level corollary of the more general LM-level
`LinearMap.isPositive_linearIsometryEquiv_conj_iff`; routes through
`isPositive_toLinearMap_iff` + `conjStarAlgEquiv_apply`. -/
@[simp]
theorem _root_.LinearIsometryEquiv.conjStarAlgEquiv_isPositive_iff
    [CompleteSpace E] [CompleteSpace F] (e : E ≃ₗᵢ[𝕜] F) {T : E →L[𝕜] E} :
    (e.conjStarAlgEquiv T).IsPositive ↔ T.IsPositive := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply, ← isPositive_toLinearMap_iff,
      ← isPositive_toLinearMap_iff T]
  have heq : ((e ∘L T ∘L (e.symm : F →L[𝕜] E) : F →L[𝕜] F) : F →ₗ[𝕜] F) =
      e.toLinearMap ∘ₗ (T : E →ₗ[𝕜] E) ∘ₗ e.symm.toLinearMap := by
    ext x; simp
  rw [heq]
  exact LinearMap.isPositive_linearIsometryEquiv_conj_iff (T := T.toLinearMap) e

/-- CLM-nonneg sibling of `LinearIsometryEquiv.conjStarAlgEquiv_isPositive_iff`: the
order `0 ≤ T` is preserved by conjugation by a linear isometry equivalence. Bridges
the `IsPositive` form through `nonneg_iff_isPositive`. -/
@[simp]
theorem _root_.LinearIsometryEquiv.conjStarAlgEquiv_nonneg_iff
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F] (e : E ≃ₗᵢ[𝕜] F) {T : E →L[𝕜] E} :
    0 ≤ e.conjStarAlgEquiv T ↔ 0 ≤ T := by
  rw [nonneg_iff_isPositive, nonneg_iff_isPositive,
    LinearIsometryEquiv.conjStarAlgEquiv_isPositive_iff]

/-- Strict positivity is preserved under conjugation by a linear isometry equivalence. The
strict-positivity sibling of `conjStarAlgEquiv_isPositive_iff` / `conjStarAlgEquiv_nonneg_iff`. -/
@[simp]
theorem _root_.LinearIsometryEquiv.conjStarAlgEquiv_isStrictlyPositive_iff
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F] (e : E ≃ₗᵢ[𝕜] F) {T : E →L[𝕜] E} :
    IsStrictlyPositive (e.conjStarAlgEquiv T) ↔ IsStrictlyPositive T := by
  rw [IsStrictlyPositive, IsStrictlyPositive, nonneg_iff_isPositive, nonneg_iff_isPositive,
    e.conjStarAlgEquiv_isPositive_iff]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ h.map e.conjStarAlgEquiv⟩
  have := h.map e.conjStarAlgEquiv.symm
  rwa [StarAlgEquiv.symm_apply_apply] at this

/-- A strictly positive operator is a unit, hence bijective, hence injective: its kernel is
trivial. -/
theorem _root_.IsStrictlyPositive.ker_eq_bot [CompleteSpace E] {T : E →L[𝕜] E}
    (h : IsStrictlyPositive T) : LinearMap.ker (T : E →ₗ[𝕜] E) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp h.2).injective

/-- The **support condition** `supp ρ ⊆ supp σ` for the relative entropy `D(ρ ‖ σ)`, in the
operator-kernel form `ker σ ≤ ker ρ` (for positive operators `supp = (ker)ᗮ`, so the support
inclusion reverses on kernels). The precondition under which the `cfc`-based `D` is meaningful.
(Placed here, below both `QuantumRelativeEntropy` and `ReducedState`, so the
`HasSupportLE.of_partialTraceRight` marginal-preservation lemma can live beside its
`of_partialTraceRight_eq` siblings.) -/
def HasSupportLE (ρ σ : E →L[𝕜] E) : Prop :=
  LinearMap.ker (σ : E →ₗ[𝕜] E) ≤ LinearMap.ker (ρ : E →ₗ[𝕜] E)

theorem hasSupportLE_iff {ρ σ : E →L[𝕜] E} :
    HasSupportLE ρ σ ↔ LinearMap.ker (σ : E →ₗ[𝕜] E) ≤ LinearMap.ker (ρ : E →ₗ[𝕜] E) :=
  Iff.rfl

/-- A faithful (strictly positive) `σ` dominates the support of every `ρ`: its kernel is trivial,
so the support condition holds unconditionally. -/
theorem HasSupportLE.of_isStrictlyPositive [CompleteSpace E] {ρ σ : E →L[𝕜] E}
    (h : IsStrictlyPositive σ) : HasSupportLE ρ σ := by
  rw [hasSupportLE_iff, IsStrictlyPositive.ker_eq_bot h]
  exact bot_le

/-- **The eigenvalues of a strictly positive operator are strictly positive.** Strengthens
`LinearMap.IsPositive.nonneg_eigenvalues` (which gives only `0 ≤`) using invertibility: `0` cannot
be an eigenvalue of a unit, so the nonnegative eigenvalues are in fact positive. Stated against an
explicit symmetry witness `hsym` so it matches a consumer's chosen `eigenvalues` term (the value is
independent of the proof by proof irrelevance). -/
theorem _root_.IsStrictlyPositive.eigenvalues_pos [FiniteDimensional 𝕜 E] {T : E →L[𝕜] E}
    (hT : IsStrictlyPositive T) (hsym : (T : E →ₗ[𝕜] E).IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) : 0 < hsym.eigenvalues hn i := by
  refine lt_of_le_of_ne (((isPositive_toLinearMap_iff T).mpr
    (nonneg_iff_isPositive.mp hT.nonneg)).nonneg_eigenvalues hn i) (Ne.symm fun h0 ↦ ?_)
  refine spectrum.not_isUnit_of_zero_mem 𝕜 ?_
    (hT.isUnit.map (ContinuousLinearMap.toLinearMapRingHom (R₁ := 𝕜) (M₁ := E)))
  simpa [h0] using (hsym.hasEigenvalue_eigenvalues hn i).mem_spectrum

/-- **Vanishing propagates along the support condition.** If `ρ.HasSupportLE σ` (`ker σ ≤ ker ρ`)
and `σ x = 0`, then `ρ x = 0`: the vector `x` lies in `ker σ`, hence in `ker ρ`. The pointwise form
of the support condition, the reusable consequence behind support-condition arguments. -/
theorem HasSupportLE.apply_eq_zero {ρ σ : E →L[𝕜] E} (h : ρ.HasSupportLE σ) {x : E}
    (hx : σ x = 0) : ρ x = 0 :=
  LinearMap.mem_ker.mp (h (LinearMap.mem_ker.mpr hx))

section Complex

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']

/-- **Positivity is preserved under nonnegative real scaling.** For a positive operator `T` and a
nonnegative real scalar `c` (`0 ≤ c`), the real scalar multiple `c • T` is positive. The
real-scalar companion of `IsPositive.smul_of_nonneg` (which takes a `ℂ`-scalar): `c • T` is
rewritten to `(↑c : ℂ) • T` via `Complex.coe_smul`, with `0 ≤ (↑c : ℂ)`. -/
theorem IsPositive.smul_real_of_nonneg {T : E' →L[ℂ] E'} (hT : T.IsPositive) {c : ℝ}
    (hc : 0 ≤ c) : (c • T).IsPositive := by
  rw [← Complex.coe_smul c T]
  exact hT.smul_of_nonneg (RCLike.nonneg_iff_exists_ofReal.mpr ⟨c, hc, rfl⟩)

end Complex

end ContinuousLinearMap
