/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Density
public import ToMathlib.Analysis.InnerProductSpace.LinearMap
public import ToMathlib.Analysis.InnerProductSpace.Positive
public import ToMathlib.Analysis.InnerProductSpace.Trace
public import ToMathlib.Analysis.InnerProductSpace.TraceNorm
public import ToMathlib.Analysis.RCLike.Basic

/-!
# Positive operator-valued measures (POVMs)

A **POVM** on a finite-dimensional inner product space `E` over `𝕜` (`ℝ` or `ℂ`) with
finite outcome index `ι` is a family of positive operators `M.elements i : E →L[𝕜] E`
indexed by `i : ι`, satisfying `∑ i, M.elements i = 1`. POVMs generalize projective
measurements: each `M.elements i` is a "soft" positive operator with the closure-to-
identity replacing idempotence.

Per Nielsen–Chuang §2.2.6, POVMs encode the most general form of quantum measurement
consistent with the Born rule:
`Pr(outcome = i | state ρ) = tr(M.elements i ∘L ρ)`.

## Main definitions

- `POVM ι 𝕜 E`: a POVM on `E` over `𝕜` with outcome index `ι`.

## Main results

- `POVM.isPositive`, `POVM.sum_eq_one`: unpacking lemmas.
- `POVM.isSymmetric`: each `M.elements i` is symmetric (via positivity).
- `POVM.reApplyInnerSelf_nonneg`: each `M.elements i` satisfies
  `0 ≤ re ⟪M.elements i ψ, ψ⟫`.

## Constructors

- `POVM.ofOrthonormalBasis`: the rank-one POVM associated to an orthonormal basis, with
  `elements i := rankOne (b i) (b i)`. The canonical "projective measurement in basis `b`"
  and the building block for the Fuchs–Caves canonical POVM (Nielsen–Chuang §9.2.2).
- `POVM.toPMF_ofOrthonormalBasis`: `toPMF (ofOrthonormalBasis b) ρ i = re ⟪b i, ρ (b i)⟫`.

## Implementation notes

The structure is RCLike-generic (`[RCLike 𝕜]`), matching `IsDensityOp` and `IsPositive`
conventions. Type parameter order `(ι 𝕜 E)` matches `OrthonormalBasis`.

The minimal API surface is: structure definition + unpacking lemmas + the inner-product
positivity helper. Constructors (rank-one projective measurements, orthonormal-basis-
derived POVMs), measurement probabilities, and the Naimark dilation theorem are left
to the files that need them.

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information*
(10th anniv. ed.). Cambridge University Press. §2.2.6.
-/

@[expose] public section

/-- A **positive operator-valued measure (POVM)** on a finite-dim inner product space
`E` over `𝕜` with finite outcome index `ι`: a family of positive operators summing to
the identity. -/
@[ext]
structure POVM (ι : Type*) [Fintype ι] (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] where
  /-- The operator-valued measure: outcome `i` corresponds to `elements i`. -/
  elements : ι → E →L[𝕜] E
  /-- Each element is positive. -/
  isPositive : ∀ i, (elements i).IsPositive
  /-- The elements sum to the identity. -/
  sum_eq_one : ∑ i, elements i = 1

namespace POVM

variable {ι : Type*} [Fintype ι]
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Each element of a POVM is symmetric (immediate from positivity). -/
theorem isSymmetric (M : POVM ι 𝕜 E) (i : ι) :
    (M.elements i).IsSymmetric :=
  (M.isPositive i).isSymmetric

/-- Each element of a POVM has non-negative real-part inner product with any vector:
`0 ≤ re ⟪M.elements i ψ, ψ⟫`. -/
theorem reApplyInnerSelf_nonneg (M : POVM ι 𝕜 E) (i : ι) (ψ : E) :
    0 ≤ (M.elements i).reApplyInnerSelf ψ :=
  (M.isPositive i).reApplyInnerSelf_nonneg ψ

/-- The pointwise sum identity: applying all POVM elements to a fixed vector `ψ` and
summing recovers `ψ`. -/
@[simp]
theorem sum_apply_eq_self (M : POVM ι 𝕜 E) (ψ : E) :
    ∑ i, M.elements i ψ = ψ := by
  rw [← sum_apply, M.sum_eq_one, one_apply_eq_self]

/-- **Born rule**: the probability of measurement outcome `i` for state `ρ` under POVM
`M`, defined as `Re tr(M.elements i ∘L ρ)`. Real-valued (the imaginary parts of the
trace cancel for self-adjoint operands). -/
noncomputable def toPMF [FiniteDimensional 𝕜 E]
    (M : POVM ι 𝕜 E) (ρ : E →L[𝕜] E) (i : ι) : ℝ :=
  RCLike.re (LinearMap.trace 𝕜 E ((M.elements i ∘L ρ : E →L[𝕜] E) : E →ₗ[𝕜] E))

theorem toPMF_eq [FiniteDimensional 𝕜 E]
    (M : POVM ι 𝕜 E) (ρ : E →L[𝕜] E) (i : ι) :
    M.toPMF ρ i =
      RCLike.re (LinearMap.trace 𝕜 E ((M.elements i ∘L ρ : E →L[𝕜] E) : E →ₗ[𝕜] E)) :=
  rfl

variable [FiniteDimensional 𝕜 E]

/-- **Born probability on a pure state.** For a POVM `M` and a vector `ψ`, the Born-rule
probability of outcome `i` on the pure state `|ψ⟩⟨ψ|` (`InnerProductSpace.rankOne 𝕜 ψ ψ`) equals
`(M.elements i).reApplyInnerSelf ψ = re ⟪(M.elements i) ψ, ψ⟫`. -/
theorem toPMF_rankOne_self (M : POVM ι 𝕜 E) (ψ : E) (i : ι) :
    M.toPMF (InnerProductSpace.rankOne 𝕜 ψ ψ) i = (M.elements i).reApplyInnerSelf ψ := by
  rw [toPMF_eq, InnerProductSpace.comp_rankOne, InnerProductSpace.trace_rankOne,
    ContinuousLinearMap.reApplyInnerSelf_apply, ← inner_conj_symm (M.elements i ψ) ψ,
    RCLike.conj_re]

/-- **Non-negativity** of measurement probabilities: for a positive operator `ρ` (in
particular, a density operator), each outcome probability is non-negative. Proof: expand
`trace (M_i ρ)` in the spectral basis of `ρ`; each summand is `λ_j · re ⟪b_j, M_i b_j⟫`
with `λ_j ≥ 0` (positive operator's eigenvalue) and `re ⟪b_j, M_i b_j⟫ ≥ 0` (positivity
of `M_i`). -/
theorem toPMF_nonneg (M : POVM ι 𝕜 E) {ρ : E →L[𝕜] E}
    (hρ : ρ.IsPositive) (i : ι) :
    0 ≤ M.toPMF ρ i := by
  rw [toPMF_eq, ContinuousLinearMap.toLinearMap_comp,
    hρ.toLinearMap.isSymmetric.trace_comp_eq_sum_eigenvalues_inner rfl _, map_sum RCLike.re]
  refine Finset.sum_nonneg fun j _ ↦ ?_
  rw [RCLike.re_ofReal_mul]
  refine mul_nonneg (hρ.toLinearMap.nonneg_eigenvalues rfl j) ?_
  rw [← (M.isPositive i).toLinearMap.isSymmetric (_ : E) (_ : E)]
  exact (M.isPositive i).toLinearMap.re_inner_nonneg_left _

omit [FiniteDimensional 𝕜 E] in
/-- For a POVM `M` and any operator `T`, summing the traces of `(M.elements i) ∘L T`
over outcomes recovers the trace of `T`. Direct consequence of trace linearity and
`M.sum_eq_one`. -/
theorem sum_trace_elements_comp (M : POVM ι 𝕜 E) (T : E →L[𝕜] E) :
    ∑ i, LinearMap.trace 𝕜 E ((M.elements i ∘L T : E →L[𝕜] E) : E →ₗ[𝕜] E) =
      LinearMap.trace 𝕜 E T.toLinearMap := by
  rw [← map_sum (LinearMap.trace 𝕜 E) _ Finset.univ,
    ← ContinuousLinearMap.toLinearMap_sum,
    ← ContinuousLinearMap.finsetSum_comp _ _, M.sum_eq_one,
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_one,
    Module.End.one_eq_id, LinearMap.id_comp]

/-- **Sums-to-one**: for a density operator `ρ`, the outcome probabilities form a
probability distribution. Proof: linearity of trace + `M.sum_eq_one` + `tr ρ = 1`. -/
theorem sum_toPMF_eq_one (M : POVM ι 𝕜 E) {ρ : E →L[𝕜] E} (hρ : ρ.IsDensityOp) :
    ∑ i, M.toPMF ρ i = 1 := by
  simp_rw [toPMF_eq]
  rw [← map_sum RCLike.re, M.sum_trace_elements_comp, hρ.trace_eq_one, RCLike.one_re]

/-- **Born rule = real part of HS pairing**: for any operator `ρ` and POVM element
`M.elements i`, the Born-rule probability `M.toPMF ρ i` equals the real part of the
Hilbert-Schmidt pairing of `ρ` with `M.elements i`. Bridges the trace-distance variational
form (`traceNorm_eq_iSup` over the HS pairing) to the POVM probabilities. -/
theorem re_hsPairing_elements_eq_toPMF [CompleteSpace E] (M : POVM ι 𝕜 E)
    (ρ : E →L[𝕜] E) (i : ι) :
    RCLike.re (ρ.hsPairing (M.elements i)) = M.toPMF ρ i := by
  rw [ContinuousLinearMap.hsPairing_eq,
    ContinuousLinearMap.isSelfAdjoint_iff'.mp (M.isPositive i).isSelfAdjoint, ← toPMF_eq]

/-- The **signed Born-rule difference** in terms of the HS pairing: for any pair of
operators `ρ, σ`, the difference of Born-rule probabilities under a POVM `M` equals the
real part of the HS pairing of `ρ - σ` with the POVM element. Corollary of
`re_hsPairing_elements_eq_toPMF` via linearity of HS pairing in the first argument. -/
theorem re_hsPairing_elements_sub_eq_toPMF_sub [CompleteSpace E] (M : POVM ι 𝕜 E)
    (ρ σ : E →L[𝕜] E) (i : ι) :
    RCLike.re ((ρ - σ).hsPairing (M.elements i)) = M.toPMF ρ i - M.toPMF σ i := by
  rw [ContinuousLinearMap.hsPairing_sub_left, map_sub,
    M.re_hsPairing_elements_eq_toPMF, M.re_hsPairing_elements_eq_toPMF]

omit [FiniteDimensional 𝕜 E] in
/-- For a POVM `M` and a real-valued function `r : ι → ℝ` with `|r i| ≤ 1` for all `i`,
the operator norm of the signed combination `∑ i, (r i : 𝕜) • M.elements i` is bounded
by `1`. Used in the proof of trace-distance monotonicity under POVM measurement: the
signed combination is the witness operator in the variational form of `traceNorm`. -/
theorem opNorm_sum_real_smul_le_one [CompleteSpace E] (M : POVM ι 𝕜 E) (r : ι → ℝ)
    (hr : ∀ i, |r i| ≤ 1) :
    ‖∑ i, (r i : 𝕜) • M.elements i‖ ≤ 1 := by
  set W : E →L[𝕜] E := ∑ i, (r i : 𝕜) • M.elements i with hW_def
  have hW_symm : W.IsSymmetric := IsSelfAdjoint.isSymmetric <| hW_def ▸
    isSelfAdjoint_sum Finset.univ fun i _ ↦
      (RCLike.isSelfAdjoint_ofReal (r i)).smul (M.isPositive i).isSelfAdjoint
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hW_symm]
  refine ciSup_le fun x ↦ ?_
  by_cases hx : x = 0
  · simp [hx, ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf]
  rw [ContinuousLinearMap.rayleighQuotient, abs_div, abs_sq,
    div_le_iff₀ (by positivity), one_mul]
  -- Decompose `W.reApplyInnerSelf x = ∑ r_i (M.elements i).reApplyInnerSelf x`, then bound.
  calc |W.reApplyInnerSelf x|
      = |∑ i, r i * (M.elements i).reApplyInnerSelf x| := by
        rw [hW_def, ContinuousLinearMap.reApplyInnerSelf_sum]
        simp_rw [ContinuousLinearMap.reApplyInnerSelf_ofReal_smul]
    _ ≤ ∑ i, |r i * (M.elements i).reApplyInnerSelf x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |r i| * (M.elements i).reApplyInnerSelf x :=
        Finset.sum_congr rfl fun i _ ↦ by
          rw [abs_mul, abs_of_nonneg ((M.isPositive i).reApplyInnerSelf_nonneg _)]
    _ ≤ ∑ i, (M.elements i).reApplyInnerSelf x :=
        Finset.sum_le_sum fun i _ ↦
          mul_le_of_le_one_left ((M.isPositive i).reApplyInnerSelf_nonneg _) (hr i)
    _ = (1 : E →L[𝕜] E).reApplyInnerSelf x := by
        rw [← M.sum_eq_one, ContinuousLinearMap.reApplyInnerSelf_sum]
    _ = ‖x‖ ^ 2 := by
        rw [ContinuousLinearMap.reApplyInnerSelf_apply, one_apply_eq_self,
          inner_self_eq_norm_sq]

/-! ## The rank-one POVM associated to an orthonormal basis -/

omit [FiniteDimensional 𝕜 E] in
/-- The **rank-one POVM** built from an orthonormal basis `b`: outcome `i` corresponds to
the rank-one projector `rankOne 𝕜 (b i) (b i)`. The resolution of identity
(`OrthonormalBasis.sum_rankOne_eq_id`) supplies the `sum_eq_one` field; positivity comes
from `isPositive_rankOne_self`. This is the canonical "projective measurement in basis
`b`" and the building block for the Fuchs–Caves canonical POVM (Nielsen–Chuang §9.2.2). -/
noncomputable def ofOrthonormalBasis (b : OrthonormalBasis ι 𝕜 E) : POVM ι 𝕜 E where
  elements i := InnerProductSpace.rankOne 𝕜 (b i) (b i)
  isPositive _ := InnerProductSpace.isPositive_rankOne_self _
  sum_eq_one := b.sum_rankOne_eq_id

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem ofOrthonormalBasis_elements (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    (ofOrthonormalBasis b).elements i = InnerProductSpace.rankOne 𝕜 (b i) (b i) :=
  rfl

/-- The **Born-rule probability** of outcome `i` under the projective measurement
`ofOrthonormalBasis b` on state `ρ` equals `re ⟪b i, ρ (b i)⟫`: the (real-part) diagonal
matrix element of `ρ` in basis `b`. Proof: trace-cyclicity + `comp_rankOne` reduce the
trace of `rankOne (b i) (b i) ∘L ρ` to `trace (rankOne (ρ (b i)) (b i)) = ⟪b i, ρ (b i)⟫`. -/
theorem toPMF_ofOrthonormalBasis (b : OrthonormalBasis ι 𝕜 E) (ρ : E →L[𝕜] E) (i : ι) :
    (ofOrthonormalBasis b).toPMF ρ i = RCLike.re (inner 𝕜 (b i) (ρ (b i))) := by
  rw [toPMF_eq, ofOrthonormalBasis_elements, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.trace_comp_comm', ← ContinuousLinearMap.toLinearMap_comp,
    InnerProductSpace.comp_rankOne, InnerProductSpace.trace_rankOne]

/-- `toPMF M ρ i` is continuous in `ρ` for fixed `M : POVM ι 𝕜 E` and `i : ι`. -/
@[fun_prop]
theorem _root_.Continuous.toPMF {X : Type*} [TopologicalSpace X] (M : POVM ι 𝕜 E) (i : ι)
    {ρ : X → E →L[𝕜] E} (hρ : Continuous ρ) :
    Continuous (fun x ↦ M.toPMF (ρ x) i) :=
  RCLike.continuous_re.comp <| ContinuousLinearMap.continuous_trace.comp <|
    (ContinuousLinearMap.compL 𝕜 E E E (M.elements i)).continuous.comp hρ

open Filter Topology in
/-- Joint Tendsto-form of `Continuous.toPMF`: given convergence of the POVM elements
`(M x).elements i → (M₀).elements i` and `ρ x → ρ₀`, `(M x).toPMF (ρ x) i → M₀.toPMF ρ₀ i`.
Used by the saturation extension proof to pass an equality through the limit
when both the POVM sequence and the perturbation sequence vary together. -/
theorem _root_.Filter.Tendsto.toPMF {X : Type*} {l : Filter X}
    {M : X → POVM ι 𝕜 E} {M₀ : POVM ι 𝕜 E} {ρ : X → E →L[𝕜] E} {ρ₀ : E →L[𝕜] E} {i : ι}
    (hM : Tendsto (fun x ↦ (M x).elements i) l (𝓝 (M₀.elements i)))
    (hρ : Tendsto ρ l (𝓝 ρ₀)) :
    Tendsto (fun x ↦ (M x).toPMF (ρ x) i) l (𝓝 (M₀.toPMF ρ₀ i)) :=
  (RCLike.continuous_re.tendsto _).comp <|
    (ContinuousLinearMap.continuous_trace.tendsto _).comp <|
      ((ContinuousLinearMap.compL 𝕜 E E E).continuous₂.tendsto (M₀.elements i, ρ₀)).comp
        (hM.prodMk_nhds hρ)

end POVM

/-- The underlying-tuple view of POVMs: tuples `f : ι → E →L[𝕜] E` satisfying the positivity
and sum-to-one axioms. Defined as an intersection so closedness/compactness arguments don't
have to unfold the predicate form. Useful for topological arguments (closedness, compactness,
subsequence extraction) where the flat `POVM` structure is awkward. -/
def POVMSet (ι : Type*) [Fintype ι] (𝕜 : Type*) [RCLike 𝕜] (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] : Set (ι → E →L[𝕜] E) :=
  (⋂ i, {f | (f i).IsPositive}) ∩ {f | ∑ i, f i = 1}

namespace POVM

variable {ι : Type*} [Fintype ι]
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A POVM's elements are a tuple in `POVMSet`. -/
theorem elements_mem_POVMSet (M : POVM ι 𝕜 E) : M.elements ∈ POVMSet ι 𝕜 E :=
  ⟨Set.mem_iInter.mpr M.isPositive, M.sum_eq_one⟩

/-- Reconstruct a POVM from a tuple in `POVMSet`. -/
@[simps]
def ofMemPOVMSet {f : ι → E →L[𝕜] E} (hf : f ∈ POVMSet ι 𝕜 E) : POVM ι 𝕜 E where
  elements := f
  isPositive := Set.mem_iInter.mp hf.1
  sum_eq_one := hf.2

/-- `POVMSet ι 𝕜 E` is closed in the operator-norm topology. -/
theorem POVMSet_isClosed [CompleteSpace E] : IsClosed (POVMSet ι 𝕜 E) :=
  .inter
    (isClosed_iInter fun i ↦ ContinuousLinearMap.isClosed_setOf_isPositive.preimage
      (continuous_apply (A := fun _ : ι ↦ E →L[𝕜] E) i))
    (isClosed_singleton.preimage (by fun_prop))

/-- Each POVM element has operator norm bounded by `(finrank 𝕜 E : ℝ)`, since for positive `M_i`
with `∑ M_j = 1`, `‖M_i‖_op ≤ M_i.traceNorm = re tr M_i ≤ ∑ re tr M_j = re tr 1 = finrank 𝕜 E`. -/
theorem POVMSet_opNorm_le [FiniteDimensional 𝕜 E] {f : ι → E →L[𝕜] E}
    (hf : f ∈ POVMSet ι 𝕜 E) (i : ι) : ‖f i‖ ≤ (Module.finrank 𝕜 E : ℝ) := by
  obtain ⟨hf_pos_inter, hf_sum⟩ := hf
  have hf_pos := Set.mem_iInter.mp hf_pos_inter
  have h_tr_eq : ∀ j, RCLike.re (LinearMap.trace 𝕜 E ((f j : E →L[𝕜] E) : E →ₗ[𝕜] E)) =
      (f j).traceNorm :=
    fun j ↦ (ContinuousLinearMap.traceNorm_eq_re_trace_of_isPositive (hf_pos j)).symm
  calc ‖f i‖
      ≤ (f i).traceNorm := (f i).opNorm_le_traceNorm
    _ = RCLike.re (LinearMap.trace 𝕜 E ((f i : E →L[𝕜] E) : E →ₗ[𝕜] E)) := (h_tr_eq i).symm
    _ ≤ ∑ j, RCLike.re (LinearMap.trace 𝕜 E ((f j : E →L[𝕜] E) : E →ₗ[𝕜] E)) :=
        Finset.single_le_sum (f := fun j ↦ RCLike.re _)
          (fun j _ ↦ (h_tr_eq j).symm ▸ ContinuousLinearMap.traceNorm_nonneg _)
          (Finset.mem_univ i)
    _ = RCLike.re (LinearMap.trace 𝕜 E ((1 : E →L[𝕜] E) : E →ₗ[𝕜] E)) := by
        rw [← map_sum RCLike.re, ← map_sum, ← ContinuousLinearMap.toLinearMap_sum, hf_sum]
    _ = (Module.finrank 𝕜 E : ℝ) := by
        rw [ContinuousLinearMap.toLinearMap_one, LinearMap.trace_one, RCLike.natCast_re]

/-- `POVMSet ι 𝕜 E` is bounded in the operator-norm topology. -/
theorem POVMSet_isBounded [FiniteDimensional 𝕜 E] :
    Bornology.IsBounded (POVMSet ι 𝕜 E) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨(Module.finrank 𝕜 E : ℝ), fun f hf ↦ ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
  exact POVMSet_opNorm_le hf

/-- `POVMSet ι 𝕜 E` is compact in finite dimensions (Heine-Borel: closed + bounded). -/
theorem POVMSet_isCompact [FiniteDimensional 𝕜 E] :
    IsCompact (POVMSet ι 𝕜 E) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  have : ProperSpace (ι → E →L[𝕜] E) := FiniteDimensional.proper_rclike 𝕜 _
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨POVMSet_isClosed, POVMSet_isBounded⟩

open Filter Topology in
/-- A sequence of POVMs admits a subsequence whose elements converge to those of some
POVM. Corollary of `POVMSet_isCompact.tendsto_subseq` bundled via `ofMemPOVMSet`. -/
theorem exists_tendsto_elements_subseq [FiniteDimensional 𝕜 E] (M : ℕ → POVM ι 𝕜 E) :
    ∃ (M_star : POVM ι 𝕜 E) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k ↦ (M (φ k)).elements) atTop (𝓝 M_star.elements) := by
  obtain ⟨_, hf_mem, φ, hφ_mono, hφ_tendsto⟩ :=
    POVMSet_isCompact.tendsto_subseq fun n ↦ (M n).elements_mem_POVMSet
  exact ⟨ofMemPOVMSet hf_mem, φ, hφ_mono, hφ_tendsto⟩

end POVM
