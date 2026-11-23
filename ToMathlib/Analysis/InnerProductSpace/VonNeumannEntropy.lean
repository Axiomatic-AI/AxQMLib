/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Density
public import ToMathlib.Analysis.InnerProductSpace.IdempotentDensityOp
public import ToMathlib.Analysis.InnerProductSpace.TensorPower
public import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Von Neumann entropy of an operator

For a continuous linear operator `T : E →L[𝕜] E` on a finite-dimensional inner product space
over `𝕜` (where `𝕜` is `ℝ` or `ℂ`), the **von Neumann entropy** of `T` is the Shannon entropy
(in nats) of its eigenvalue spectrum:

`vonNeumannEntropy T := Real.entropy (eigenvalues T)`

with junk values on operators that are not self-adjoint (where the spectral decomposition
doesn't yield real eigenvalues uniformly). Mathematically meaningful for positive operators
and natural to interpret on **density operators** (positive trace-1 operators), where the
spectrum is a probability distribution and the entropy is bounded by `log (finrank 𝕜 E)`.

## Main definitions

- `ContinuousLinearMap.vonNeumannEntropy : (E →L[𝕜] E) → ℝ`

## Main results

- `vonNeumannEntropy_of_isSymmetric`: closed form on self-adjoint operators.
- `IsDensityOp.vonNeumannEntropy_nonneg`: nonneg on density operators.
- `IsDensityOp.vonNeumannEntropy_le_log_dim`: upper bound `log (finrank 𝕜 E)` on density
  operators of nontrivial dimension; tight for the maximally mixed state.
- `vonNeumannEntropy_rankOne_self`: a rank-one self-projector `rankOne 𝕜 v v` (with
  `‖v‖ = 1`) has zero entropy.
- `LinearMap.vonNeumannEntropy`: LM-level sibling (parallel def + rfl-bridge to CLM).
- `LinearMap.IsSymmetric.vonNeumannEntropy_tensorPow_of_sum_eigenvalues_eq_one`: tensor-iid
  scaling for symmetric operators whose eigenvalues sum to 1 — `(A ^⊗ n).vonNeumannEntropy =
  n * A.vonNeumannEntropy`. The density-operator case is `IsDensityOp.vonNeumannEntropy_tensorPow`.
- `IsDensityOp.vonNeumannEntropy_le_neg_sum_spectral_log`: **Operator Klein's inequality**
  (Nielsen–Chuang Theorem 11.7, real-level spectral form) — for density operators
  `ρ, σ` with `σ` having all-positive eigenvalues, `S(ρ) ≤ -∑ᵢ pᵢ * ∑ⱼ ‖⟨fⱼ, eᵢ⟩‖² * log qⱼ`
  where `(pᵢ, eᵢ)` and `(qⱼ, fⱼ)` are the spectral data of `ρ` and `σ`.
- `IsDensityOp.vonNeumannEntropy_le_neg_re_trace_cfc_log_comp`: **Trace form of operator
  Klein** — `S(ρ) ≤ -re(tr((cfc log σ) ∘ ρ))`. Natural shape for combining via trace
  linearity (consumed by concavity).
- `IsDensityOp.re_trace_cfc_log_self_eq_neg_vonNeumannEntropy`: **Self-trace expansion** —
  `re(tr((cfc log σ) ∘ σ)) = -S(σ)`. Trace of σ against its own log equals negative entropy.
- `IsDensityOp.vonNeumannEntropy_convex_combination_le`: **Concavity of vNE** (NC Theorem
  11.8) — for a mixture `σ = ∑ᵢ pᵢ ρᵢ` of density operators with `σ`'s eigenvalues positive,
  `∑ᵢ pᵢ S(ρᵢ) ≤ S(σ)`. NC §11.3.5's textbook trace-form chain.
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

open scoped Classical in
/-- The **von Neumann entropy** of an operator: the Shannon entropy of its eigenvalue
spectrum if self-adjoint, with a junk value of `0` otherwise. -/
noncomputable def vonNeumannEntropy (T : E →L[𝕜] E) : ℝ :=
  if h : T.toLinearMap.IsSymmetric
    then Real.entropy fun i : Fin (Module.finrank 𝕜 E) ↦ h.eigenvalues rfl i
    else 0

/-- Closed form for the von Neumann entropy on a self-adjoint operator. -/
theorem vonNeumannEntropy_of_isSymmetric {T : E →L[𝕜] E}
    (h : T.toLinearMap.IsSymmetric) :
    T.vonNeumannEntropy = Real.entropy fun i : Fin (Module.finrank 𝕜 E) ↦ h.eigenvalues rfl i := by
  rw [vonNeumannEntropy, dite_eq_left h]

theorem vonNeumannEntropy_of_not_isSymmetric {T : E →L[𝕜] E}
    (h : ¬ T.toLinearMap.IsSymmetric) :
    T.vonNeumannEntropy = 0 := by
  rw [vonNeumannEntropy, dite_eq_right h]

/-- The von Neumann entropy of a density operator is non-negative. -/
theorem IsDensityOp.vonNeumannEntropy_nonneg {T : E →L[𝕜] E} (h : T.IsDensityOp) :
    0 ≤ T.vonNeumannEntropy := by
  rw [vonNeumannEntropy_of_isSymmetric h.isSymmetric]
  exact Real.entropy_nonneg
    (fun i ↦ h.eigenvalues_nonneg rfl i)
    (fun i ↦ h.eigenvalues_le_one rfl i)

/-- The von Neumann entropy of a density operator on a nontrivial space is at most
`log (finrank 𝕜 E)`. The bound is tight for the maximally mixed state. -/
theorem IsDensityOp.vonNeumannEntropy_le_log_dim [Nontrivial E] {T : E →L[𝕜] E}
    (h : T.IsDensityOp) :
    T.vonNeumannEntropy ≤ Real.log (Module.finrank 𝕜 E) := by
  rw [vonNeumannEntropy_of_isSymmetric h.isSymmetric]
  have : Nonempty (Fin (Module.finrank 𝕜 E)) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  simpa using Real.entropy_le_log_card
    (fun i ↦ h.eigenvalues_nonneg rfl i)
    (h.eigenvalues_sum_eq_one rfl)

/-- The von Neumann entropy of a rank-one self-projector `rankOne 𝕜 v v` (with `‖v‖ = 1`)
is zero. In the quantum-information interpretation, this is the entropy of a pure state. -/
theorem vonNeumannEntropy_rankOne_self {v : E} (hv : ‖v‖ = 1) :
    (InnerProductSpace.rankOne 𝕜 v v).vonNeumannEntropy = 0 := by
  have hsymm := InnerProductSpace.isSymmetric_rankOne_self v (𝕜 := 𝕜)
  rw [vonNeumannEntropy_of_isSymmetric hsymm, Real.entropy_eq]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rcases (ContinuousLinearMap.IsIdempotentElem.toLinearMap
      (InnerProductSpace.isIdempotentElem_rankOne_self hv)).eigenvalues_zero_or_one hsymm rfl i
    with hi | hi <;> simp [hi]

/-- Helper: the von Neumann entropy of a self-adjoint operator equals the entropy of its
eigenvalue sequence under any choice of finrank-witness `hn`, not just `rfl`. This lets us
align the index types when comparing entropies on different (but equi-dimensional) spaces. -/
lemma vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq {T : E →L[𝕜] E}
    (h : T.toLinearMap.IsSymmetric) {n : ℕ} (hn : Module.finrank 𝕜 E = n) :
    T.vonNeumannEntropy = Real.entropy fun i : Fin n ↦ h.eigenvalues hn i := by
  subst hn
  exact vonNeumannEntropy_of_isSymmetric h

/-- **Isometry invariance of von Neumann entropy.** Conjugating an operator by a linear
isometry preserves the eigenvalue spectrum (via charpoly invariance under linear-equiv
conjugation), hence preserves the von Neumann entropy. -/
theorem vonNeumannEntropy_conjStarAlgEquiv [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [CompleteSpace F] (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    (e.conjStarAlgEquiv T).vonNeumannEntropy = T.vonNeumannEntropy := by
  have hSA_iff := T.toLinearMap.isSymmetric_linearIsometryEquiv_conj_iff e
  have hfinrank : Module.finrank 𝕜 F = Module.finrank 𝕜 E := e.toLinearEquiv.finrank_eq.symm
  by_cases h : T.toLinearMap.IsSymmetric
  · have hconj : (e.conjStarAlgEquiv T).toLinearMap.IsSymmetric := hSA_iff.mpr h
    rw [vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq hconj hfinrank,
      vonNeumannEntropy_of_isSymmetric h,
      (hconj.eigenvalues_eq_eigenvalues_iff hfinrank h rfl).mpr
        (e.toLinearEquiv.charpoly_conj T.toLinearMap)]
  · rw [vonNeumannEntropy_of_not_isSymmetric h,
      vonNeumannEntropy_of_not_isSymmetric (h ∘ hSA_iff.mp)]

/-- **Operator Klein's inequality** (Nielsen–Chuang Theorem 11.7, real-level spectral form):
for density operators `ρ, σ : E →L[ℂ] E` with `σ`'s eigenvalues all positive, the von Neumann
entropy of `ρ` is bounded above by the negation of `tr(ρ log σ)`'s spectral expansion:
```
ρ.vonNeumannEntropy ≤ -∑ᵢ pᵢ * ∑ⱼ ‖⟨fⱼ, eᵢ⟩‖² * log qⱼ
```
where `(pᵢ, eᵢ)` and `(qⱼ, fⱼ)` are the eigenvalue/eigenvector pairs of `ρ` and `σ`. The RHS
is the spectral form of `-RCLike.re (tr((cfc log σ) ∘ ρ))` (via `trace_comp_cfc_eq_double_sum`).

**Proof.** Apply `Real.sum_mul_sum_mul_log_le_neg_entropy_of_doubly_stochastic` with weights
`Wᵢⱼ := ‖⟨fⱼ, eᵢ⟩‖²`. The doubly-stochastic property follows from Parseval
(`OrthonormalBasis.sum_sq_norm_inner_right`) applied to the orthonormal eigenbases. -/
theorem IsDensityOp.vonNeumannEntropy_le_neg_sum_spectral_log
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E]
    {ρ σ : E →L[ℂ] E} (hρ : ρ.IsDensityOp) (hσ : σ.IsDensityOp)
    (hσ_pos : ∀ j, 0 < hσ.isSymmetric.eigenvalues rfl j) :
    ρ.vonNeumannEntropy ≤
      -∑ i, hρ.isSymmetric.eigenvalues rfl i *
        ∑ j, ‖⟪hσ.isSymmetric.eigenvectorBasis rfl j,
                hρ.isSymmetric.eigenvectorBasis rfl i⟫_ℂ‖ ^ 2
              * Real.log (hσ.isSymmetric.eigenvalues rfl j) := by
  set eρ := hρ.isSymmetric.eigenvectorBasis rfl
  set eσ := hσ.isSymmetric.eigenvectorBasis rfl
  rw [vonNeumannEntropy_of_isSymmetric hρ.isSymmetric, le_neg]
  refine Real.sum_mul_sum_mul_log_le_neg_entropy_of_doubly_stochastic
    (hρ.eigenvalues_nonneg rfl) hσ_pos (hρ.eigenvalues_sum_eq_one rfl)
    (hσ.eigenvalues_sum_eq_one rfl) (fun _ _ ↦ sq_nonneg _) (fun i ↦ ?_) (fun j ↦ ?_)
  · rw [eσ.sum_sq_norm_inner_right, eρ.orthonormal.1, one_pow]
  · simp_rw [← norm_inner_symm (𝕜 := ℂ), eρ.sum_sq_norm_inner_right, eσ.orthonormal.1, one_pow]

/-- `Real.log` is continuous on the spectrum of a positive-spectrum density operator
(since the spectrum is then a subset of `{0}ᶜ`, where `Real.log` is continuous). Reusable
continuity-discharge for `cfc Real.log σ` consumers in trace-form computations.
Density-op specialization of `IsSelfAdjoint.continuousOn_log_spectrum_of_eigenvalues_pos`. -/
private theorem IsDensityOp.continuousOn_log_spectrum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    {σ : E →L[ℂ] E} (hσ : σ.IsDensityOp)
    (hσ_pos : ∀ j, 0 < hσ.isSymmetric.eigenvalues rfl j) :
    ContinuousOn Real.log (spectrum ℝ σ) :=
  hσ.isPositive.isSelfAdjoint.continuousOn_log_spectrum_of_eigenvalues_pos rfl hσ_pos

/-- **Operator Klein's inequality, trace form** (Nielsen–Chuang Theorem 11.7): for density
operators `ρ, σ : E →L[ℂ] E` with `σ`'s eigenvalues all positive,
`S(ρ) ≤ -re(tr((cfc log σ) ∘ ρ))`. The trace form is the natural shape for combining via
trace linearity (the chain used in NC's proof of concavity, Theorem 11.8); it follows from
the spectral form (`vonNeumannEntropy_le_neg_sum_spectral_log`) by identifying the
real-coerced spectral sum with the real part of the complex trace expansion (Q1.3.B1
`trace_comp_cfc_eq_double_sum` applied with `f := Real.log`). -/
theorem IsDensityOp.vonNeumannEntropy_le_neg_re_trace_cfc_log_comp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E]
    {ρ σ : E →L[ℂ] E} (hρ : ρ.IsDensityOp) (hσ : σ.IsDensityOp)
    (hσ_pos : ∀ j, 0 < hσ.isSymmetric.eigenvalues rfl j) :
    ρ.vonNeumannEntropy ≤
      -RCLike.re (LinearMap.trace ℂ E ((cfc Real.log σ).toLinearMap ∘ₗ ρ.toLinearMap)) := by
  refine (hρ.vonNeumannEntropy_le_neg_sum_spectral_log hσ hσ_pos).trans_eq ?_
  congr 1
  rw [hρ.isPositive.isSelfAdjoint.trace_comp_cfc_eq_double_sum
    hσ.isPositive.isSelfAdjoint rfl Real.log (hσ.continuousOn_log_spectrum hσ_pos)]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ ↦ congr_arg _ <| Finset.sum_congr rfl fun j _ ↦ by ring

/-- **Self-trace expansion**: for *any* density operator `σ : E →L[ℂ] E`,
`re(tr((cfc log σ) ∘ σ)) = -S(σ)` — no positivity needed (`Real.log` is continuous on the finite
spectrum unconditionally, and a zero eigenvalue contributes `0·log 0 = 0` on both sides). The "trace
of σ against its own log" equals the negative von Neumann entropy. Proof: specialize
`trace_comp_cfc_eq_double_sum` with `T := σ`, `U := σ`, `f := Real.log`; orthonormality of σ's
eigenbasis collapses the overlap inner-sum to a Kronecker delta; the resulting `∑ᵢ μᵢ * log μᵢ`
matches `-Real.entropy μ` by `negMulLog` unfolding. -/
theorem IsDensityOp.re_trace_cfc_log_self_eq_neg_vonNeumannEntropy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E]
    {σ : E →L[ℂ] E} (hσ : σ.IsDensityOp) :
    RCLike.re (LinearMap.trace ℂ E ((cfc Real.log σ).toLinearMap ∘ₗ σ.toLinearMap)) =
      -σ.vonNeumannEntropy := by
  rw [hσ.isPositive.isSelfAdjoint.trace_comp_cfc_eq_double_sum hσ.isPositive.isSelfAdjoint rfl
    Real.log hσ.isPositive.isSelfAdjoint.continuousOn_log_spectrum,
    vonNeumannEntropy_of_isSymmetric hσ.isSymmetric, Real.entropy]
  set eσ := hσ.isSymmetric.eigenvectorBasis rfl
  -- Orthonormal collapse: `‖⟪eσ j, eσ i⟫‖² = if j = i then 1 else 0`, so inner sum = log μᵢ.
  have h_inner : ∀ i, ∑ j, ((Real.log (hσ.isSymmetric.eigenvalues rfl j) : ℝ) : ℂ) *
        ((‖⟪eσ j, eσ i⟫_ℂ‖ : ℂ) ^ 2) =
      ((Real.log (hσ.isSymmetric.eigenvalues rfl i) : ℝ) : ℂ) := fun i ↦ by
    rw [Finset.sum_eq_single i]
    · rw [(orthonormal_iff_ite (𝕜 := ℂ)).mp eσ.orthonormal, ite_eq_left rfl]; simp
    · intro j _ hji
      rw [(orthonormal_iff_ite (𝕜 := ℂ)).mp eσ.orthonormal, ite_eq_right hji]; simp
    · simp
  -- `RCLike.re ↑r = r` is rfl-true but `RCLike.ofReal_re` doesn't unify in simp here
  -- (the goal's `↑` elaborates via `Complex.ofReal` rather than `RCLike`'s coercion).
  simp only [h_inner, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Real.negMulLog,
    show ∀ r : ℝ, RCLike.re (r : ℂ) = r from fun _ ↦ rfl, neg_mul,
    Finset.sum_neg_distrib, neg_neg]

/-- **Diagonal form of the self-trace expansion**: for any density operator `σ`, the sum of
`log(λᵢ)` weighted by the quadratic form of `σ` in its own eigenbasis equals `-S(σ)`:
`∑ᵢ log(λᵢ)·re⟪eᵢ, σ eᵢ⟫ = -S(σ)`. The eigenbasis (sum) form of
`re_trace_cfc_log_self_eq_neg_vonNeumannEntropy`, obtained by expanding its trace over `σ`'s
eigenbasis via `re_trace_cfc_comp_eq_sum`. -/
theorem IsDensityOp.sum_log_eigenvalue_mul_re_inner_self_eq_neg_vonNeumannEntropy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E] {σ : E →L[ℂ] E} (hσ : σ.IsDensityOp) :
    ∑ i, Real.log (hσ.isSymmetric.eigenvalues rfl i) *
        RCLike.re ⟪hσ.isSymmetric.eigenvectorBasis rfl i,
          σ (hσ.isSymmetric.eigenvectorBasis rfl i)⟫_ℂ =
      -σ.vonNeumannEntropy :=
  (hσ.isPositive.isSelfAdjoint.re_trace_cfc_comp_eq_sum rfl Real.log
    hσ.isPositive.isSelfAdjoint.continuousOn_log_spectrum σ).symm.trans
    hσ.re_trace_cfc_log_self_eq_neg_vonNeumannEntropy

/-- **`re ∘ trace ∘ (A ∘ -)` distributes over real-scalar-weighted CLM finite sums**:
for `A : E →L[ℂ] E`, the map `B ↦ re(trace(A.toLinearMap ∘ B.toLinearMap))` respects sums of
the form `∑ᵢ (cᵢ : ℂ) • Bᵢ`, pulling the real coefficients `cᵢ` out as ordinary real
multiplication. Reusable trace-linearity bridge for trace-of-mixture computations
(e.g., concavity-of-vNE in NC §11.3.5). -/
theorem re_trace_comp_clm_finset_sum_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E] (A : E →L[ℂ] E)
    {ι : Type*} [Fintype ι] (B : ι → E →L[ℂ] E) (c : ι → ℝ) :
    RCLike.re (LinearMap.trace ℂ E
        (A.toLinearMap ∘ₗ ((∑ i, (c i : ℂ) • B i) : E →L[ℂ] E).toLinearMap)) =
      ∑ i, c i * RCLike.re (LinearMap.trace ℂ E (A.toLinearMap ∘ₗ (B i).toLinearMap)) := by
  rw [← ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.comp_finsetSum]
  simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.toLinearMap_sum,
    ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_comp, map_sum,
    map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ RCLike.re_ofReal_mul _ _

/-- **Concavity of von Neumann entropy** (Nielsen–Chuang Theorem 11.8): for a finite mixture
`σ = ∑ᵢ pᵢ ρᵢ` of density operators with `pᵢ ≥ 0` (probabilities; sum-to-1 implied by all
σ being a density op),
```
∑ᵢ pᵢ S(ρᵢ) ≤ S(σ).
```
Requires `σ`'s eigenvalues all positive (needed for the `cfc Real.log σ` continuity in the
trace-form Klein helper). NC §11.3.5: apply trace-form Klein to each `ρᵢ` against `σ` as
the reference, multiply by `pᵢ`, and sum; linearity of trace identifies the weighted sum
of cross-terms `∑ᵢ pᵢ tr(ρᵢ log σ)` with `tr(σ log σ) = -S(σ)`. This is the textbook
chain; the path avoids Lieb's joint concavity (needed for SSA, Q1.3.C). -/
theorem IsDensityOp.vonNeumannEntropy_convex_combination_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E]
    {ι : Type*} [Fintype ι] {ρ : ι → E →L[ℂ] E} (hρ : ∀ i, (ρ i).IsDensityOp)
    {σ : E →L[ℂ] E} (hσ : σ.IsDensityOp) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hσ_eq : σ = ∑ i, (p i : ℂ) • ρ i)
    (hσ_pos : ∀ k, 0 < hσ.isSymmetric.eigenvalues rfl k) :
    ∑ i, p i * (ρ i).vonNeumannEntropy ≤ σ.vonNeumannEntropy := by
  refine (Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
    ((hρ i).vonNeumannEntropy_le_neg_re_trace_cfc_log_comp hσ hσ_pos) (hp i)).trans ?_
  -- Bridge `∑ pᵢ * re(tr(A ∘ ρᵢ)) = re(tr(A ∘ σ))` via `re_trace_comp_clm_finset_sum_smul`
  -- + `hσ_eq`. Close via Helper B (self-trace = -S identity).
  simp_rw [mul_neg, Finset.sum_neg_distrib,
    ← re_trace_comp_clm_finset_sum_smul (cfc Real.log σ) ρ p, ← hσ_eq,
    hσ.re_trace_cfc_log_self_eq_neg_vonNeumannEntropy, neg_neg]
  exact le_rfl

end ContinuousLinearMap

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

open scoped Classical in
/-- LM-level **von Neumann entropy**: parallel to the CLM definition. For a linear endomorphism
`A : E →ₗ[𝕜] E`, the entropy of its eigenvalue spectrum (junk-`0` on non-symmetric inputs). -/
noncomputable def vonNeumannEntropy (A : E →ₗ[𝕜] E) : ℝ :=
  if h : A.IsSymmetric
    then Real.entropy fun i : Fin (Module.finrank 𝕜 E) ↦ h.eigenvalues rfl i
    else 0

theorem vonNeumannEntropy_of_isSymmetric {A : E →ₗ[𝕜] E} (h : A.IsSymmetric) :
    A.vonNeumannEntropy = Real.entropy fun i : Fin (Module.finrank 𝕜 E) ↦ h.eigenvalues rfl i := by
  rw [vonNeumannEntropy, dite_eq_left h]

theorem vonNeumannEntropy_of_not_isSymmetric {A : E →ₗ[𝕜] E} (h : ¬ A.IsSymmetric) :
    A.vonNeumannEntropy = 0 := by
  rw [vonNeumannEntropy, dite_eq_right h]

/-- Helper: the LM-level von Neumann entropy of a symmetric operator equals the entropy of its
eigenvalue sequence under any choice of finrank-witness `hn`. LM-level analog of the CLM
`ContinuousLinearMap.vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq`. -/
lemma vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq {A : E →ₗ[𝕜] E}
    (h : A.IsSymmetric) {n : ℕ} (hn : Module.finrank 𝕜 E = n) :
    A.vonNeumannEntropy = Real.entropy fun i : Fin n ↦ h.eigenvalues hn i := by
  subst hn
  exact vonNeumannEntropy_of_isSymmetric h

/-- **Tensor-iid scaling of von Neumann entropy** (LM-level): for symmetric `A : E →ₗ[𝕜] E`
whose eigenvalues sum to one (e.g., the LM of a density operator),
`(A ^⊗ n).vonNeumannEntropy = n * A.vonNeumannEntropy`.

Proof: the multiset of eigenvalues of `A ^⊗ n` (via
`LinearMap.IsSymmetric.tensorPow_eigenvalues_multiset_eq`) is the multiset of products
`∏ i, A.eigenvalues (κ i)` over `κ : Fin n → Fin d`. Bridging Finset-sum to Multiset-sum via
this equality reduces the LHS entropy to `Real.entropy (fun κ ↦ ∏ i, A.eigenvalues (κ i))`,
which is `n * A.vonNeumannEntropy` by `Real.entropy_pi_prod_of_sum_eq_one`. -/
theorem IsSymmetric.vonNeumannEntropy_tensorPow_of_sum_eigenvalues_eq_one
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hsum : ∑ i, hA.eigenvalues rfl i = 1) (n : ℕ) :
    (A ^⊗ n).vonNeumannEntropy = n * A.vonNeumannEntropy := by
  rw [vonNeumannEntropy_of_isSymmetric (hA.tensorPow n),
    vonNeumannEntropy_of_isSymmetric hA, ← Real.entropy_pi_prod_of_sum_eq_one hsum n]
  exact Real.entropy_eq_of_multiset_map_eq (hA.tensorPow_eigenvalues_multiset_eq n rfl rfl).symm

/-- **Binary tensor-product additivity of von Neumann entropy** (LM-level, abstract).
For symmetric operators `A : E →ₗ[𝕜] E` and `B : F →ₗ[𝕜] F` (on finite-dim inner product
spaces) whose eigenvalues each sum to 1:
`(TensorProduct.map A B).vonNeumannEntropy = A.vonNeumannEntropy + B.vonNeumannEntropy`.

Proof: multiset-bridge pattern, using `tensorMap_eigenvalues_multiset_eq`
(binary multiset equality) + `Real.entropy_prod` (binary product additivity).
The dimension witness uses `Module.finrank_tensorProduct` for `finrank (E ⊗ F) = dE * dF`. -/
theorem IsSymmetric.vonNeumannEntropy_tensorMap_of_sum_eigenvalues_eq_one
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hsumA : ∑ i : Fin (Module.finrank 𝕜 E), hA.eigenvalues rfl i = 1)
    {B : F →ₗ[𝕜] F} (hB : B.IsSymmetric)
    (hsumB : ∑ j : Fin (Module.finrank 𝕜 F), hB.eigenvalues rfl j = 1) :
    (TensorProduct.map A B : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F).vonNeumannEntropy =
      A.vonNeumannEntropy + B.vonNeumannEntropy := by
  have h_tensor_finrank : Module.finrank 𝕜 (E ⊗[𝕜] F) =
      Module.finrank 𝕜 E * Module.finrank 𝕜 F := Module.finrank_tensorProduct
  rw [vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq (hA.tensorMap hB) h_tensor_finrank,
    vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq hA rfl,
    vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq hB rfl,
    ← Real.entropy_prod hsumA hsumB]
  exact Real.entropy_eq_of_multiset_map_eq
    (hA.tensorMap_eigenvalues_multiset_eq hB rfl rfl h_tensor_finrank).symm

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- **rfl-bridge: CLM `vonNeumannEntropy` equals LM `vonNeumannEntropy` of `toLinearMap`.** The
two definitions are structurally identical (both dispatch on `T.toLinearMap.IsSymmetric` and
compute `Real.entropy` of the eigenvalue spectrum). -/
@[simp] theorem vonNeumannEntropy_toLinearMap (T : E →L[𝕜] E) :
    T.toLinearMap.vonNeumannEntropy = T.vonNeumannEntropy := rfl

/-- **Tensor-iid scaling of von Neumann entropy** (density-operator form). For a density
operator `ρ`, the CLM-level `vonNeumannEntropy` of the n-fold tensor-power LM `ρ^⊗n`
(via the LM-level bridge) scales as `n * ρ.vonNeumannEntropy`. -/
theorem IsDensityOp.vonNeumannEntropy_tensorPow {ρ : E →L[𝕜] E} (hρ : ρ.IsDensityOp) (n : ℕ) :
    (ρ.toLinearMap ^⊗ n).vonNeumannEntropy = n * ρ.vonNeumannEntropy := by
  rw [← vonNeumannEntropy_toLinearMap]
  exact hρ.isSymmetric.vonNeumannEntropy_tensorPow_of_sum_eigenvalues_eq_one
    (hρ.eigenvalues_sum_eq_one rfl) n

/-- **Binary tensor-product additivity of von Neumann entropy** (abstract, density-operator
form). For density operators `ρ : E →L[𝕜] E` and `σ : F →L[𝕜] F` on finite-dim inner product
spaces:
`(TensorProduct.map ρ.toLinearMap σ.toLinearMap).vonNeumannEntropy =
  ρ.vonNeumannEntropy + σ.vonNeumannEntropy`.

Density operators delegate via `vonNeumannEntropy_toLinearMap` (rfl bridge) to the
LM-level `IsSymmetric.vonNeumannEntropy_tensorMap_of_sum_eigenvalues_eq_one`. -/
theorem IsDensityOp.vonNeumannEntropy_tensorMap
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {ρ : E →L[𝕜] E} (hρ : ρ.IsDensityOp) {σ : F →L[𝕜] F} (hσ : σ.IsDensityOp) :
    (TensorProduct.map ρ.toLinearMap σ.toLinearMap :
        E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F).vonNeumannEntropy =
      ρ.vonNeumannEntropy + σ.vonNeumannEntropy := by
  rw [← vonNeumannEntropy_toLinearMap (T := ρ), ← vonNeumannEntropy_toLinearMap (T := σ)]
  exact hρ.isSymmetric.vonNeumannEntropy_tensorMap_of_sum_eigenvalues_eq_one
    (hρ.eigenvalues_sum_eq_one rfl) hσ.isSymmetric (hσ.eigenvalues_sum_eq_one rfl)

end ContinuousLinearMap

namespace ContinuousLinearMap

/-- **Von Neumann entropy of the maximally mixed operator** `S((1/d) • I) = log d`, where
`d = finrank ℂ E`. This is the equality case of the upper bound
`ContinuousLinearMap.IsDensityOp.vonNeumannEntropy_le_log_dim`: the maximally mixed operator
`(finrank ℂ E)⁻¹ • 1` (a density operator by `isDensityOp_finrank_inv_smul_one`) attains the
`log d` bound. Its `d` eigenvalues all equal `1/d` (read off from
`LinearMap.IsSymmetric.apply_eigenvectorBasis`, since it is a real scalar multiple of the
identity), so the entropy is the Shannon entropy of the uniform spectrum,
`d · negMulLog(1/d) = log d` (`Real.entropy_const`). -/
theorem vonNeumannEntropy_finrank_inv_smul_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E] [Nontrivial E] :
    ((Module.finrank ℂ E : ℂ)⁻¹ • (1 : E →L[ℂ] E)).vonNeumannEntropy
      = Real.log (Module.finrank ℂ E) := by
  have hne : (Module.finrank ℂ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  -- The operator `(1/d) • I` is self-adjoint (a real scalar times the identity).
  have hsa : IsSelfAdjoint ((Module.finrank ℂ E : ℂ)⁻¹ • (1 : E →L[ℂ] E)) := by
    refine IsSelfAdjoint.smul ?_ (isSelfAdjoint_iff.mpr (star_one _))
    rw [isSelfAdjoint_iff]; simp
  have hsym := hsa.isSymmetric
  rw [ContinuousLinearMap.vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq hsym rfl]
  -- Every eigenvalue of `(1/d) • I` equals `1/d`.
  have heig : (fun i => hsym.eigenvalues rfl i)
      = (fun _ : Fin (Module.finrank ℂ E) => (Module.finrank ℂ E : ℝ)⁻¹) := by
    funext i
    have h := hsym.apply_eigenvectorBasis rfl i
    simp only [ContinuousLinearMap.coe_coe, _root_.smul_apply,
      one_apply_eq_self] at h
    have hv : (hsym.eigenvectorBasis rfl) i ≠ 0 :=
      (hsym.eigenvectorBasis rfl).orthonormal.ne_zero i
    have hsc : (Module.finrank ℂ E : ℂ)⁻¹ = ((hsym.eigenvalues rfl i : ℝ) : ℂ) :=
      smul_left_injective ℂ hv h
    refine Complex.ofReal_inj.mp ?_
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
    exact hsc.symm
  -- `H(1/d, …, 1/d) = d · negMulLog(1/d) = log d`.
  rw [heig, Real.entropy_const, Fintype.card_fin, Real.negMulLog, Real.log_inv]
  field_simp

end ContinuousLinearMap
