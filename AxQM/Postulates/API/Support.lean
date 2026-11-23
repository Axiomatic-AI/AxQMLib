/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SchmidtNumber
import ToMathlib.Analysis.InnerProductSpace.Spectrum
import ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# AxQM — the support of a density operator

Nielsen & Chuang, in Exercise 2.73, work with the **support** of a density operator `ρ`:
*"the vector space spanned by the eigenvectors of `ρ` with non-zero eigenvalues"* (the general
definition, stated there for a Hermitian operator `A`, is the span of its non-kernel eigenvectors).
Equivalently — and this is the definition we take — the support is the **range** of `ρ`, and, since
`ρ` is self-adjoint, the **orthogonal complement of its kernel**:
`support ρ = range ρ = (ker ρ)ᗮ`.

The three descriptions coincide because `ρ` is symmetric:
`LinearMap.IsSymmetric.range_eq_orthogonal_ker` gives `range = kerᗮ`, and the kernel of a
self-adjoint operator is the span of its zero-eigenvalue eigenvectors, so `kerᗮ` is the span of the
non-zero-eigenvalue eigenvectors — N&C's phrasing.

Taking `support := range ρ` makes the dimension identity free: the **rank** `ρ.rank`
(`AxQM.State.rank`) is defined as `finrank (range ρ)`, so `finrank (support ρ) = ρ.rank`
holds definitionally. That rank identity is what the *minimal ensemble* part of Exercise 2.73
needs: a minimal ensemble has exactly `rank ρ = finrank (support ρ)` elements.

## Main definitions

* `AxQM.State.support` — the support `range ρ` of a density operator, a `Submodule`.

## Main results

* `State.rank_eq_finrank_support` — `ρ.rank = finrank (support ρ)` (definitional).
* `State.support_eq_orthogonal_ker` — `support ρ = (ker ρ)ᗮ` (self-adjointness).
* `State.eigenvectorBasis_mem_ker_of_eigenvalue_eq_zero` — a zero-eigenvalue eigenvector lies in
  `ker ρ` (zero-eigenspace = kernel); the shared building block behind the two lemmas below.
* `State.eigenvectorBasis_mem_support_iff` — an eigenvector `bⱼ` lies in the support iff its
  eigenvalue is non-zero: the "span of non-zero eigenvectors" characterization of N&C.
* `State.inner_eigenvectorBasis_eq_zero_of_mem_support` — a state `ψ` in the support has zero
  overlap with every zero-eigenvalue eigenvector `⟪bⱼ, ψ⟫ = 0`. This expresses "`|ψ⟩` lies in the
  support" and shows that `⟨ψ|ρ⁻¹|ψ⟩` is a genuine (finite, positive) quantity even though `ρ⁻¹`
  kills the kernel.
* `State.support_isOrtho_iff_op_mul_eq_zero` — **orthogonal supports as a vanishing operator
  product**: `ρ.support ⟂ σ.support ↔ ρ.op * σ.op = 0`. An operator-level formulation of
  "the states have orthogonal supports", used by the equality condition of the entropy-of-a-mixture
  bound (N&C Theorem 11.10).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace State

/-- **The support of a density operator** (Nielsen–Chuang Exercise 2.73): the range of `ρ`, which —
since `ρ` is self-adjoint — is the span of the eigenvectors of `ρ` with non-zero eigenvalues
(equivalently `(ker ρ)ᗮ`, see `support_eq_orthogonal_ker`). Defined as `range ρ` so that the rank
identity `finrank (support ρ) = ρ.rank` is definitional. -/
def support (ρ : State S) : Submodule ℂ S.space :=
  LinearMap.range (ρ.op : S.space →ₗ[ℂ] S.space)

/-- **The rank of `ρ` is the dimension of its support**: `ρ.rank = finrank (support ρ)`. Holds by
definition (`State.rank` is `finrank (range ρ)` and `support ρ = range ρ`); recorded as a named
lemma because the minimal-ensemble development refers to `finrank (support ρ)` and to `ρ.rank`
interchangeably. -/
theorem rank_eq_finrank_support (ρ : State S) :
    ρ.rank = Module.finrank ℂ ρ.support :=
  rfl

/-- **The support is the orthogonal complement of the kernel**: `support ρ = (ker ρ)ᗮ`. For a
self-adjoint operator the range equals `kerᗮ` (`LinearMap.IsSymmetric.range_eq_orthogonal_ker`), and
`ρ` is symmetric as a density operator. -/
theorem support_eq_orthogonal_ker (ρ : State S) :
    ρ.support = (LinearMap.ker (ρ.op : S.space →ₗ[ℂ] S.space))ᗮ :=
  ρ.isDensity.isSymmetric.range_eq_orthogonal_ker

/-- **A zero-eigenvalue eigenvector lies in the kernel**: if `λⱼ = 0` then `bⱼ ∈ ker ρ`. The
zero-eigenspace of a density operator is exactly its kernel — the foundational spectral fact dual to
`support_eq_orthogonal_ker` (`support = kerᗮ`), and the shared building block behind both the
"span of non-zero eigenvectors" characterization and the coefficient-vanishing handle below. -/
theorem eigenvectorBasis_mem_ker_of_eigenvalue_eq_zero (ρ : State S)
    (j : Fin (Module.finrank ℂ S.space))
    (hj : ρ.isDensity.isSymmetric.eigenvalues rfl j = 0) :
    ρ.isDensity.isSymmetric.eigenvectorBasis rfl j ∈
      LinearMap.ker (ρ.op : S.space →ₗ[ℂ] S.space) := by
  rw [LinearMap.mem_ker, ρ.isDensity.isSymmetric.apply_eigenvectorBasis rfl j, hj]; simp

/-- **The support is spanned by the non-zero eigenvectors** (Nielsen–Chuang's phrasing): an
eigenvector `bⱼ` of `ρ` lies in the support iff its eigenvalue `λⱼ` is non-zero. Forward: if
`λⱼ = 0` then `bⱼ ∈ ker ρ`, and `bⱼ ∈ support = kerᗮ` would force `⟪bⱼ, bⱼ⟫ = 0`, contradicting
`‖bⱼ‖ = 1`. Backward: if `λⱼ ≠ 0` then `bⱼ = ρ (λⱼ⁻¹ • bⱼ) ∈ range ρ`. -/
theorem eigenvectorBasis_mem_support_iff (ρ : State S)
    (j : Fin (Module.finrank ℂ S.space)) :
    ρ.isDensity.isSymmetric.eigenvectorBasis rfl j ∈ ρ.support ↔
      ρ.isDensity.isSymmetric.eigenvalues rfl j ≠ 0 := by
  set hsym := ρ.isDensity.isSymmetric with hsym_def
  have hb : (ρ.op : S.space →ₗ[ℂ] S.space) (hsym.eigenvectorBasis rfl j)
      = (hsym.eigenvalues rfl j : ℂ) • hsym.eigenvectorBasis rfl j :=
    hsym.apply_eigenvectorBasis rfl j
  constructor
  · intro hmem hμ
    rw [support_eq_orthogonal_ker] at hmem
    have h0 : inner ℂ (hsym.eigenvectorBasis rfl j) (hsym.eigenvectorBasis rfl j) = 0 :=
      Submodule.inner_right_of_mem_orthogonal
        (ρ.eigenvectorBasis_mem_ker_of_eigenvalue_eq_zero j hμ) hmem
    rw [orthonormal_iff_ite.mp (hsym.eigenvectorBasis rfl).orthonormal j j, ite_eq_left rfl] at h0
    exact one_ne_zero h0
  · intro hμ
    rw [support, LinearMap.mem_range]
    refine ⟨(hsym.eigenvalues rfl j : ℂ)⁻¹ • hsym.eigenvectorBasis rfl j, ?_⟩
    rw [map_smul, hb, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hμ), one_smul]

/-- **A state in the support is orthogonal to every zero-eigenvalue eigenvector**: if
`ψ ∈ support ρ` and `λⱼ = 0`, then `⟪bⱼ, ψ⟫ = 0`. Since `λⱼ = 0` gives `bⱼ ∈ ker ρ` and
`support = kerᗮ`, the two are orthogonal. This is the formal content of "`|ψ⟩` lies in the support
of `ρ`": `ψ` has no component along the kernel, so its expansion runs over the non-zero
eigenvectors only. -/
theorem inner_eigenvectorBasis_eq_zero_of_mem_support (ρ : State S) {ψ : S.space}
    (hψ : ψ ∈ ρ.support) (j : Fin (Module.finrank ℂ S.space))
    (hj : ρ.isDensity.isSymmetric.eigenvalues rfl j = 0) :
    inner ℂ (ρ.isDensity.isSymmetric.eigenvectorBasis rfl j) ψ = 0 := by
  rw [support_eq_orthogonal_ker] at hψ
  exact Submodule.inner_right_of_mem_orthogonal
    (ρ.eigenvectorBasis_mem_ker_of_eigenvalue_eq_zero j hj) hψ

/-- **Orthogonal supports as a vanishing operator product** — the operator-level
characterization of "the states `ρ`, `σ` have orthogonal supports": the supports are orthogonal
submodules iff the product of the density operators vanishes,

`ρ.support ⟂ σ.support ↔ ρ.op * σ.op = 0`.

Commuting the orthogonality (`Submodule.isOrtho_comm`) puts the roles the right way round; then
`support ρ = range ρ.op`, `ρ.op` self-adjoint so `(ker ρ.op)ᗮᗮ = ker ρ.op`
(`support_eq_orthogonal_ker` + `Submodule.orthogonal_orthogonal`), reduces the condition to
`range σ.op ≤ ker ρ.op`, which by `LinearMap.range_le_ker_iff` is exactly `ρ.op ∘ σ.op = 0`, i.e.
`ρ.op * σ.op = 0`. This is the reusable "orthogonal supports" predicate behind the equality
condition of the entropy-of-a-mixture bound (N&C Theorem 11.10). -/
theorem support_isOrtho_iff_op_mul_eq_zero (ρ σ : State S) :
    ρ.support ⟂ σ.support ↔ ρ.op * σ.op = 0 := by
  rw [Submodule.isOrtho_comm, Submodule.isOrtho_iff_le, State.support_eq_orthogonal_ker ρ,
    Submodule.orthogonal_orthogonal, State.support, LinearMap.range_le_ker_iff,
    ContinuousLinearMap.mul_def, ← ContinuousLinearMap.toLinearMap_comp]
  have hzero : ((0 : S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space) = 0 :=
    ContinuousLinearMap.toLinearMap_zero
  exact ContinuousLinearMap.coe_injective.eq_iff' hzero

end State

end AxQM
