/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Adjoint
public import ToMathlib.Analysis.InnerProductSpace.HSPairing
public import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
public import ToMathlib.Analysis.InnerProductSpace.PiL2
public import ToMathlib.Analysis.InnerProductSpace.Trace

/-!
# Matricization (vectorization) on a tensor product

The vectorization isomorphism `matricize b : E ⊗[𝕜] F ≃ₗ[𝕜] (F →L[𝕜] E)`,
parametrized by an orthonormal basis `b` on the right factor `F`. It reshapes a bipartite
vector `Ψ : E ⊗[𝕜] F` into a continuous linear map by
`matricize b Ψ φ = ∑ k, ⟪b k, φ⟫_𝕜 • restrictRight b k Ψ`. The canonical bridge between
Schmidt decomposition (a "vectorized" state on the bipartite space) and the SVD of an
operator (the same data viewed as a linear map).

The inner product of bipartite vectors equals the **Hilbert–Schmidt** pairing of their
matricizations (`matricize_inner_eq_trace_adjoint_comp`). The map is therefore an
isometry for the HS-norm but a `LinearEquiv` (rather than a `LinearIsometryEquiv`) at
the CLM-with-operator-norm level.

## Main definitions

- `TensorProduct.matricize` : the basis-parametric `LinearEquiv`
  `E ⊗[𝕜] F ≃ₗ[𝕜] (F →L[𝕜] E)`.

## Main results

- `TensorProduct.matricize_apply` / `TensorProduct.matricize_symm_apply` : the
  defining apply forms.
- `TensorProduct.matricize_inner_eq_trace_adjoint_comp` : the Hilbert–Schmidt bridge,
  `⟪Ψ₁, Ψ₂⟫ = trace ((matricize b Ψ₁)† ∘ matricize b Ψ₂)`.
-/

@[expose] public section

/-! ## Orthonormal-basis collapse helpers

Two general lemmas used in the abstract matricize construction below: they package
the basis-orthonormality `δ`-collapse in both inner-product orientations.
(Basis decomposition `∑ ℓ, ⟪b ℓ, φ⟫ • b ℓ = φ` is already in Mathlib as
`OrthonormalBasis.sum_repr'`.) -/

namespace OrthonormalBasis

open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι]
  {𝕜 : Type*} [RCLike 𝕜]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Basis-orthonormality `δ`-collapse (summed-index on the LEFT of the inner product):
`∑ k, ⟪b k, b ℓ⟫_𝕜 • f k = f ℓ`. -/
theorem sum_inner_basis_smul_left {G : Type*} [AddCommMonoid G] [Module 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 F) (f : ι → G) (ℓ : ι) :
    ∑ k, ⟪b k, b ℓ⟫_𝕜 • f k = f ℓ := by
  classical
  rw [Finset.sum_eq_single ℓ (fun k _ hk ↦ by rw [b.inner_eq_ite, ite_eq_right hk, zero_smul])
    (fun h ↦ absurd (Finset.mem_univ ℓ) h), b.inner_eq_ite, ite_eq_left rfl, one_smul]

/-- Basis-orthonormality `δ`-collapse (summed-index on the RIGHT of the inner product):
`∑ k, ⟪b ℓ, b k⟫_𝕜 • f k = f ℓ`. -/
theorem sum_inner_basis_smul_right {G : Type*} [AddCommMonoid G] [Module 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 F) (f : ι → G) (ℓ : ι) :
    ∑ k, ⟪b ℓ, b k⟫_𝕜 • f k = f ℓ := by
  classical
  rw [Finset.sum_eq_single ℓ
    (fun k _ hk ↦ by rw [b.inner_eq_ite, ite_eq_right (Ne.symm hk), zero_smul])
    (fun h ↦ absurd (Finset.mem_univ ℓ) h), b.inner_eq_ite, ite_eq_left rfl, one_smul]

end OrthonormalBasis

/-! ## Matricization on `E ⊗[𝕜] F`

Basis-parametric `LinearEquiv` `E ⊗[𝕜] F ≃ₗ[𝕜] (F →L[𝕜] E)` for inner-product spaces
`E, F` over `RCLike 𝕜` and an orthonormal basis `b` on the right factor `F`.
Finite-dimensionality of `F` is a consequence of carrying a basis indexed by
`[Fintype ι]`, not a declared instance; `E` is unconstrained beyond the inner-product
structure. -/

namespace TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {ι : Type*} [Fintype ι]

open scoped InnerProductSpace

/-- The forward `LinearMap` of `TensorProduct.matricize`. See `matricize` for the bundled
`LinearEquiv` and the math docstring. -/
noncomputable def matricizeToCLM (b : OrthonormalBasis ι 𝕜 F) :
    E ⊗[𝕜] F →ₗ[𝕜] (F →L[𝕜] E) where
  toFun Ψ := ∑ k : ι, (innerSL 𝕜 (b k)).smulRight (LinearMap.restrictRight b k Ψ)
  map_add' Ψ₁ Ψ₂ := by
    ext φ
    simp [ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, Finset.sum_add_distrib, smul_add]
  map_smul' c Ψ := by
    ext φ
    simp [ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, Finset.smul_sum, smul_smul, mul_comm]

@[simp]
theorem matricizeToCLM_apply (b : OrthonormalBasis ι 𝕜 F) (Ψ : E ⊗[𝕜] F) (φ : F) :
    matricizeToCLM b Ψ φ = ∑ k : ι, ⟪b k, φ⟫_𝕜 • LinearMap.restrictRight b k Ψ := by
  simp [matricizeToCLM, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply]

/-- The inverse `LinearMap` of `TensorProduct.matricize`: `T ↦ ∑ k, T (b k) ⊗ₜ b k`. -/
noncomputable def matricizeFromCLM (b : OrthonormalBasis ι 𝕜 F) :
    (F →L[𝕜] E) →ₗ[𝕜] E ⊗[𝕜] F where
  toFun T := ∑ k : ι, T (b k) ⊗ₜ[𝕜] b k
  map_add' T₁ T₂ := by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' c T := by simp [TensorProduct.smul_tmul', Finset.smul_sum]

@[simp]
theorem matricizeFromCLM_apply (b : OrthonormalBasis ι 𝕜 F) (T : F →L[𝕜] E) :
    matricizeFromCLM b T = ∑ k : ι, T (b k) ⊗ₜ[𝕜] b k :=
  rfl

/-- `matricizeToCLM b` post-composed with `matricizeFromCLM b` is the identity on
`F →L[𝕜] E`. The right-inverse half of `TensorProduct.matricize` below. -/
theorem matricizeToCLM_comp_matricizeFromCLM (b : OrthonormalBasis ι 𝕜 F) :
    (matricizeToCLM (E := E) b).comp (matricizeFromCLM b) = LinearMap.id :=
  LinearMap.ext fun T ↦ ContinuousLinearMap.ext fun φ ↦ by
    have inner_collapse : ∀ ℓ, LinearMap.restrictRight b ℓ (∑ k, T (b k) ⊗ₜ[𝕜] b k)
        = T (b ℓ) := fun ℓ ↦ by
      rw [map_sum]
      simp_rw [LinearMap.restrictRight_tmul]
      exact b.sum_inner_basis_smul_right (T ∘ b) ℓ
    simp only [LinearMap.coe_comp, Function.comp_apply, matricizeFromCLM_apply,
      matricizeToCLM_apply, LinearMap.id_coe, id_eq]
    simp_rw [inner_collapse, ← T.map_smul, ← map_sum, b.sum_repr']

/-- `matricizeFromCLM b` post-composed with `matricizeToCLM b` is the identity on
`E ⊗[𝕜] F`. The left-inverse half of `TensorProduct.matricize` below. -/
theorem matricizeFromCLM_comp_matricizeToCLM (b : OrthonormalBasis ι 𝕜 F) :
    (matricizeFromCLM b).comp (matricizeToCLM (E := E) b) = LinearMap.id :=
  LinearMap.ext fun Ψ ↦ by
    simp only [LinearMap.coe_comp, Function.comp_apply, matricizeFromCLM_apply,
      matricizeToCLM_apply, LinearMap.id_coe, id_eq]
    conv_rhs => rw [← LinearMap.sum_embedRight_restrictRight_eq_self b Ψ]
    exact Finset.sum_congr rfl fun k _ ↦ by
      rw [LinearMap.embedRight_apply,
        b.sum_inner_basis_smul_left (LinearMap.restrictRight b · Ψ)]

/-- **Abstract matricization (bra-ket isomorphism)**, basis-parametric on the F-side.
For an orthonormal basis `b : OrthonormalBasis ι 𝕜 F`, this `LinearEquiv` identifies
`Ψ : E ⊗[𝕜] F` with the continuous linear map `F →L[𝕜] E` characterized by

  `matricize b Ψ φ = ∑ k, ⟪b k, φ⟫_𝕜 • restrictRight b k Ψ`,

i.e., the basis-defined bilinear pairing on `F` (the inner product is sesquilinear, but
indexing by the orthonormal basis turns it into a linear pairing on coordinates) applied
slot-by-slot. The inverse sends a CLM `T : F →L[𝕜] E` to the bipartite vector
`∑ k, T (b k) ⊗ₜ b k`.

On the construction route: Riesz is conjugate-linear and not viable; direct bilinear extension via
`ContinuousLinearMap.smulRight` + sum is the chosen route.

cf. `dualTensorHomEquivOfBasis` for the algebraic dual-space analog `M* ⊗ N ≃ M →ₗ N`
on any free module: that variant is `Module.Dual`-based and produces `LinearMap`-valued
output; ours is inner-product / orthonormal-basis-parametric and `ContinuousLinearMap`-
valued, which is what lets Route 2 sidestep the Riesz conjugate-linearity. -/
noncomputable def matricize (b : OrthonormalBasis ι 𝕜 F) :
    E ⊗[𝕜] F ≃ₗ[𝕜] (F →L[𝕜] E) :=
  LinearEquiv.ofLinearMap (matricizeToCLM b) (matricizeFromCLM b)
    (matricizeToCLM_comp_matricizeFromCLM b)
    (matricizeFromCLM_comp_matricizeToCLM b)

@[simp]
theorem matricize_apply (b : OrthonormalBasis ι 𝕜 F) (Ψ : E ⊗[𝕜] F) (φ : F) :
    matricize b Ψ φ = ∑ k : ι, ⟪b k, φ⟫_𝕜 • LinearMap.restrictRight b k Ψ :=
  matricizeToCLM_apply b Ψ φ

/-- Symm-apply form of `TensorProduct.matricize`:
`(matricize b).symm T = ∑ k, T (b k) ⊗ₜ b k`. -/
@[simp]
theorem matricize_symm_apply (b : OrthonormalBasis ι 𝕜 F) (T : F →L[𝕜] E) :
    (matricize b).symm T = ∑ k : ι, T (b k) ⊗ₜ[𝕜] b k :=
  rfl

/-- **Matricize evaluated on a basis vector** equals the right-restriction:
`matricize b Ψ (b k) = restrictRight b k Ψ`. Specialization of `matricize_apply`
with `φ = b k`; the sum on the RHS collapses by orthonormality. -/
@[simp]
theorem matricize_basis_apply (b : OrthonormalBasis ι 𝕜 F) (Ψ : E ⊗[𝕜] F) (k : ι) :
    matricize b Ψ (b k) = LinearMap.restrictRight b k Ψ := by
  rw [matricize_apply, b.sum_inner_basis_smul_left]

/-! ### Adjoint of `matricize` and the Hilbert–Schmidt pairing bridge

Coordinate-form characterization of `(matricize b Ψ).adjoint` and the Hilbert–Schmidt
bridge: the inner product on `E ⊗[𝕜] F` equals the Hilbert–Schmidt pairing of the
matricizations. The adjoint and trace operations require `[CompleteSpace _]`
(CLM-adjoint) and `[FiniteDimensional 𝕜 F]` (trace), so this section declares those
instances. -/

section Adjoint

variable [CompleteSpace E] [CompleteSpace F]

/-- **Coordinate form of `matricize`-adjoint**: the `k`-th basis coefficient of
`(matricize b Ψ).adjoint x` is the inner product of `restrictRight b k Ψ` with `x`.
Direct consequence of `ContinuousLinearMap.adjoint_inner_left` + the apply form
`matricize_apply` evaluated at the basis vector `b k`. -/
theorem matricize_adjoint_apply (b : OrthonormalBasis ι 𝕜 F) (Ψ : E ⊗[𝕜] F)
    (x : E) (k : ι) :
    ⟪b k, (matricize b Ψ).adjoint x⟫_𝕜 = ⟪LinearMap.restrictRight b k Ψ, x⟫_𝕜 := by
  rw [ContinuousLinearMap.adjoint_inner_right, matricize_apply,
    b.sum_inner_basis_smul_left (fun ℓ ↦ LinearMap.restrictRight b ℓ Ψ)]

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- **Hilbert–Schmidt bridge**: the inner product on `E ⊗[𝕜] F` equals the trace
pairing of the matricizations,
`⟪Ψ₁, Ψ₂⟫ = trace ((matricize Ψ₁)† ∘ matricize Ψ₂)`.

Used in the Phase B abstract Uhlmann saturation proof
(`matricize_compose_optimal_eq_*`-style identities) where the inner-product-as-HS-trace
identity is the load-bearing step.

Proof: decompose `Ψ₂ = ∑ k, embedRight b k (restrictRight b k Ψ₂)`, distribute the
inner product through the sum, use `adjoint_embedRight` to turn each
`⟪Ψ₁, embedRight b k _⟫` into `⟪restrictRight b k Ψ₁, _⟫`, then match with
`LinearMap.trace_eq_sum_inner` of the RHS evaluated on the basis. -/
theorem matricize_inner_eq_trace_adjoint_comp (b : OrthonormalBasis ι 𝕜 F)
    (Ψ₁ Ψ₂ : E ⊗[𝕜] F) :
    inner 𝕜 Ψ₁ Ψ₂ = LinearMap.trace 𝕜 _
      ((matricize b Ψ₁).adjoint.toLinearMap ∘ₗ (matricize b Ψ₂).toLinearMap) := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  simp_rw [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
    matricize_basis_apply, matricize_adjoint_apply]
  conv_lhs => rw [← LinearMap.sum_embedRight_restrictRight_eq_self b Ψ₂]
  rw [inner_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by
    rw [← LinearMap.adjoint_inner_left, LinearMap.adjoint_embedRight]

/-- **Matricize-side HS-pairing form** of the bipartite inner product (abstract):
`⟪Ψ₁, Ψ₂⟫ = (matricize Ψ₂).hsPairing (matricize Ψ₁)`. Direct from
`matricize_inner_eq_trace_adjoint_comp` + `ContinuousLinearMap.hsPairing_eq`. -/
theorem matricize_inner_eq_hsPairing (b : OrthonormalBasis ι 𝕜 F) (Ψ₁ Ψ₂ : E ⊗[𝕜] F) :
    inner 𝕜 Ψ₁ Ψ₂ = (matricize b Ψ₂).hsPairing (matricize b Ψ₁) := by
  rw [matricize_inner_eq_trace_adjoint_comp b, ContinuousLinearMap.hsPairing_eq,
    ContinuousLinearMap.toLinearMap_comp]

/-- **Purification identity**: the right-partial-trace of the rank-one self-projection
onto `Ψ` factors as `matricize b Ψ ∘ (matricize b Ψ)†`, basis-parametric on `b`.

Structural identity behind the purification construction: the reduced density matrix
on the first factor of a bipartite pure state is the outer-product expansion of the
columns of the matricization. -/
theorem partialTraceRight_rankOne_self (b : OrthonormalBasis ι 𝕜 F) (Ψ : E ⊗[𝕜] F) :
    LinearMap.partialTraceRight b ((InnerProductSpace.rankOne 𝕜 Ψ Ψ).toLinearMap) =
      ((matricize b Ψ).comp (matricize b Ψ).adjoint).toLinearMap := by
  ext x
  simp only [LinearMap.partialTraceRight_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, LinearMap.map_smul,
    Function.comp_apply, ContinuousLinearMap.coe_comp, matricize_apply,
    matricize_adjoint_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← LinearMap.embedRight_apply b, ← LinearMap.adjoint_inner_left,
    LinearMap.adjoint_embedRight]

end Adjoint

end TensorProduct
