/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.PiTensorProduct
public import ToMathlib.Analysis.InnerProductSpace.Positive
public import ToMathlib.Analysis.InnerProductSpace.Spectrum
public import ToMathlib.Analysis.InnerProductSpace.TensorProduct
public import ToMathlib.LinearAlgebra.Matrix.Trace
public import ToMathlib.LinearAlgebra.TensorPower.Endomorphism
public import ToMathlib.LinearAlgebra.Trace

/-!

# Tensor power and binary tensor map of endomorphisms on inner product spaces

For `A : E →ₗ[𝕜] E` an endomorphism of a finite-dimensional inner product space, this
file establishes the eigenvalue/positivity structure of n-fold tensor powers and binary
tensor maps.

## n-fold tensor power:

* `LinearMap.tensorPow_adjoint`: `(A ^⊗ n)† = (A†) ^⊗ n` — the adjoint of an n-fold tensor
  power is the n-fold tensor power of the adjoint.
* `IsSelfAdjoint.tensorPow`: `IsSelfAdjoint A → IsSelfAdjoint (A ^⊗ n)`.
* `LinearMap.IsSymmetric.tensorPow`: the LinearMap-level symmetric counterpart.
* `LinearMap.trace_tensorPow`: `trace (A ^⊗ n) = (trace A) ^ n`.
* `LinearMap.IsSymmetric.tensorPow_eigenvalues_multiset_eq`: the multiset of eigenvalues
  of `A ^⊗ n` equals the multiset of products `∏ i, A.eigenvalues hd (κ i)` over
  `κ : Fin n → Fin d`.
* `LinearMap.IsPositive.tensorPow`: an n-fold tensor power preserves positivity.

## Binary tensor map (`TensorProduct.map A B`):

* `LinearMap.IsSymmetric.tensorMap_eigenvalues_multiset_eq`: the multiset of eigenvalues of
  `TensorProduct.map A B` equals the multiset of products `μA i * μB j`.
* `LinearMap.IsPositive.tensorMap`: a binary tensor map preserves positivity.

-/

@[expose] public section

open scoped TensorProduct
open Module

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

namespace PiTensorProduct

/-- The n-fold tensor power of a finite-dimensional space is finite-dimensional. -/
instance instFiniteDimensional_tensorPow (n : ℕ) :
    FiniteDimensional 𝕜 ((⨂[𝕜]^n) E) :=
  Module.Finite.of_basis (Basis.piTensorProduct fun _ : Fin n ↦ Module.finBasis 𝕜 E)

end PiTensorProduct

namespace LinearMap

/-- The adjoint of the n-fold tensor power of `A` is the n-fold tensor power of the
adjoint of `A`. -/
theorem tensorPow_adjoint (A : E →ₗ[𝕜] E) (n : ℕ) :
    (A ^⊗ n).adjoint = A.adjoint ^⊗ n := by
  rw [eq_comm, LinearMap.eq_adjoint_iff]
  intro x y
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' b =>
      simp only [tensorPow_apply_tprod, map_smul, inner_smul_left, inner_smul_right,
        PiTensorProduct.inner_tprod_tprod]
      simp_rw [LinearMap.adjoint_inner_left]
    | add u v hu hv =>
      simp only [map_add, inner_add_right, hu, hv]
  | add u v hu hv =>
    simp only [map_add, inner_add_left, hu, hv]

/-- An n-fold tensor power preserves the symmetry of a `LinearMap`: if `A.IsSymmetric`,
so is `A ^⊗ n`. -/
theorem IsSymmetric.tensorPow {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (n : ℕ) :
    (A ^⊗ n).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint] at hA ⊢
  rw [LinearMap.isSelfAdjoint_iff'] at hA ⊢
  rw [LinearMap.tensorPow_adjoint, hA]

end LinearMap

namespace IsSelfAdjoint

/-- An n-fold tensor power preserves self-adjointness: if `A` is self-adjoint, so is
`A ^⊗ n`. -/
theorem tensorPow {A : E →ₗ[𝕜] E} (hA : IsSelfAdjoint A) (n : ℕ) :
    IsSelfAdjoint (A ^⊗ n) := by
  rw [LinearMap.isSelfAdjoint_iff'] at hA ⊢
  rw [LinearMap.tensorPow_adjoint, hA]

end IsSelfAdjoint

namespace LinearMap

/-- The trace of the n-fold tensor power of `A` is the n-th power of the trace of `A`. -/
theorem trace_tensorPow (A : E →ₗ[𝕜] E) (n : ℕ) :
    LinearMap.trace 𝕜 _ (A ^⊗ n) = (LinearMap.trace 𝕜 _ A) ^ n := by
  classical
  let b : Basis (Fin (finrank 𝕜 E)) 𝕜 E := Module.finBasis 𝕜 E
  rw [LinearMap.trace_eq_matrix_trace 𝕜 (Basis.piTensorProduct (fun _ : Fin n ↦ b)),
    Matrix.trace_apply, LinearMap.trace_eq_matrix_trace 𝕜 b, Matrix.trace_apply]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply,
    tensorPow_apply_tprod, Basis.piTensorProduct_repr_tprod_apply]
  rw [Finset.sum_pow', Fintype.piFinset_univ]

/-- **Eigenvalues of an n-fold tensor power**: the multiset of eigenvalues of `A ^⊗ n`
(for symmetric `A`) equals the multiset of products `∏ i, A.eigenvalues hd (κ i)` over
`κ : Fin n → Fin d`, where `d = finrank 𝕜 E`. -/
theorem IsSymmetric.tensorPow_eigenvalues_multiset_eq
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {d N : ℕ} (n : ℕ)
    (hd : finrank 𝕜 E = d) (hN : finrank 𝕜 ((⨂[𝕜]^n) E) = N) :
    Multiset.map (fun κ : Fin n → Fin d ↦ ∏ i, hA.eigenvalues hd (κ i)) Finset.univ.val =
      Multiset.map ((hA.tensorPow n).eigenvalues hN) Finset.univ.val := by
  classical
  let b : Basis (Fin n → Fin d) 𝕜 ((⨂[𝕜]^n) E) :=
    Basis.piTensorProduct (fun _ : Fin n ↦ (hA.eigenvectorBasis hd).toBasis)
  refine (hA.tensorPow n).eigenvalues_multiset_map_eq_of_eigenbasis hN b (μ := _) (fun κ ↦ ?_)
  simp only [b, Basis.piTensorProduct_apply, OrthonormalBasis.coe_toBasis,
    tensorPow_apply_tprod, hA.apply_eigenvectorBasis,
    MultilinearMap.map_smul_univ (PiTensorProduct.tprod 𝕜), RCLike.ofReal_prod, RingHom.id_apply]

/-- An n-fold tensor power preserves positivity: if `A.IsPositive`, so is `A ^⊗ n`. -/
theorem IsPositive.tensorPow {A : E →ₗ[𝕜] E} (hA : A.IsPositive) (n : ℕ) :
    (A ^⊗ n).IsPositive := by
  refine (hA.isSymmetric.tensorPow n).isPositive_of_eigenvalues_nonneg rfl fun j ↦ ?_
  have hmem := Multiset.mem_map_of_mem
    ((hA.isSymmetric.tensorPow n).eigenvalues rfl) (Finset.mem_univ_val j)
  rw [← hA.isSymmetric.tensorPow_eigenvalues_multiset_eq n rfl rfl] at hmem
  obtain ⟨κ, _, hκ⟩ := Multiset.mem_map.mp hmem
  exact hκ ▸ Finset.prod_nonneg fun i _ ↦ hA.nonneg_eigenvalues rfl (κ i)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Joint-eigenvector identity for `TensorProduct.map`**: on the pure tensor
`hA.eigenvectorBasis i ⊗ₜ hB.eigenvectorBasis j`, the operator `TensorProduct.map A B`
acts as scalar multiplication by `μA i * μB j`. -/
theorem IsSymmetric.tensorMap_apply_eigenvectorBasis_smul
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {B : F →ₗ[𝕜] F} (hB : B.IsSymmetric)
    {dE dF : ℕ} (hdE : finrank 𝕜 E = dE) (hdF : finrank 𝕜 F = dF) (i : Fin dE) (j : Fin dF) :
    TensorProduct.map A B (hA.eigenvectorBasis hdE i ⊗ₜ[𝕜] hB.eigenvectorBasis hdF j) =
      ((hA.eigenvalues hdE i * hB.eigenvalues hdF j : ℝ) : 𝕜) •
        (hA.eigenvectorBasis hdE i ⊗ₜ[𝕜] hB.eigenvectorBasis hdF j) := by
  rw [TensorProduct.map_tmul, hA.apply_eigenvectorBasis, hB.apply_eigenvectorBasis,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← mul_smul]
  push_cast
  ring_nf

/-- **Eigenvalues of a binary tensor product map**: the multiset of eigenvalues of
`TensorProduct.map A B` (for symmetric `A, B`) equals the multiset of products
`μA i * μB j` over `(i, j) : Fin dE × Fin dF`. Binary analog of
`LinearMap.IsSymmetric.tensorPow_eigenvalues_multiset_eq`. -/
theorem IsSymmetric.tensorMap_eigenvalues_multiset_eq
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {B : F →ₗ[𝕜] F} (hB : B.IsSymmetric)
    {dE dF N : ℕ}
    (hdE : finrank 𝕜 E = dE) (hdF : finrank 𝕜 F = dF)
    (hN : finrank 𝕜 (E ⊗[𝕜] F) = N) :
    Multiset.map (fun ij : Fin dE × Fin dF ↦ hA.eigenvalues hdE ij.1 * hB.eigenvalues hdF ij.2)
        Finset.univ.val =
      Multiset.map ((LinearMap.IsSymmetric.tensorMap hA hB).eigenvalues hN) Finset.univ.val := by
  classical
  let b : Basis (Fin dE × Fin dF) 𝕜 (E ⊗[𝕜] F) :=
    (hA.eigenvectorBasis hdE).toBasis.tensorProduct (hB.eigenvectorBasis hdF).toBasis
  refine (LinearMap.IsSymmetric.tensorMap hA hB).eigenvalues_multiset_map_eq_of_eigenbasis
    hN b (μ := _) (fun ⟨i, j⟩ ↦ ?_)
  simp only [b, Basis.tensorProduct_apply, OrthonormalBasis.coe_toBasis]
  exact LinearMap.IsSymmetric.tensorMap_apply_eigenvectorBasis_smul hA hB hdE hdF i j

/-- A binary tensor product map has strictly positive eigenvalues if both factors do. The
multiset identity supplies the joint-eigenvalue structure. -/
theorem IsSymmetric.tensorMap_eigenvalues_pos
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {B : F →ₗ[𝕜] F} (hB : B.IsSymmetric)
    {dE dF N : ℕ}
    (hdE : finrank 𝕜 E = dE) (hdF : finrank 𝕜 F = dF)
    (hN : finrank 𝕜 (E ⊗[𝕜] F) = N)
    (hA_pos : ∀ i, 0 < hA.eigenvalues hdE i) (hB_pos : ∀ j, 0 < hB.eigenvalues hdF j)
    (k : Fin N) : 0 < (LinearMap.IsSymmetric.tensorMap hA hB).eigenvalues hN k := by
  have hmem := Multiset.mem_map_of_mem
    ((LinearMap.IsSymmetric.tensorMap hA hB).eigenvalues hN) (Finset.mem_univ_val k)
  rw [← LinearMap.IsSymmetric.tensorMap_eigenvalues_multiset_eq hA hB hdE hdF hN] at hmem
  obtain ⟨⟨i, j⟩, _, hij⟩ := Multiset.mem_map.mp hmem
  exact hij ▸ mul_pos (hA_pos i) (hB_pos j)

end LinearMap
