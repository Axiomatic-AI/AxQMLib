/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! ### Simultaneous diagonalization by a common orthonormal basis

The internal-direct-sum results of `Mathlib.Analysis.InnerProductSpace.JointEigenspace` are
repackaged here in the form usually quoted in physics (Nielsen & Chuang, *Quantum Computation
and Quantum Information*, Theorem 2.2): two symmetric operators commute if and only if they are
diagonal in a common orthonormal basis, i.e. share an orthonormal basis of eigenvectors. This is
generalized to a finite pairwise-commuting family of symmetric operators sharing a single
orthonormal eigenbasis.
-/

@[expose] public section

namespace Module.End

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If every vector of a basis `b` is an eigenvector of both endomorphisms `f` and `g` — that is,
if `f` and `g` are simultaneously diagonal in `b` — then `f` and `g` commute. This is the easy
direction of the simultaneous diagonalization theorem, and holds over any commutative ring with no
extra structure. -/
theorem commute_of_forall_apply_basis_eq_smul {f g : Module.End R M} (b : Module.Basis ι R M)
    (hf : ∀ i, ∃ μ : R, f (b i) = μ • b i) (hg : ∀ i, ∃ ν : R, g (b i) = ν • b i) :
    Commute f g := by
  refine b.ext fun i => ?_
  obtain ⟨μ, hμ⟩ := hf i
  obtain ⟨ν, hν⟩ := hg i
  simp only [mul_apply_eq_comp, hμ, hν, map_smul, smul_smul, mul_comm]

end Module.End

namespace LinearMap.IsSymmetric

open Module.End Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}

/-- **Simultaneous diagonalization, existence half.** Two commuting symmetric operators on a
finite-dimensional inner product space share an orthonormal eigenbasis: there is an orthonormal
basis `b` and scalar functions `μ ν` with `A (b i) = μ i • b i` and `B (b i) = ν i • b i` for all
`i` — a basis with respect to which both `A` and `B` are diagonal.

The joint eigenspaces `eigenspace A i.2 ⊓ eigenspace B i.1` form an orthogonal family
(`orthogonalFamily_eigenspace_inf_eigenspace`) and span the whole space
(`iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute`). Reindexing along the *actual* eigenvalue
pairs `Eigenvalues B × Eigenvalues A` (a finite type) makes the index a `Fintype`, so
`subordinateOrthonormalBasis` collects an orthonormal basis subordinate to that decomposition; each
of its vectors lies in a single joint eigenspace, hence is a common eigenvector of `A` and `B`.

This is the shared construction behind the spectral theorem for normal operators
(`IsStarNormal.exists_orthonormalBasis_forall_apply_eq_smul`) and the simultaneous diagonalization
theorem `commute_iff_exists_orthonormalBasis_forall_apply_eq_smul` below. -/
theorem exists_orthonormalBasis_forall_apply_eq_smul_of_commute
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
      (μ ν : Fin (Module.finrank 𝕜 E) → 𝕜), ∀ i, A (b i) = μ i • b i ∧ B (b i) = ν i • b i := by
  classical
  -- The joint eigenspaces of `A` and `B` form an orthogonal family and span the whole space.
  set V : 𝕜 × 𝕜 → Submodule 𝕜 E := fun i => eigenspace A i.2 ⊓ eigenspace B i.1 with hVdef
  have hof : OrthogonalFamily 𝕜 (fun i => (V i)) (fun i => (V i).subtypeₗᵢ) :=
    orthogonalFamily_eigenspace_inf_eigenspace hA hB
  -- Reindex along the (finite) set of eigenvalue pairs so that the index type is a `Fintype`.
  set f : Eigenvalues B × Eigenvalues A → 𝕜 × 𝕜 := fun q => (q.1, q.2) with hfdef
  have hf : Function.Injective f := by
    rintro ⟨b1, a1⟩ ⟨b2, a2⟩ h
    simp only [hfdef, Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
  have hof' := hof.comp hf
  have hspan : ⨆ q, V (f q) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hA hB hAB]
    refine iSup_le fun α => iSup_le fun γ => ?_
    by_cases h : eigenspace A α ⊓ eigenspace B γ = ⊥
    · rw [h]; exact bot_le
    · have hα : eigenspace A α ≠ ⊥ := fun he => h (by rw [he, bot_inf_eq])
      have hγ : eigenspace B γ ≠ ⊥ := fun he => h (by rw [he, inf_bot_eq])
      exact le_iSup (fun q => V (f q)) (⟨γ, hγ⟩, ⟨α, hα⟩)
  have hInt : DirectSum.IsInternal (fun q => V (f q)) := by
    rw [hof'.isInternal_iff, hspan]
    exact Submodule.top_orthogonal_eq_bot
  -- A subordinate orthonormal basis consists of common eigenvectors of `A` and `B`.
  refine ⟨hInt.subordinateOrthonormalBasis rfl hof',
    fun i => ((hInt.subordinateOrthonormalBasisIndex rfl i hof').2 : 𝕜),
    fun i => ((hInt.subordinateOrthonormalBasisIndex rfl i hof').1 : 𝕜), fun i => ?_⟩
  have hmem := hInt.subordinateOrthonormalBasis_subordinate rfl i hof'
  simp only [hVdef, hfdef, Submodule.mem_inf, Module.End.mem_eigenspace_iff] at hmem
  exact hmem

/-- **Simultaneous diagonalization theorem** (Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Theorem 2.2). Two symmetric operators `A` and `B` on a finite-dimensional inner
product space commute if and only if there is an orthonormal basis of common eigenvectors — an
orthonormal basis with respect to which both `A` and `B` are diagonal. (Over `𝕜 = ℂ`, `IsSymmetric`
is Hermiticity, recovering the textbook statement.) -/
theorem commute_iff_exists_orthonormalBasis_forall_apply_eq_smul
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    Commute A B ↔ ∃ b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E,
      (∀ i, ∃ μ : 𝕜, A (b i) = μ • b i) ∧ ∀ i, ∃ ν : 𝕜, B (b i) = ν • b i :=
  ⟨fun hAB => by
    obtain ⟨b, μ, ν, h⟩ := exists_orthonormalBasis_forall_apply_eq_smul_of_commute hA hB hAB
    exact ⟨b, fun i => ⟨μ i, (h i).1⟩, fun i => ⟨ν i, (h i).2⟩⟩,
   fun ⟨b, hbA, hbB⟩ =>
    Module.End.commute_of_forall_apply_basis_eq_smul b.toBasis
      (fun i => by simpa only [OrthonormalBasis.coe_toBasis] using hbA i)
      (fun i => by simpa only [OrthonormalBasis.coe_toBasis] using hbB i)⟩

/-- **Simultaneous diagonalization for a commuting family, existence half** — the `n`-operator
generalization of `exists_orthonormalBasis_forall_apply_eq_smul_of_commute`. A finite family `T` of
pairwise-commuting symmetric operators on a finite-dimensional inner product space shares an
orthonormal eigenbasis: there is an orthonormal basis `b` and scalar functions `μ` with
`T j (b i) = μ j i • b i` for every operator index `j` and basis index `i` — a single basis with
respect to which every `T j` is diagonal.

The joint eigenspaces `⨅ j, eigenspace (T j) (χ j)` form an orthogonal family
(`orthogonalFamily_iInf_eigenspaces`) and span the whole space (`iSup_iInf_eq_top_of_commute`).
Reindexing along the *actual* eigenvalue tuples `∀ j, Eigenvalues (T j)` (a finite type) makes the
index a `Fintype`, so `subordinateOrthonormalBasis` collects an orthonormal basis subordinate to
that decomposition; each of its vectors lies in a single joint eigenspace, hence is a common
eigenvector of every `T j`. -/
theorem exists_orthonormalBasis_forall_apply_eq_smul_of_pairwise_commute
    {ι : Type*} [Finite ι] {T : ι → E →ₗ[𝕜] E}
    (hT : ∀ j, (T j).IsSymmetric) (hC : Pairwise (Function.onFun Commute T)) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
      (μ : ι → Fin (Module.finrank 𝕜 E) → 𝕜), ∀ j i, T j (b i) = μ j i • b i := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set V : (ι → 𝕜) → Submodule 𝕜 E := fun χ => ⨅ j, eigenspace (T j) (χ j) with hVdef
  have hof : OrthogonalFamily 𝕜 (fun χ => (V χ)) (fun χ => (V χ).subtypeₗᵢ) :=
    orthogonalFamily_iInf_eigenspaces hT
  -- Reindex the joint eigenspaces along the *actual* eigenvalue tuples, a `Fintype`.
  set f : (∀ j, Eigenvalues (T j)) → (ι → 𝕜) := fun q j => (q j : 𝕜) with hfdef
  have hf : Function.Injective f := fun q1 q2 h => funext fun j => Subtype.ext (congrFun h j)
  have hof' := hof.comp hf
  have hspan : ⨆ q, V (f q) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← iSup_iInf_eq_top_of_commute hT hC]
    refine iSup_le fun χ => ?_
    by_cases h : (⨅ j, eigenspace (T j) (χ j)) = ⊥
    · rw [h]; exact bot_le
    · -- a nonzero joint eigenspace forces each coordinate `χ j` to be an eigenvalue of `T j`
      have hqj : ∀ j, HasEigenvalue (T j) (χ j) := fun j => by
        rw [hasEigenvalue_iff]
        exact fun he => h (le_bot_iff.mp ((iInf_le _ j).trans he.le))
      exact le_iSup (fun q => V (f q)) (fun j => ⟨χ j, hqj j⟩)
  have hInt : DirectSum.IsInternal (fun q => V (f q)) := by
    rw [hof'.isInternal_iff, hspan]; exact Submodule.top_orthogonal_eq_bot
  refine ⟨hInt.subordinateOrthonormalBasis rfl hof',
    fun j i => ((hInt.subordinateOrthonormalBasisIndex rfl i hof') j : 𝕜), fun j i => ?_⟩
  have hmem := hInt.subordinateOrthonormalBasis_subordinate rfl i hof'
  simp only [hVdef, hfdef, Submodule.mem_iInf, mem_eigenspace_iff] at hmem
  exact hmem j

end LinearMap.IsSymmetric
