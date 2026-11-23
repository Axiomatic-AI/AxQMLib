/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Entropy

/-!
# AxQM — the spectral characterization of the von Neumann entropy

Nielsen–Chuang open §11.3 with the defining identity for the von Neumann entropy: writing a density
operator in its spectral (eigen-) decomposition `ρ = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|`, the entropy is the *Shannon
entropy of the eigenvalue spectrum*,

`S(ρ) = H(λ₁, …, λ_d) = -∑ᵢ λᵢ log λᵢ`.

The entropy `State.vonNeumannEntropy` is *defined* through
`ContinuousLinearMap.vonNeumannEntropy`, whose value on a self-adjoint operator is precisely the
Shannon entropy of its *canonical* eigenvalue sequence (`vonNeumannEntropy_of_isSymmetric`). This
file records the more flexible **any-eigenbasis** form: if `b` is *any* orthonormal basis
diagonalizing `ρ.op` with real eigenvalues `μ`, then `S(ρ) = H(μ)`. One is rarely handed the
Mathlib-canonical spectral order; concrete situations (Schmidt decompositions, block-diagonal
mixtures, explicit qubit states) come with their *own* diagonalizing basis, and this lemma lets one
compute the entropy directly from it.

This is the analytic engine behind the substantive parts of Nielsen–Chuang Theorem 11.8 (the
equality `S(A) = S(B)` for a pure composite, the orthogonal-support mixture identity, and the joint
entropy theorem), all of which reduce a von Neumann entropy to the Shannon entropy of a spectrum
presented in a task-specific eigenbasis.

## Main results

* `AxQM.State.vonNeumannEntropy_eq_entropy_of_isEigenbasis` — `S(ρ) = H(μ)` whenever the
  orthonormal basis `b` diagonalizes `ρ.op` with real eigenvalue sequence `μ`.
* `AxQM.State.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum` — `S(ρ) = H(w)`
  whenever `ρ.op = ∑ᵢ wᵢ |eᵢ⟩⟨eᵢ|` for an orthonormal (possibly *incomplete*) family `e`. This is
  the workhorse for the spectral parts of Theorem 11.8: a task-specific eigenbasis (Schmidt bases,
  block-diagonal mixtures) rarely spans the whole space, and this lemma reads the entropy off the
  finite weight list directly — the extra `0` eigenvalues on the orthogonal complement contribute
  nothing (`η(0) = 0`).
* `AxQM.State.vonNeumannEntropy_eq_entropy_of_rankOne_sum_orthonormal_on_ne_zero` — the
  same conclusion `S(ρ) = H(w)` requiring the family `e` orthonormal only on the **non-zero-weight**
  indices `{i : wᵢ ≠ 0}`. The zero-weight rank-one terms vanish and may overlap freely; this is what
  the orthogonal-support mixture identity (Theorem 11.8 part 4) needs, since the assembled
  eigenfamily of a mixture is orthonormal only across the summands' supports.
-/

namespace AxQM

open scoped InnerProductSpace

variable {S : QSystem} {ι : Type*} [Fintype ι]

/-- **Spectral characterization of the von Neumann entropy** (Nielsen–Chuang §11.3): for *any*
orthonormal basis `b` diagonalizing the density operator `ρ.op` with real eigenvalues `μ`
(`ρ.op (b i) = μ i • b i`), the entropy is the Shannon entropy of that eigenvalue spectrum,
`S(ρ) = H(μ)`.

The proof feeds the given eigenbasis into the eigenvalue-recognition theorem
(`LinearMap.IsSymmetric.eigenvalues_multiset_map_eq_of_eigenbasis`): the multiset of `μ` agrees with
the multiset of `ρ.op`'s canonical eigenvalues, and Shannon entropy depends only on that multiset
(`Real.entropy_eq_of_multiset_map_eq`), so it agrees with the canonical value computed by
`ContinuousLinearMap.vonNeumannEntropy_of_isSymmetric`. -/
theorem State.vonNeumannEntropy_eq_entropy_of_isEigenbasis (ρ : State S)
    (b : OrthonormalBasis ι ℂ S.space) {μ : ι → ℝ}
    (h : ∀ i, ρ.op (b i) = (μ i : ℂ) • b i) :
    ρ.vonNeumannEntropy = Real.entropy μ := by
  have hsym : ρ.op.toLinearMap.IsSymmetric := ρ.isDensity.isSymmetric
  have hfin : Module.finrank ℂ S.space = Fintype.card ι := Module.finrank_eq_card_basis b.toBasis
  have heigen : ∀ i, ρ.op.toLinearMap (b.toBasis i) = (μ i : ℂ) • b.toBasis i := by
    intro i; rw [b.coe_toBasis]; exact h i
  have hrec := hsym.eigenvalues_multiset_map_eq_of_eigenbasis hfin b.toBasis heigen
  rw [State.vonNeumannEntropy_def,
    ContinuousLinearMap.vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq hsym hfin]
  exact Real.entropy_eq_of_multiset_map_eq hrec.symm

/-- **Extend an orthonormal rank-one eigenfamily to a full diagonalizing basis.** If the density
operator `ρ.op` is a weighted sum of rank-one projectors onto an *orthonormal* family
`e : ι → S.space` — `ρ.op = ∑ᵢ wᵢ |eᵢ⟩⟨eᵢ|` — then `e`, which need not span `S.space`, extends to a
full orthonormal basis `B` of `S.space` indexed by `ι ⊕ Fin (finrank (span e)ᗮ)` that diagonalizes
`ρ.op` with the real eigenvalue family `Sum.elim w 0`: on the `ι` block each `eᵢ` is an eigenvector
with eigenvalue `wᵢ` (orthonormality kills the cross terms), and the adjoined complement block — an
orthonormal basis `c` of `(span e)ᗮ` — lies in the kernel of every `|eᵢ⟩⟨eᵢ|`, so each `cⱼ` is an
eigenvector with eigenvalue `0`.

The shared construction behind both spectral read-offs of such a decomposition — the entropy
`S(ρ) = H(w)` (`State.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum`) and the
same-non-zero spectrum `w ≅ λ_ρ` (`State.sameNonzero_eigenvalueDist_of_orthonormal_rankOne_sum`) —
which differ only in the recognition lemma applied to the returned eigenbasis. -/
theorem State.exists_eigenbasis_of_orthonormal_rankOne_sum (ρ : State S) {e : ι → S.space}
    (he : Orthonormal ℂ e) (w : ι → ℝ)
    (hop : ρ.op = ∑ i, (w i : ℂ) • (InnerProductSpace.rankOne ℂ (e i)) (e i)) :
    ∃ B : OrthonormalBasis (ι ⊕ Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range e))ᗮ)) ℂ S.space,
      ∀ x, ρ.op (B x) = ((Sum.elim w (fun _ => (0 : ℝ)) x : ℝ) : ℂ) • B x := by
  classical
  set U : Submodule ℂ S.space := Submodule.span ℂ (Set.range e) with hUdef
  set c : OrthonormalBasis (Fin (Module.finrank ℂ Uᗮ)) ℂ Uᗮ := stdOrthonormalBasis ℂ Uᗮ
  set c' : Fin (Module.finrank ℂ Uᗮ) → S.space := fun j => (c j : S.space) with hc'
  -- Membership facts anchoring the two blocks of the extended basis.
  have hmem_e : ∀ i, e i ∈ U := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hmem_c' : ∀ j, c' j ∈ Uᗮ := fun j => Submodule.coe_mem (c j)
  -- The action of `ρ.op` on any vector, unfolded through the rank-one sum.
  have key : ∀ x : S.space, ρ.op x = ∑ i, ((w i : ℂ) * inner ℂ (e i) x) • e i := by
    intro x
    rw [hop, sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_apply, InnerProductSpace.rankOne_apply, smul_smul]
  -- Block 1: each `eᵢ` is an eigenvector with eigenvalue `wᵢ`.
  have hdiag_e : ∀ i, ρ.op (e i) = (w i : ℂ) • e i := by
    intro i
    rw [key, Finset.sum_eq_single i]
    · rw [orthonormal_iff_ite.mp he i i]; simp
    · intro j _ hji
      rw [orthonormal_iff_ite.mp he j i, ite_eq_right hji, mul_zero, zero_smul]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- Block 2: each complement vector is an eigenvector with eigenvalue `0`.
  have hdiag_c' : ∀ j, ρ.op (c' j) = 0 := by
    intro j
    rw [key]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Submodule.inner_right_of_mem_orthogonal (hmem_e i) (hmem_c' j), mul_zero, zero_smul]
  -- The combined family is orthonormal.
  have hgon : Orthonormal ℂ (Sum.elim e c') := by
    rw [orthonormal_iff_ite]
    rintro (i | j) (i' | j') <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq, ite_false]
    · exact orthonormal_iff_ite.mp he i i'
    · exact Submodule.inner_right_of_mem_orthogonal (hmem_e i) (hmem_c' j')
    · exact Submodule.inner_left_of_mem_orthogonal (hmem_e i') (hmem_c' j)
    · rw [hc']; exact orthonormal_iff_ite.mp c.orthonormal j j'
  -- The combined family spans the whole space, so its complement is trivial.
  have hspan : (Submodule.span ℂ (Set.range (Sum.elim e c')))ᗮ = ⊥ := by
    rw [Submodule.orthogonal_eq_bot_iff, Set.Sum.elim_range, Submodule.span_union, ← hUdef]
    have hcspan : Submodule.span ℂ (Set.range (⇑c)) = ⊤ := by
      rw [← OrthonormalBasis.coe_toBasis]; exact c.toBasis.span_eq
    have hc'span : Submodule.span ℂ (Set.range c') = Uᗮ := by
      rw [hc', show (fun j => (c j : S.space)) = Uᗮ.subtype ∘ c from rfl, Set.range_comp,
        Submodule.span_image, hcspan, Submodule.map_subtype_top]
    rw [hc'span]
    exact Submodule.sup_orthogonal_of_hasOrthogonalProjection
  -- Assemble the extended orthonormal basis and read off the diagonal action.
  set B : OrthonormalBasis (ι ⊕ Fin (Module.finrank ℂ Uᗮ)) ℂ S.space :=
    OrthonormalBasis.mkOfOrthogonalEqBot hgon hspan
  have hBcoe : ⇑B = Sum.elim e c' := OrthonormalBasis.coe_of_orthogonal_eq_bot_mk hgon hspan
  refine ⟨B, fun x => ?_⟩
  rw [hBcoe]
  cases x with
  | inl i => simpa using hdiag_e i
  | inr j => simp [hdiag_c' j]

/-- **Entropy from an orthonormal eigenfamily** (Nielsen–Chuang §11.3, spectral workhorse). If the
density operator `ρ.op` is a weighted sum of rank-one projectors onto an *orthonormal* family
`e : ι → S.space` — `ρ.op = ∑ᵢ wᵢ |eᵢ⟩⟨eᵢ|` — then the von Neumann entropy is the Shannon entropy of
the weight list, `S(ρ) = H(w)`.

The family `e` need not span `S.space`: `State.exists_eigenbasis_of_orthonormal_rankOne_sum` extends
it to a full eigenbasis `B` with eigenvalue family `Sum.elim w 0` (the complement vectors carry
eigenvalue `0`). Feeding `B` into `State.vonNeumannEntropy_eq_entropy_of_isEigenbasis` gives
`S(ρ) = H(w ⊕ 0) = H(w)`, since the padded `0` eigenvalues contribute `η(0) = 0` to the Shannon
sum. -/
theorem State.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum (ρ : State S)
    {e : ι → S.space} (he : Orthonormal ℂ e) (w : ι → ℝ)
    (hop : ρ.op = ∑ i, (w i : ℂ) • (InnerProductSpace.rankOne ℂ (e i)) (e i)) :
    ρ.vonNeumannEntropy = Real.entropy w := by
  obtain ⟨B, hdiag⟩ := ρ.exists_eigenbasis_of_orthonormal_rankOne_sum he w hop
  rw [ρ.vonNeumannEntropy_eq_entropy_of_isEigenbasis B hdiag, Real.entropy_eq, Real.entropy_eq,
    Fintype.sum_sum_type]
  simp [Real.negMulLog_zero]

/-- **Dropping the zero-weight terms of a finite sum.** If `g i = 0` whenever `w i = 0`, then the
sum of `g` over the whole index type equals the sum over the sub-type of indices with non-zero
weight. Used to reduce a rank-one/entropy sum with a possibly-degenerate weight list to the
non-degenerate sub-family. A thin specialisation of the lemma `Finset.sum_congr_set` to the
support set `{i | w i ≠ 0}`. -/
private theorem sum_eq_sum_subtype_ne_zero {α M : Type*} [Fintype α] [AddCommMonoid M]
    (w : α → ℝ) (g : α → M) (hg : ∀ i, w i = 0 → g i = 0) :
    ∑ i, g i = ∑ i : {i : α // w i ≠ 0}, g i.1 := by
  classical
  exact Finset.sum_congr_set {i | w i ≠ 0} g (fun i => g i.1) (fun _ _ => rfl)
    (fun x hx => hg x (not_not.mp hx))

/-- **Entropy from a rank-one family orthonormal on its support** (the degenerate-weight
strengthening of `State.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum`). If
`ρ.op = ∑ᵢ wᵢ |eᵢ⟩⟨eᵢ|` and the sub-family `{eᵢ : wᵢ ≠ 0}` — the vectors carrying non-zero weight —
is orthonormal, then `S(ρ) = H(w)`. The family `e` need *not* be orthonormal on the zero-weight
indices: those rank-one terms vanish (`0 • x = 0`) and contribute `η(0) = 0` to the Shannon sum, so
they may be discarded before invoking the orthonormal engine.

This is the workhorse for the *orthogonal-support mixture* identity (Nielsen–Chuang Theorem 11.8,
part 4): the eigenvectors of the summands `ρᵢ` assemble into a rank-one decomposition of the mixture
whose full index family is orthonormal only on the support (the non-zero eigenvalues), precisely
because distinct summands have orthogonal supports. -/
theorem State.vonNeumannEntropy_eq_entropy_of_rankOne_sum_orthonormal_on_ne_zero
    (ρ : State S) {e : ι → S.space} (w : ι → ℝ)
    (he : Orthonormal ℂ (fun i : {i : ι // w i ≠ 0} => e i.1))
    (hop : ρ.op = ∑ i, (w i : ℂ) • (InnerProductSpace.rankOne ℂ (e i)) (e i)) :
    ρ.vonNeumannEntropy = Real.entropy w := by
  have hop' : ρ.op = ∑ i : {i : ι // w i ≠ 0},
      (w i.1 : ℂ) • (InnerProductSpace.rankOne ℂ (e i.1)) (e i.1) := by
    rw [hop]; exact sum_eq_sum_subtype_ne_zero w _ (fun i hi => by simp [hi])
  rw [ρ.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum he (fun i => w i.1) hop',
    Real.entropy_eq, Real.entropy_eq]
  exact (sum_eq_sum_subtype_ne_zero w (fun i => (w i).negMulLog)
    (fun i hi => by simp [hi, Real.negMulLog_zero])).symm

end AxQM
