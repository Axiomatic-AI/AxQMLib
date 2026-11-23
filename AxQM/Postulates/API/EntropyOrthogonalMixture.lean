/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Mixture
import AxQM.Postulates.API.EntropySpectral
import AxQM.Postulates.API.Support

/-!
# AxQM — entropy of a mixture with orthogonal supports (N&C Thm 11.8 part 4 / Thm 11.10)

For a mixture `μ = State.mix p ρ = ∑ᵢ pᵢ ρᵢ` of quantum states whose components have **orthogonal
supports**, the von Neumann entropy is *exactly* the average component entropy plus the Shannon
entropy of the weights,

`S(∑ᵢ pᵢ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)`,

the equality case of the entropy-of-a-mixture bound (Nielsen & Chuang, *Quantum Computation and
Quantum Information*, Theorem 11.10, eq. (11.87)) and the orthogonal-support mixture identity of
Theorem 11.8 (part (4), eq. (11.57)).

This file supplies the shared "if" direction in two forms:

* `State.vonNeumannEntropy_mix_of_orthonormal_rankOne` — the **constructive engine**: "orthogonal
  supports" is given as a jointly-orthonormal family of eigen-decompositions
  `ρᵢ.op = ∑ₖ wᵢₖ |eᵢₖ⟩⟨eᵢₖ|` (the combined family over `Σ i, κ i` orthonormal), exactly as in N&C's
  own proof. It reads the mixture entropy off the single orthonormal rank-one sum and splits it with
  the grouping identity `Real.entropy_sigma_mul`. This is the reusable engine for the joint-entropy
  theorem (Thm 11.8 part 5) and the Thm 11.10 equality condition.
* `State.vonNeumannEntropy_mix_orthogonalSupport` — the **faithful N&C statement** of Theorem 11.8
  part (4): "orthogonal supports" is the literal `Pairwise ((ρ i).support ⟂ (ρ j).support)`. Its
  proof derives the eigen-decompositions internally (`IsSelfAdjoint.spectral_sum`) and proves the
  combined eigenfamily orthonormal on its support from the support-orthogonality hypothesis
  (`State.eigenvectorBasis_mem_support_iff`, `Submodule.isOrtho_iff_inner_eq`), feeding the
  degenerate-weight engine
  `State.vonNeumannEntropy_eq_entropy_of_rankOne_sum_orthonormal_on_ne_zero` and the grouping
  identity `Real.entropy_sigma_mul`.

## Main results

The statement of Theorem 11.8 is in `AxQM/NC/Ch11/Theorem11_8.lean`; the declarations are here.

* `AxQM.State.mix_op_eq_sum_sigma_rankOne` — the shared operator bridge: a mixture of
  states with rank-one decompositions is the single `Σ`-indexed rank-one sum with weights `pᵢ wᵢₖ`.
* `AxQM.State.vonNeumannEntropy_mix_of_orthonormal_rankOne` — engine form,
  `S(∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ S(ρᵢ) + H(p)` for components with jointly-orthonormal eigen-decompositions.
* `AxQM.State.vonNeumannEntropy_mix_orthogonalSupport` — Nielsen–Chuang Theorem 11.8
  part (4), `S(∑ᵢ pᵢ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)` under `Pairwise ((ρ i).support ⟂ (ρ j).support)`.
* `AxQM.State.vonNeumannEntropy_mix_eq_of_pairwise_op_mul_eq_zero` — the **"if" direction**
  of the Theorem 11.10 equality condition, stated over the intrinsic operator-product predicate
  `Pairwise ((ρ i).op * (ρ j).op = 0)`: pairwise-vanishing density-operator products (= orthogonal
  supports, `State.support_isOrtho_iff_op_mul_eq_zero`) give equality `S(∑ᵢ pᵢ ρᵢ) = H(p) + ∑ᵢ pᵢ
  S(ρᵢ)`. This is the form over which the iff `vonNeumannEntropy_mix_eq_iff_orthogonal` is
  assembled in `AxQM/Postulates/API/EntropyMixtureReverse.lean`, where the converse ("only if")
  is proved.
-/

namespace AxQM

open scoped InnerProductSpace

variable {S : QSystem}

/-- **The density operator of a mixture as a `Σ`-indexed rank-one sum.** If the components of a
mixture carry rank-one decompositions `(ρ i).op = ∑ₖ wᵢₖ |eᵢₖ⟩⟨eᵢₖ|`, then the mixture's operator
`∑ᵢ pᵢ ρᵢ` is the single rank-one sum over the sigma index `Σ i, κ i` with weights `pᵢ wᵢₖ`. The
shared operator-decomposition bridge behind both the constructive equality engine
`State.vonNeumannEntropy_mix_of_orthonormal_rankOne` and the orthogonal-support identity
`State.vonNeumannEntropy_mix_orthogonalSupport`. -/
theorem State.mix_op_eq_sum_sigma_rankOne {ι : Type*} [Fintype ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (ρ : ι → State S) (e : (i : ι) → κ i → S.space) (w : (i : ι) → κ i → ℝ)
    (hop : ∀ i, (ρ i).op = ∑ k, (w i k : ℂ) • (InnerProductSpace.rankOne ℂ (e i k)) (e i k)) :
    (State.mix p hp hsum ρ).op
      = ∑ ik : Σ i, κ i, ((p ik.1 * w ik.1 ik.2 : ℝ) : ℂ) •
          (InnerProductSpace.rankOne ℂ (e ik.1 ik.2)) (e ik.1 ik.2) := by
  rw [State.mix_op, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hop i, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]; congr 1; push_cast; ring

/-- **Entropy of a mixture with orthogonal supports** (Nielsen & Chuang, Theorem 11.10, equality
case of eq. (11.87); the engine for Theorem 11.8 parts 4–5). For a probability distribution `p` and
a family `ρ : ι → State S` whose components carry orthonormal eigen-decompositions
`ρᵢ.op = ∑ₖ wᵢₖ |eᵢₖ⟩⟨eᵢₖ|` that are **jointly orthonormal** across components (the combined family
`⟨i, k⟩ ↦ eᵢₖ` is orthonormal — i.e. the `ρᵢ` have mutually orthogonal supports), the von Neumann
entropy of the mixture is the average component entropy plus the Shannon entropy of the weights:

`S(∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ S(ρᵢ) + H(p)`, where `H(p) = Real.entropy p`.

The mixed operator is the single orthonormal rank-one sum
`μ.op = ∑_{⟨i,k⟩} (pᵢ wᵢₖ) |eᵢₖ⟩⟨eᵢₖ|`, so
`State.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum` evaluates `S(μ)` to the Shannon
entropy of `⟨i,k⟩ ↦ pᵢ wᵢₖ`; the grouping identity `Real.entropy_sigma_mul` (using `∑ₖ wᵢₖ = 1`)
splits this into `H(p) + ∑ᵢ pᵢ H(wᵢ)`, and each `S(ρᵢ) = H(wᵢ)` by the same engine restricted to
the `i`-th orthonormal block. -/
theorem State.vonNeumannEntropy_mix_of_orthonormal_rankOne
    {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S)
    (e : (i : ι) → κ i → S.space) (w : (i : ι) → κ i → ℝ)
    (hortho : Orthonormal ℂ (fun ik : Σ i, κ i => e ik.1 ik.2))
    (hwsum : ∀ i, ∑ k, w i k = 1)
    (hop : ∀ i, (ρ i).op
      = ∑ k, (w i k : ℂ) • (InnerProductSpace.rankOne ℂ (e i k)) (e i k)) :
    (State.mix p hp hsum ρ).vonNeumannEntropy
      = ∑ i, p i * (ρ i).vonNeumannEntropy + Real.entropy p := by
  classical
  -- The mixture's operator is the single `Σ`-indexed orthonormal rank-one sum, weights `pᵢ wᵢₖ`.
  have hmixop := State.mix_op_eq_sum_sigma_rankOne p hp hsum ρ e w hop
  -- Entropy of the mixture read off the combined orthonormal decomposition.
  have hmix := (State.mix p hp hsum ρ).vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum
    hortho (fun ik => p ik.1 * w ik.1 ik.2) hmixop
  -- Entropy of each component, from the `i`-th orthonormal block of the combined family.
  have hcomp : ∀ i, (ρ i).vonNeumannEntropy = Real.entropy (w i) := fun i =>
    (ρ i).vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum
      (hortho.comp (Sigma.mk i) sigma_mk_injective) (w i) (hop i)
  -- Assemble via the classical grouping identity.
  rw [hmix, Real.entropy_sigma_mul p w hwsum]
  simp_rw [hcomp]
  ring

/-- **Entropy of an orthogonal-support mixture** (Nielsen–Chuang Theorem 11.8, part (4),
eq. (11.57)). For a probability distribution `p` and a family `ρ : ι → State S` whose supports are
**pairwise orthogonal** (`(ρ i).support ⟂ (ρ j).support` for `i ≠ j`), the von Neumann entropy of
the mixture `State.mix p hp hsum ρ = ∑ᵢ pᵢ ρᵢ` is the Shannon entropy `H(p)` of the weights plus the
`p`-average of the component entropies:

`S(∑ᵢ pᵢ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)`.

This is the N&C-faithful form of the equality engine
`State.vonNeumannEntropy_mix_of_orthonormal_rankOne` above: rather than *assuming*
jointly-orthonormal eigen-decompositions, it derives them. Each summand is diagonalised
(`IsSelfAdjoint.spectral_sum`), the combined eigenfamily over `Σ i, Fin d` is orthonormal on the
non-zero weights because the supports are orthogonal (`State.eigenvectorBasis_mem_support_iff`,
`Submodule.isOrtho_iff_inner_eq`), and the degenerate-weight engine
`State.vonNeumannEntropy_eq_entropy_of_rankOne_sum_orthonormal_on_ne_zero` reads off
`S(mix) = H(⟨i,j⟩ ↦ pᵢ λᵢⱼ)`, which the grouping identity `Real.entropy_sigma_mul` splits into
`H(p) + ∑ᵢ pᵢ H(λᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)`. -/
theorem State.vonNeumannEntropy_mix_orthogonalSupport {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S)
    (horth : Pairwise fun i j => (ρ i).support ⟂ (ρ j).support) :
    (State.mix p hp hsum ρ).vonNeumannEntropy
      = Real.entropy p + ∑ i, p i * (ρ i).vonNeumannEntropy := by
  classical
  set d := Module.finrank ℂ S.space
  -- Canonical spectral data of each summand: eigenvector basis `b i` and eigenvalues `lam i`.
  set b : (i : ι) → Fin d → S.space :=
    fun i j => (ρ i).isDensity.isSymmetric.eigenvectorBasis rfl j
  set lam : (i : ι) → Fin d → ℝ :=
    fun i j => (ρ i).isDensity.isSymmetric.eigenvalues rfl j
  set W : (Σ _ : ι, Fin d) → ℝ := fun x => p x.1 * lam x.1 x.2 with hW
  -- Per-summand spectral decomposition, spectrum summing to one, and entropy `S(ρᵢ) = H(λᵢ)`.
  have hspec : ∀ i, (ρ i).op
      = ∑ j, (lam i j : ℂ) • (InnerProductSpace.rankOne ℂ (b i j)) (b i j) :=
    fun i => ((ρ i).isDensity.isPositive.isSelfAdjoint).spectral_sum rfl
  have hq : ∀ i, ∑ j, lam i j = 1 := fun i => (ρ i).isDensity.eigenvalues_sum_eq_one rfl
  have hSi : ∀ i, (ρ i).vonNeumannEntropy = Real.entropy (lam i) := fun i =>
    (ρ i).vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum
      ((ρ i).isDensity.isSymmetric.eigenvectorBasis rfl).orthonormal (lam i) (hspec i)
  -- The mixture's density operator as a rank-one sum over the sigma index `Σ i, Fin d`.
  have hmixop : (State.mix p hp hsum ρ).op
      = ∑ x : Σ _ : ι, Fin d,
          (W x : ℂ) • (InnerProductSpace.rankOne ℂ (b x.1 x.2)) (b x.1 x.2) :=
    State.mix_op_eq_sum_sigma_rankOne p hp hsum ρ b lam hspec
  -- The eigenfamily is orthonormal on the non-zero weights: orthogonal supports do the work.
  have horthfam : Orthonormal ℂ (fun x : {x : Σ _ : ι, Fin d // W x ≠ 0} => b x.1.1 x.1.2) := by
    rw [orthonormal_iff_ite]
    rintro ⟨⟨i, j⟩, hx⟩ ⟨⟨k, l⟩, hy⟩
    have hlij : lam i j ≠ 0 := fun h => hx (by simp [hW, h])
    have hlkl : lam k l ≠ 0 := fun h => hy (by simp [hW, h])
    have hmi : b i j ∈ (ρ i).support := ((ρ i).eigenvectorBasis_mem_support_iff j).mpr hlij
    have hmk : b k l ∈ (ρ k).support := ((ρ k).eigenvectorBasis_mem_support_iff l).mpr hlkl
    by_cases hik : i = k
    · subst hik
      rw [orthonormal_iff_ite.mp ((ρ i).isDensity.isSymmetric.eigenvectorBasis rfl).orthonormal j l]
      congr 1
      simp only [Subtype.ext_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    · rw [ite_eq_right (by simp only [Subtype.ext_iff, Sigma.mk.inj_iff]; tauto)]
      exact Submodule.isOrtho_iff_inner_eq.mp (horth hik) (b i j) hmi (b k l) hmk
  -- Read off the mixture entropy, then split it with the classical grouping identity.
  rw [(State.mix p hp hsum ρ).vonNeumannEntropy_eq_entropy_of_rankOne_sum_orthonormal_on_ne_zero
      W horthfam hmixop, hW, Real.entropy_sigma_mul p lam hq]
  simp_rw [hSi]

/-- **Entropy of a mixture with orthogonal supports, intrinsic operator-product form** (the "if"
direction of the Nielsen–Chuang Theorem 11.10 equality condition). If the density operators of a
family `ρ : ι → State S` have **pairwise-vanishing products** `(ρ i).op * (ρ j).op = 0` for `i ≠ j`
— equivalently, pairwise orthogonal supports (`State.support_isOrtho_iff_op_mul_eq_zero`) — then the
von Neumann entropy of the mixture is exactly the average component entropy plus the Shannon entropy
of the weights:

`S(∑ᵢ pᵢ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)`.

This restates `State.vonNeumannEntropy_mix_orthogonalSupport` over the intrinsic operator predicate
`(ρ i).op * (ρ j).op = 0` (rather than the geometric `(ρ i).support ⟂ (ρ j).support`), the form the
Theorem 11.10 equality *iff* `vonNeumannEntropy_mix_eq_iff_orthogonal` is assembled over. The proof
just relays each `(ρ i).op * (ρ j).op = 0` back to support-orthogonality via the characterization
`State.support_isOrtho_iff_op_mul_eq_zero`. The converse ("equality ⟹ orthogonal supports") is
developed separately (via purification and the equality condition of Theorem 11.9). -/
theorem State.vonNeumannEntropy_mix_eq_of_pairwise_op_mul_eq_zero {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S)
    (horth : Pairwise fun i j => (ρ i).op * (ρ j).op = 0) :
    (State.mix p hp hsum ρ).vonNeumannEntropy
      = Real.entropy p + ∑ i, p i * (ρ i).vonNeumannEntropy :=
  State.vonNeumannEntropy_mix_orthogonalSupport p hp hsum ρ
    fun i j hij => (State.support_isOrtho_iff_op_mul_eq_zero (ρ i) (ρ j)).mpr (horth hij)

end AxQM
