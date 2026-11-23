/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EnsemblePurification
import AxQM.Postulates.API.PureMarginalEntropy
import AxQM.Postulates.API.EntropySpectral
import AxQM.Postulates.API.EntropyOrthogonalMixture
import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropyPinching

/-!
# AxQM — the reverse direction of the N&C Thm 11.10 equality condition (pure case)

Nielsen & Chuang, Theorem 11.10, states the entropy-of-a-mixture bound
`S(∑ᵢ pᵢ ρᵢ) ≤ ∑ᵢ pᵢ S(ρᵢ) + H(p)` with equality **iff** the `ρᵢ` have support on
orthogonal subspaces. The `⟸` ("if") direction is in
`AxQM/Postulates/API/EntropyOrthogonalMixture.lean`. This file develops the `⟹` ("only if")
direction for the **pure-ensemble case** — the engine on which the general mixed case is built.

Nielsen & Chuang prove the reverse direction (their pure-state argument,
eq. (11.88)–(11.91)) by purifying the ensemble `e = {pᵢ, |ψᵢ⟩}` to
`|AR⟩ = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩`, whose reference marginal is the **Gram operator**
`σ = ∑ᵢⱼ √pᵢ √pⱼ ⟪ψⱼ, ψᵢ⟫ |i⟩⟨j|` (`Ensemble.purify_reducedRight_op`). Since `|AR⟩` is
pure, `S(σ) = S(ρ)` — the marginal entropies of a pure bipartite state agree (Theorem 11.8
part 3, `S(A) = S(B)`, `PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`). Measuring
the reference in the `|i⟩` basis then pinches `σ` to the weight-diagonal density
`∑ᵢ pᵢ |i⟩⟨i|` of entropy `H(p)`; when `S(ρ) = H(p)` the pinching preserves entropy, so (by
the equality case of the pinching-entropy inequality
`ContinuousLinearMap.vonNeumannEntropy_krausSumₗ_eq_iff`) it fixes `σ`, forcing `σ` diagonal
and hence `⟪ψⱼ, ψᵢ⟫ = 0` for `i ≠ j`.

## Main results

* `AxQM.Ensemble.vonNeumannEntropy_toState_eq_reducedRight` — `S(ρ) = S(σ)`: the
  ensemble's mixture and its Gram reference marginal have equal von Neumann entropy. This is
  the pivotal purity fact the reverse direction rests on.
* `AxQM.Ensemble.inner_states_eq_zero_of_vonNeumannEntropy_toState_eq` — the
  **pure-case reverse direction**: if the ensemble mixture attains the maximal entropy
  `S(ρ) = H(p)` (equality in Theorem 11.10 with pure components, `S(ρᵢ) = 0`), then the
  ensemble states `|ψᵢ⟩`, `|ψⱼ⟩` of non-zero probability are pairwise orthogonal
  (`⟪ψⱼ, ψᵢ⟫ = 0` for `i ≠ j`). This is the engine the general mixed-case converse and
  the final `iff` `State.vonNeumannEntropy_mix_eq_iff_orthogonal` are built on.

The proof carries out N&C's own argument entirely at the **operator level** to avoid the
`ofModel (EuclideanSpace …)` / `EuclideanSpace` definitional-equality diamond that breaks
`rw`/`simp` when an operator is applied to individual reference basis vectors: with the diagonal
star projectors `Qₖ = |k⟩⟨k|` (`InnerProductSpace.isStarProjection_rankOne_self`,
`OrthonormalBasis.sum_rankOne_eq_id`), the sandwich `Qₐ σ Q_c = √pₐ √p_c ⟪ψ_c, ψₐ⟫ · |a⟩⟨c|` is
computed by `InnerProductSpace.rankOne_comp_rankOne`, giving the pinching
`krausSumₗ Q σ = ∑ₖ pₖ |k⟩⟨k|` on the diagonal (entropy `H(p)`, via
`State.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum`) and, once
`vonNeumannEntropy_krausSumₗ_eq_iff` forces `krausSumₗ Q σ = σ`, the off-diagonal read-off
`√pᵢ √pⱼ ⟪ψⱼ, ψᵢ⟫ = 0`.

The reduction of the general mixed case to its combined eigen-ensemble, and the final `iff`, are
in the later declarations of this file.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Ensemble

/-- **The mixture and its Gram reference marginal have equal entropy** (purity of the
ensemble purification). For an ensemble `e = {pᵢ, |ψᵢ⟩}` generating `ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`,
the reference marginal `σ = e.purify.reducedRight` of the purification
`|AR⟩ = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩` satisfies `S(ρ) = S(σ)`. Since `|AR⟩` is pure, its two reduced
states share the squared-Schmidt-coefficient spectrum, so their entropies agree
(`PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`, the statement `S(A) = S(B)`);
`Ensemble.purify_reducedLeft` identifies the left marginal with `ρ`. It is the reference-side
entropy the reverse direction of the Theorem 11.10 equality condition pins to `H(p)`. -/
theorem vonNeumannEntropy_toState_eq_reducedRight (e : Ensemble S) :
    e.toState.vonNeumannEntropy = e.purify.toState.reducedRight.vonNeumannEntropy := by
  rw [← e.purify_reducedLeft]
  exact e.purify.vonNeumannEntropy_reducedLeft_eq_reducedRight

/-- **Pure-case reverse direction of the Theorem 11.10 equality condition.** If the density
operator `ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` of an ensemble `e = {pᵢ, |ψᵢ⟩}` of *pure* states attains the maximal
von Neumann entropy `S(ρ) = H(p)` (equality in the entropy-of-a-mixture bound with pure components,
`S(ρᵢ) = 0`), then the ensemble states of non-zero probability are pairwise orthogonal:
`⟪ψⱼ, ψᵢ⟫ = 0` whenever `i ≠ j`, `pᵢ ≠ 0`, `pⱼ ≠ 0`.

This is Nielsen & Chuang's pure-state argument (eq. (11.88)–(11.91)). Purify `e` to
`|AR⟩ = ∑ᵢ √pᵢ |ψᵢ⟩ ⊗ |i⟩`; its reference marginal `σ` is the Gram operator
`∑ᵢⱼ √pᵢ √pⱼ ⟪ψⱼ, ψᵢ⟫ |i⟩⟨j|` (`purify_reducedRight_op`), and `S(σ) = S(ρ) = H(p)`
(`vonNeumannEntropy_toState_eq_reducedRight`, the purity fact, plus the hypothesis). Pinching `σ`
by the diagonal projectors `Qₖ = |k⟩⟨k|` gives the weight-diagonal `∑ₖ pₖ |k⟩⟨k|`, of entropy
`H(p)`; equality of entropies forces the pinching to fix `σ`
(`ContinuousLinearMap.vonNeumannEntropy_krausSumₗ_eq_iff`), so `σ` is diagonal and each
off-diagonal entry `√pᵢ √pⱼ ⟪ψⱼ, ψᵢ⟫` vanishes.

The engine for the general mixed-case converse and the final `iff`
`State.vonNeumannEntropy_mix_eq_iff_orthogonal`. -/
theorem inner_states_eq_zero_of_vonNeumannEntropy_toState_eq (e : Ensemble S)
    (hS : e.toState.vonNeumannEntropy = Real.entropy e.prob)
    {i j : Fin e.card} (hij : i ≠ j) (hi : e.prob i ≠ 0) (hj : e.prob j ≠ 0) :
    inner ℂ (e.states j).vec (e.states i).vec = 0 := by
  classical
  set R := QSystem.ofModel (EuclideanSpace ℂ (Fin e.card)) with hR
  set σ : State R := e.purify.toState.reducedRight with hσ
  set b : OrthonormalBasis (Fin e.card) ℂ R.space := EuclideanSpace.basisFun (Fin e.card) ℂ with hb
  set Q : Fin e.card → (R.space →L[ℂ] R.space) :=
    fun k => InnerProductSpace.rankOne ℂ (b k) (b k) with hQ
  -- The reference marginal is the Gram operator (re-typed against the reference basis `b`).
  have hgram : σ.op = ∑ i, ∑ j,
      ((Real.sqrt (e.prob i) : ℂ) * (Real.sqrt (e.prob j) : ℂ)
        * inner ℂ (e.states j).vec (e.states i).vec) • InnerProductSpace.rankOne ℂ (b i) (b j) :=
    e.purify_reducedRight_op
  -- Orthonormal-basis inner products.
  have hbip : ∀ k l, inner ℂ (b k) (b l) = if k = l then (1 : ℂ) else 0 :=
    fun k l => orthonormal_iff_ite.mp b.orthonormal k l
  -- The diagonal projectors form a complete family of orthogonal star projections.
  have hnorm : ∀ k, ‖b k‖ = 1 := fun k => b.orthonormal.norm_eq_one k
  have hP : ∀ k, IsStarProjection (Q k) := fun k =>
    InnerProductSpace.isStarProjection_rankOne_self (hnorm k)
  have hQQ : ∀ k l, Q k * Q l = inner ℂ (b k) (b l) • InnerProductSpace.rankOne ℂ (b k) (b l) := by
    intro k l
    simp only [hQ, ContinuousLinearMap.mul_def, InnerProductSpace.rankOne_comp_rankOne]
  have horth : ∀ k l, k ≠ l → Q k * Q l = 0 := by
    intro k l hkl
    rw [hQQ, hbip, ite_eq_right hkl, zero_smul]
  have hsum : ∑ k, Q k = 1 := by
    simp only [hQ]
    exact (OrthonormalBasis.sum_rankOne_eq_id b).trans ContinuousLinearMap.one_def.symm
  -- The sandwich `Qₐ · rankOne(bₘ,bₙ) · Q_c = ⟪bₐ,bₘ⟫⟪bₙ,b_c⟫ · rankOne(bₐ,b_c)`.
  have hsand : ∀ (a c m n : Fin e.card),
      Q a * InnerProductSpace.rankOne ℂ (b m) (b n) * Q c
        = (inner ℂ (b a) (b m) * inner ℂ (b n) (b c))
          • InnerProductSpace.rankOne ℂ (b a) (b c) := by
    intro a c m n
    simp only [hQ, ContinuousLinearMap.mul_def, ContinuousLinearMap.smul_comp,
      InnerProductSpace.rankOne_comp_rankOne, smul_smul]
  -- The key operator identity: `Qₐ σ Q_c = √pₐ √p_c ⟪ψ_c,ψₐ⟫ · rankOne(bₐ,b_c)`.
  have keyOp : ∀ a c, Q a * σ.op * Q c
      = ((Real.sqrt (e.prob a) : ℂ) * (Real.sqrt (e.prob c) : ℂ)
          * inner ℂ (e.states c).vec (e.states a).vec)
        • InnerProductSpace.rankOne ℂ (b a) (b c) := by
    intro a c
    rw [hgram]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, hsand]
    rw [Finset.sum_eq_single a
          (fun d _ hda => by
            refine Finset.sum_eq_zero (fun f _ => ?_)
            rw [hbip a d, ite_eq_right (Ne.symm hda), zero_mul, zero_smul, smul_zero])
          (fun h => absurd (Finset.mem_univ a) h),
        Finset.sum_eq_single c
          (fun d _ hdc => by rw [hbip d c, ite_eq_right hdc, mul_zero, zero_smul, smul_zero])
          (fun h => absurd (Finset.mem_univ c) h)]
    simp
  -- The pinching of the Gram operator is the weight-diagonal `∑ₖ pₖ |k⟩⟨k|`.
  have hpinch : ContinuousLinearMap.krausSumₗ Q σ.op = ∑ k, (e.prob k : ℂ) • Q k := by
    rw [ContinuousLinearMap.krausSumₗ_eq_sum_conj_of_isStarProjection hP]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hself : inner ℂ (e.states k).vec (e.states k).vec = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, (e.states k).normalized]; norm_num
    rw [keyOp k k, hself, mul_one]
    simp only [hQ]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (e.prob_nonneg k)]
  -- The pinched operator has entropy `H(p)`.
  have hDent : (ContinuousLinearMap.krausSumₗ Q σ.op).vonNeumannEntropy = Real.entropy e.prob := by
    have hDdens : (ContinuousLinearMap.krausSumₗ Q σ.op).IsDensityOp :=
      ContinuousLinearMap.isDensityOp_krausSumₗ_of_isStarProjection hP hsum σ.isDensity
    have hDop : (⟨ContinuousLinearMap.krausSumₗ Q σ.op, hDdens⟩ : State R).op
        = ∑ k, (e.prob k : ℂ) • InnerProductSpace.rankOne ℂ (b k) (b k) := by
      change ContinuousLinearMap.krausSumₗ Q σ.op = _
      rw [hpinch]
    exact (⟨ContinuousLinearMap.krausSumₗ Q σ.op, hDdens⟩ :
      State R).vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum b.orthonormal e.prob hDop
  -- `S(σ) = S(ρ) = H(p)`.
  have hσent : σ.op.vonNeumannEntropy = Real.entropy e.prob :=
    (e.vonNeumannEntropy_toState_eq_reducedRight).symm.trans hS
  -- Equal entropies force the pinching to fix `σ`, so `σ` is weight-diagonal.
  have hfix : ContinuousLinearMap.krausSumₗ Q σ.op = σ.op :=
    (ContinuousLinearMap.vonNeumannEntropy_krausSumₗ_eq_iff hP horth hsum σ.isDensity).mp (by
      rw [hσent]; exact hDent)
  have hdiag : σ.op = ∑ k, (e.prob k : ℂ) • Q k := hfix.symm.trans hpinch
  -- Off-diagonal block vanishes: `Qᵢ σ Qⱼ = 0` for `i ≠ j`.
  have hoff : Q i * σ.op * Q j = 0 := by
    rw [hdiag, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [mul_smul_comm, smul_mul_assoc]
    by_cases hki : k = i
    · rw [hki, mul_assoc, horth i j hij, mul_zero, smul_zero]
    · rw [horth i k (Ne.symm hki), zero_mul, smul_zero]
  -- Read off the vanishing overlap.
  have hcombine : ((Real.sqrt (e.prob i) : ℂ) * (Real.sqrt (e.prob j) : ℂ)
        * inner ℂ (e.states j).vec (e.states i).vec)
      • InnerProductSpace.rankOne ℂ (b i) (b j) = 0 := by
    rw [← keyOp i j]; exact hoff
  have happ := congrArg (fun T : R.space →L[ℂ] R.space => T (b j)) hcombine
  simp only [smul_apply, InnerProductSpace.rankOne_apply,
    zero_apply] at happ
  rw [hbip j j, ite_eq_left rfl, one_smul] at happ
  have hsqrt : ∀ k, e.prob k ≠ 0 → ((Real.sqrt (e.prob k) : ℝ) : ℂ) ≠ 0 := fun k hk =>
    Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (lt_of_le_of_ne (e.prob_nonneg k) (Ne.symm hk))).ne'
  have hspi := hsqrt i hi
  have hspj := hsqrt j hj
  rcases smul_eq_zero.mp happ with hs | hbi0
  · rcases mul_eq_zero.mp hs with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · exact absurd h1 hspi
      · exact absurd h2 hspj
    · exact h3
  · exact absurd hbi0 (b.orthonormal.ne_zero i)

end Ensemble

/-- **Dropping the probability-zero terms of a finite sum.** If `f i = 0` whenever `p i = 0`, the
sum of `f` over the whole index type equals the sum over the sub-type of positive-weight indices.
The shared "restrict to the support of `p`" bridge used to transfer the orthogonal-support mixture
identity from the positive-weight subfamily back to the whole family. -/
private theorem sum_dropZeroProb {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (p : ι → ℝ) (f : ι → M) (hf : ∀ i, p i = 0 → f i = 0) :
    ∑ i, f i = ∑ i' : {i : ι // p i ≠ 0}, f i'.1 := by
  classical
  rw [← Finset.sum_subtype (s := Finset.univ.filter (fun i => p i ≠ 0)) (fun x => by simp) f]
  exact (Finset.sum_subset (Finset.filter_subset _ _)
    (fun x _ hx => hf x (by simpa using hx))).symm

/-- **Mixed-case reverse direction of the N&C Theorem 11.10 equality condition.** If a general
mixture `μ = ∑ᵢ pᵢ ρᵢ` of (possibly mixed) states attains the entropy-of-a-mixture upper bound with
equality, `S(μ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)`, then any two components of non-zero probability have
**orthogonal supports** — recorded as the vanishing operator product `(ρ i).op * (ρ j).op = 0`
(`State.support_isOrtho_iff_op_mul_eq_zero`).

This is Nielsen & Chuang's mixed-state argument (eq. (11.92)–(11.94)): diagonalise each component
`ρᵢ.op = ∑ₖ λᵢₖ |eᵢₖ⟩⟨eᵢₖ|` and view `μ` as the **combined pure-state ensemble** `{pᵢ λᵢₖ, |eᵢₖ⟩}`
over the sigma index `Σ i, Fin d` (re-indexed to `Fin (|ι|·d)`). By the grouping identity
`Real.entropy_sigma_mul` (using `∑ₖ λᵢₖ = 1` and `S(ρᵢ) = H(λᵢ)`), the combined-weight entropy is
exactly `H(p) + ∑ᵢ pᵢ S(ρᵢ)`, so the equality hypothesis reads `S(μ) = H(pᵢ λᵢₖ)` — maximal entropy
for the combined ensemble. The pure-case engine
`Ensemble.inner_states_eq_zero_of_vonNeumannEntropy_toState_eq` then forces the combined
eigenvectors of non-zero weight to be pairwise orthogonal; in particular, for `i ≠ j` with
`pᵢ, pⱼ ≠ 0`, every non-zero-eigenvalue eigenvector of `ρᵢ` is orthogonal to every one of `ρⱼ`. The
product `ρᵢ.op * ρⱼ.op = ∑ₐ ∑_b λᵢₐ λⱼ_b ⟪eᵢₐ, eⱼ_b⟫ |eᵢₐ⟩⟨eⱼ_b|` then vanishes term by term
(`InnerProductSpace.rankOne_comp_rankOne`): each summand has a zero eigenvalue or, when both are
non-zero, a zero overlap.

The `⟹` direction the Theorem 11.10 equality *iff* (`State.vonNeumannEntropy_mix_eq_iff_orthogonal`)
is assembled from, paired with the orthogonal-support `⟸` engine
(`State.vonNeumannEntropy_mix_eq_of_pairwise_op_mul_eq_zero`). -/
theorem State.op_mul_eq_zero_of_vonNeumannEntropy_mix_eq {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S)
    (hS : (State.mix p hp hsum ρ).vonNeumannEntropy
      = Real.entropy p + ∑ i, p i * (ρ i).vonNeumannEntropy)
    {i j : ι} (hij : i ≠ j) (hi : p i ≠ 0) (hj : p j ≠ 0) :
    (ρ i).op * (ρ j).op = 0 := by
  classical
  set d := Module.finrank ℂ S.space with hd
  -- Canonical spectral data of each component: eigenbasis `bb i`, eigenvectors `b i k`,
  -- eigenvalues `lam i k`.
  set bb : (i : ι) → OrthonormalBasis (Fin d) ℂ S.space :=
    fun i => (ρ i).isDensity.isSymmetric.eigenvectorBasis rfl with hbb
  set b : (i : ι) → Fin d → S.space := fun i k => bb i k with hb
  set lam : (i : ι) → Fin d → ℝ :=
    fun i k => (ρ i).isDensity.isSymmetric.eigenvalues rfl k with hlam
  have hspec : ∀ i, (ρ i).op
      = ∑ k, (lam i k : ℂ) • (InnerProductSpace.rankOne ℂ (b i k)) (b i k) :=
    fun i => ((ρ i).isDensity.isPositive.isSelfAdjoint).spectral_sum rfl
  have hq : ∀ i, ∑ k, lam i k = 1 := fun i => (ρ i).isDensity.eigenvalues_sum_eq_one rfl
  have hSi : ∀ i, (ρ i).vonNeumannEntropy = Real.entropy (lam i) := fun i =>
    (ρ i).vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum (bb i).orthonormal (lam i)
      (hspec i)
  have hlnn : ∀ i k, 0 ≤ lam i k := fun i k => (ρ i).isDensity.eigenvalues_nonneg rfl k
  have hnorm : ∀ i k, ‖b i k‖ = 1 := fun i k => (bb i).orthonormal.norm_eq_one k
  -- The combined pure-state ensemble `{pᵢ λᵢₖ, |eᵢₖ⟩}` over `Σ i, Fin d`, re-indexed to `Fin n`.
  set n := Fintype.card (Σ _i : ι, Fin d) with hn
  set ec : (Σ _i : ι, Fin d) ≃ Fin n := Fintype.equivFin _ with hec
  set e : Ensemble S :=
    { card := n
      prob := fun m => p (ec.symm m).1 * lam (ec.symm m).1 (ec.symm m).2
      states := fun m => ⟨b (ec.symm m).1 (ec.symm m).2, hnorm _ _⟩
      prob_nonneg := fun m => mul_nonneg (hp _) (hlnn _ _)
      sum_prob := by
        rw [show (∑ m, p (ec.symm m).1 * lam (ec.symm m).1 (ec.symm m).2)
              = ∑ x : Σ _i : ι, Fin d, p x.1 * lam x.1 x.2 from
            Equiv.sum_comp ec.symm (fun x => p x.1 * lam x.1 x.2), Fintype.sum_sigma]
        simp_rw [← Finset.mul_sum, hq, mul_one]
        exact hsum } with he
  have hprob : ∀ m, e.prob m = p (ec.symm m).1 * lam (ec.symm m).1 (ec.symm m).2 :=
    fun m => rfl
  have hvec : ∀ m, (e.states m).vec = b (ec.symm m).1 (ec.symm m).2 := fun m => rfl
  -- The ensemble's density operator is the mixture `μ`.
  have hmixop := State.mix_op_eq_sum_sigma_rankOne p hp hsum ρ b lam hspec
  have htoStateEq : e.toState = State.mix p hp hsum ρ := by
    apply State.ext
    rw [Ensemble.toState_op, hmixop,
      ← Equiv.sum_comp ec.symm (fun x : Σ _i : ι, Fin d =>
        ((p x.1 * lam x.1 x.2 : ℝ) : ℂ) • (InnerProductSpace.rankOne ℂ (b x.1 x.2)) (b x.1 x.2))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [PureState.toState_op, hvec m, hprob m]
  -- The combined-weight entropy is `H(p) + ∑ᵢ pᵢ S(ρᵢ)`.
  have hentropy : Real.entropy e.prob = Real.entropy p + ∑ i, p i * (ρ i).vonNeumannEntropy := by
    have hre : Real.entropy e.prob
        = Real.entropy (fun x : Σ _i : ι, Fin d => p x.1 * lam x.1 x.2) := by
      rw [Real.entropy_eq, Real.entropy_eq]
      exact Equiv.sum_comp ec.symm (fun x => Real.negMulLog (p x.1 * lam x.1 x.2))
    rw [hre, Real.entropy_sigma_mul p lam hq]
    simp_rw [hSi]
  -- Maximal entropy for the combined ensemble.
  have hC : e.toState.vonNeumannEntropy = Real.entropy e.prob := by
    rw [htoStateEq, hS, hentropy]
  -- Cross-block eigenvector orthogonality from the pure-case engine.
  have hcross : ∀ a a' : Fin d, lam i a ≠ 0 → lam j a' ≠ 0 →
      inner ℂ (b j a') (b i a) = 0 := by
    intro a a' ha ha'
    have hne : ec ⟨i, a⟩ ≠ ec ⟨j, a'⟩ := by
      rw [ne_eq, Equiv.apply_eq_iff_eq]
      exact fun h => hij (congrArg Sigma.fst h)
    have hpi : e.prob (ec ⟨i, a⟩) ≠ 0 := by
      rw [hprob, Equiv.symm_apply_apply]; exact mul_ne_zero hi ha
    have hpj : e.prob (ec ⟨j, a'⟩) ≠ 0 := by
      rw [hprob, Equiv.symm_apply_apply]; exact mul_ne_zero hj ha'
    have hkey := e.inner_states_eq_zero_of_vonNeumannEntropy_toState_eq hC hne hpi hpj
    rw [hvec, hvec, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hkey
    exact hkey
  -- The operator product vanishes term by term.
  rw [hspec i, hspec j, Finset.sum_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun a' _ => ?_
  simp only [smul_mul_assoc, mul_smul_comm, ContinuousLinearMap.mul_def,
    InnerProductSpace.rankOne_comp_rankOne]
  by_cases ha : lam i a = 0
  · simp [ha]
  · by_cases ha' : lam j a' = 0
    · simp [ha']
    · have hz : inner ℂ (b i a) (b j a') = (0 : ℂ) := by
        rw [← inner_conj_symm (b i a) (b j a'), hcross a a' ha ha', map_zero]
      simp [hz]

/-- **N&C Theorem 11.10, the equality condition.** For a mixture `μ = ∑ᵢ pᵢ ρᵢ` of quantum states,
the entropy-of-a-mixture upper bound `S(μ) ≤ H(p) + ∑ᵢ pᵢ S(ρᵢ)` (eq. (11.87)) holds with
**equality if and only if the components of non-zero probability have orthogonal supports**:

`S(∑ᵢ pᵢ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ) ↔ (∀ i ≠ j with pᵢ, pⱼ ≠ 0, (ρ i).op * (ρ j).op = 0)`.

The orthogonal-support condition is recorded as the vanishing operator product
`(ρ i).op * (ρ j).op = 0`, the intrinsic form of `(ρ i).support ⟂ (ρ j).support`
(`State.support_isOrtho_iff_op_mul_eq_zero`). The `pᵢ, pⱼ ≠ 0` restriction is essential and
faithful: a probability-zero component contributes nothing to `μ` and nothing to the bound
(`0 · S(ρᵢ) = 0`, `η(0) = 0`), so its support is genuinely unconstrained — the *unrestricted*
pairwise condition would make the iff false (e.g. `p = (1, 0)` gives equality for every `ρ₂`).

* `⟹` is the mixed-case reverse engine `State.op_mul_eq_zero_of_vonNeumannEntropy_mix_eq` (N&C's
  eigen-ensemble reduction to the pure-state argument).
* `⟸` restricts to the positive-weight subfamily `{i // pᵢ ≠ 0}` — on which the condition is the
  full `Pairwise` hypothesis of the orthogonal-support "if" engine
  `State.vonNeumannEntropy_mix_eq_of_pairwise_op_mul_eq_zero` — and transfers the resulting identity
  back to the whole family by dropping the (vanishing) probability-zero terms.

This is the formalisation of the Theorem 11.10 equality characterization; the statement of the
theorem is in `AxQM/NC/Ch11/Theorem11_10.lean`. -/
theorem State.vonNeumannEntropy_mix_eq_iff_orthogonal {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S) :
    (State.mix p hp hsum ρ).vonNeumannEntropy
        = Real.entropy p + ∑ i, p i * (ρ i).vonNeumannEntropy
      ↔ ∀ ⦃i j⦄, i ≠ j → p i ≠ 0 → p j ≠ 0 → (ρ i).op * (ρ j).op = 0 := by
  classical
  refine ⟨fun hS _i _j hij hi hj =>
    State.op_mul_eq_zero_of_vonNeumannEntropy_mix_eq p hp hsum ρ hS hij hi hj, fun horth => ?_⟩
  -- `⟸`: restrict to the positive-weight subfamily, apply the orthogonal-support "if" engine, and
  -- drop the vanishing probability-zero terms.
  set p' : {i : ι // p i ≠ 0} → ℝ := fun i' => p i'.1 with hp'def
  set ρ' : {i : ι // p i ≠ 0} → State S := fun i' => ρ i'.1 with hρ'def
  have hp' : ∀ i', 0 ≤ p' i' := fun i' => hp i'.1
  have hsum' : ∑ i', p' i' = 1 := (sum_dropZeroProb p p (fun _ h => h)).symm.trans hsum
  have hmixeq : State.mix p' hp' hsum' ρ' = State.mix p hp hsum ρ := by
    apply State.ext
    rw [State.mix_op, State.mix_op]
    exact (sum_dropZeroProb p (fun i => (p i : ℂ) • (ρ i).op) (fun i h => by simp [h])).symm
  have horth' : Pairwise fun i' j' => (ρ' i').op * (ρ' j').op = 0 := fun i' j' hne =>
    horth (fun h => hne (Subtype.ext h)) i'.2 j'.2
  rw [← hmixeq, State.vonNeumannEntropy_mix_eq_of_pairwise_op_mul_eq_zero p' hp' hsum' ρ' horth']
  congr 1
  · rw [Real.entropy_eq, Real.entropy_eq]
    exact (sum_dropZeroProb p (fun i => Real.negMulLog (p i))
      (fun i h => by simp [h, Real.negMulLog_zero])).symm
  · exact (sum_dropZeroProb p (fun i => p i * (ρ i).vonNeumannEntropy)
      (fun i h => by simp [h])).symm

end AxQM
