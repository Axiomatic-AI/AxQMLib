/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.NoisyChannel
public import ToMathlib.InformationTheory.TypicalSequence

/-!
# Jointly typical sequences for a discrete memoryless channel

The achievability half of Shannon's noisy channel coding theorem (Nielsen & Chuang, Theorem 12.7)
is proved by *jointly typical* random coding (Cover–Thomas, ch. 7.7): a random codebook is decoded
by testing whether the received output string is jointly typical with a codeword. This file builds
the probabilistic foundation — the joint input–output sequence law and the jointly typical set —
reusing the classical typical-sequence machinery of `ToMathlib.InformationTheory.TypicalSequence`.

Fix a discrete memoryless channel `q : ι → κ → ℝ` (`Real.IsChannel`) and an input distribution
`p : ι → ℝ`. When the input string `Xⁿ` is drawn i.i.d. from `p` and passed through `n` uses of the
channel to produce `Yⁿ`, the pair `(Xⁿ, Yⁿ)` has the **joint input–output sequence law**

`Real.channelPairSeqProb q p (x, y) = (∏ⱼ p(xⱼ)) · ∏ⱼ q(yⱼ | xⱼ)`.

Because `p(xⱼ) · q(yⱼ | xⱼ) = channelJoint q p (xⱼ, yⱼ)`, this is exactly the `n`-fold i.i.d.
product of the single-use joint law `channelJoint q p` on `ι × κ`
(`Real.channelPairSeqProb_eq_prod_channelJoint`). Its first marginal is the i.i.d. input law `pⁿ`
(`Real.sum_snd_channelPairSeqProb`) and its second marginal is the i.i.d. output law
`(channelOutput q p)ⁿ` (`Real.sum_fst_channelPairSeqProb`).

A pair `(x, y)` is **jointly typical** (`Real.channelTypicalPairs`) when the pair-sequence is
typical for the joint law `channelJoint q p`, *and* `x` is typical for `p`, *and* `y` is typical for
the output law `channelOutput q p` — the three-way conjunction that the packing bound of the coding
theorem needs.

The **joint AEP** (`Real.exists_le_sum_channelTypicalPairs`) says the jointly typical set carries
probability `→ 1` under the true joint law; the **packing bound**
(`Real.sum_indep_channelTypicalPairs_le`) says it carries probability `≤ exp(-n(H(X:Y)-3ε))` under
the *independent* pair law `Real.channelIndepPairProb`, where the codeword is drawn independently of
the output. Together these are the two probabilistic inputs to the random-coding error analysis.

## Main declarations

* `Real.channelPairSeqProb` — the joint input–output sequence law of `(Xⁿ, Yⁿ)`.
* `Real.channelPairSeqProb_eq_prod_channelJoint` — it is the i.i.d. product of `channelJoint q p`.
* `Real.sum_channelPairSeqProb` — it is a probability distribution (total mass `1`).
* `Real.sum_snd_channelPairSeqProb`, `Real.sum_fst_channelPairSeqProb` — its input marginal `pⁿ` and
  output marginal `(channelOutput q p)ⁿ`.
* `Real.channelTypicalPairs` — the jointly typical set.
* `Real.exists_le_sum_channelTypicalPairs` — the joint AEP: the jointly typical set has probability
  `≥ 1 - δ` for large `n` under the true joint law.
* `Real.channelIndepPairProb` — the independent input–output pair law (a product of the marginals).
* `Real.sum_indep_channelTypicalPairs_le` — the packing bound: the jointly typical set has
  probability `≤ exp(-n(H(X:Y)-3ε))` under the independent pair law.
-/

@[expose] public section

open Finset

namespace Real

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### The joint input–output sequence law -/

/-- The **joint input–output sequence law** of `(Xⁿ, Yⁿ)` for a channel `q` fed an i.i.d. input
distribution `p`: the probability `(∏ⱼ p(xⱼ)) · ∏ⱼ q(yⱼ | xⱼ)` that the input string `x : Fin n → ι`
is drawn i.i.d. from `p` and the memoryless `n`-use channel produces the output string
`y : Fin n → κ`. -/
noncomputable def channelPairSeqProb (q : ι → κ → ℝ) (p : ι → ℝ) {n : ℕ}
    (xy : (Fin n → ι) × (Fin n → κ)) : ℝ :=
  (∏ j, p (xy.1 j)) * channelSeqProb q xy.1 xy.2

omit [Fintype ι] [Fintype κ] in
/-- The joint input–output sequence law evaluated at an explicit pair `(x, y)`. -/
@[simp] theorem channelPairSeqProb_mk (q : ι → κ → ℝ) (p : ι → ℝ) {n : ℕ}
    (x : Fin n → ι) (y : Fin n → κ) :
    channelPairSeqProb q p (x, y) = (∏ j, p (x j)) * channelSeqProb q x y := rfl

omit [Fintype ι] [Fintype κ] in
/-- The joint input–output sequence law is the `n`-fold i.i.d. product of the single-use joint law
`channelJoint q p` on `ι × κ`: `(∏ⱼ p(xⱼ)) · ∏ⱼ q(yⱼ | xⱼ) = ∏ⱼ channelJoint q p (xⱼ, yⱼ)`. -/
theorem channelPairSeqProb_eq_prod_channelJoint (q : ι → κ → ℝ) (p : ι → ℝ) {n : ℕ}
    (xy : (Fin n → ι) × (Fin n → κ)) :
    channelPairSeqProb q p xy = ∏ j, channelJoint q p (xy.1 j, xy.2 j) := by
  rw [channelPairSeqProb, channelSeqProb, ← Finset.prod_mul_distrib]
  simp only [channelJoint_apply]

omit [Fintype ι] in
/-- The joint input–output sequence law is nonnegative for a channel fed a nonnegative input
distribution. -/
theorem channelPairSeqProb_nonneg {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) {n : ℕ} (xy : (Fin n → ι) × (Fin n → κ)) :
    0 ≤ channelPairSeqProb q p xy :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => hp0 _)
    (Finset.prod_nonneg fun _ _ => hN.nonneg _ _)

omit [Fintype ι] in
/-- **The input marginal is the i.i.d. input law `pⁿ`.** Summing the joint sequence law over all
output strings leaves `∏ⱼ p(xⱼ)`: for a fixed input `x`, `∑_y ∏ⱼ q(yⱼ | xⱼ) = 1`
(`sum_channelSeqProb`). -/
theorem sum_snd_channelPairSeqProb {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ} {n : ℕ}
    (x : Fin n → ι) :
    ∑ y : Fin n → κ, channelPairSeqProb q p (x, y) = ∏ j, p (x j) := by
  simp_rw [channelPairSeqProb_mk, ← Finset.mul_sum, sum_channelSeqProb hN, mul_one]

omit [Fintype κ] in
/-- **The output marginal is the i.i.d. output law `(channelOutput q p)ⁿ`.** Summing the joint
sequence law over all input strings leaves `∏ⱼ (∑ₐ p(a) q(yⱼ | a)) = ∏ⱼ channelOutput q p (yⱼ)`, by
the product-marginalization `∑_x ∏ⱼ f j (xⱼ) = ∏ⱼ ∑ₐ f j a` (`Finset.prod_univ_sum`). -/
theorem sum_fst_channelPairSeqProb {q : ι → κ → ℝ} (p : ι → ℝ) {n : ℕ}
    (y : Fin n → κ) :
    ∑ x : Fin n → ι, channelPairSeqProb q p (x, y) = ∏ j, channelOutput q p (y j) := by
  have key : ∑ x : Fin n → ι, ∏ j, channelJoint q p (x j, y j)
      = ∏ j, ∑ a, channelJoint q p (a, y j) := by
    rw [← Fintype.piFinset_univ]
    exact (Finset.prod_univ_sum (fun _ => (univ : Finset ι))
      (fun j a => channelJoint q p (a, y j))).symm
  simp_rw [channelPairSeqProb_eq_prod_channelJoint]
  rw [key]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [channelJoint_apply, channelOutput_apply]

/-- The joint input–output sequence law is a probability distribution: its total mass is `1`. -/
theorem sum_channelPairSeqProb {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp1 : ∑ x, p x = 1) {n : ℕ} :
    ∑ xy : (Fin n → ι) × (Fin n → κ), channelPairSeqProb q p xy = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [sum_snd_channelPairSeqProb hN]
  rw [iid_total_mass, hp1, one_pow]

/-! ### The jointly typical set -/

open Classical in
/-- The **jointly typical set** of pairs `(x, y)` for a channel `q` fed input `p`, at block length
`n` and tolerance `ε`: those `(x, y)` for which the pair-sequence `j ↦ (xⱼ, yⱼ)` is `ε`-typical for
the joint law `channelJoint q p`, `x` is `ε`-typical for `p`, and `y` is `ε`-typical for the output
law `channelOutput q p`. The three-way conjunction (joint typicality together with both marginal
typicalities) is what the packing bound of the coding theorem requires. -/
noncomputable def channelTypicalPairs (q : ι → κ → ℝ) (p : ι → ℝ) (n : ℕ) (ε : ℝ) :
    Finset ((Fin n → ι) × (Fin n → κ)) :=
  univ.filter fun xy =>
    (fun j => (xy.1 j, xy.2 j)) ∈ typicalSeq (channelJoint q p) n ε ∧
      xy.1 ∈ typicalSeq p n ε ∧ xy.2 ∈ typicalSeq (channelOutput q p) n ε

/-- Membership in the jointly typical set: `(x, y)` is jointly typical iff the paired sequence is
typical for the joint law and both `x` and `y` are typical for their respective marginals. -/
theorem mem_channelTypicalPairs {q : ι → κ → ℝ} {p : ι → ℝ} {n : ℕ} {ε : ℝ}
    {xy : (Fin n → ι) × (Fin n → κ)} :
    xy ∈ channelTypicalPairs q p n ε ↔
      (fun j => (xy.1 j, xy.2 j)) ∈ typicalSeq (channelJoint q p) n ε ∧
        xy.1 ∈ typicalSeq p n ε ∧ xy.2 ∈ typicalSeq (channelOutput q p) n ε := by
  classical
  simp only [channelTypicalPairs, mem_filter, mem_univ, true_and]

/-! ### The joint asymptotic equipartition property -/

open Classical in
/-- Marginalizing the pair mass over pairs whose **input** string is typical for `p` reduces to the
i.i.d.-input typical mass `∑_{x ∈ T(p)} ∏ⱼ p(xⱼ)` (the condition depends only on `x`, so summing out
`y` via the input marginal `sum_snd_channelPairSeqProb` leaves the single-source typical mass). -/
private theorem sum_filter_fst_channelPairSeqProb {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    {n : ℕ} (ε : ℝ) :
    ∑ xy ∈ univ.filter (fun xy : (Fin n → ι) × (Fin n → κ) => xy.1 ∈ typicalSeq p n ε),
        channelPairSeqProb q p xy
      = ∑ x ∈ typicalSeq p n ε, ∏ j, p (x j) := by
  classical
  have hset : univ.filter (fun xy : (Fin n → ι) × (Fin n → κ) => xy.1 ∈ typicalSeq p n ε)
      = (typicalSeq p n ε) ×ˢ univ := by
    ext ⟨x, y⟩; simp
  rw [hset, Finset.sum_product]
  exact Finset.sum_congr rfl fun x _ => sum_snd_channelPairSeqProb hN x

open Classical in
/-- Marginalizing the pair mass over pairs whose **output** string is typical for the output law
reduces to the i.i.d.-output typical mass `∑_{y ∈ T(channelOutput q p)} ∏ⱼ channelOutput q p (yⱼ)`
(the condition depends only on `y`, so summing out `x` via the output marginal
`sum_fst_channelPairSeqProb` leaves the single-source typical mass). -/
private theorem sum_filter_snd_channelPairSeqProb (q : ι → κ → ℝ) (p : ι → ℝ) {n : ℕ} (ε : ℝ) :
    ∑ xy ∈ univ.filter
        (fun xy : (Fin n → ι) × (Fin n → κ) => xy.2 ∈ typicalSeq (channelOutput q p) n ε),
        channelPairSeqProb q p xy
      = ∑ y ∈ typicalSeq (channelOutput q p) n ε, ∏ j, channelOutput q p (y j) := by
  classical
  have hset : univ.filter
      (fun xy : (Fin n → ι) × (Fin n → κ) => xy.2 ∈ typicalSeq (channelOutput q p) n ε)
      = univ ×ˢ (typicalSeq (channelOutput q p) n ε) := by
    ext ⟨x, y⟩; simp
  rw [hset, Finset.sum_product, Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => sum_fst_channelPairSeqProb p y

open Classical in
/-- Marginalizing the pair mass over pairs whose paired sequence `j ↦ (xⱼ, yⱼ)` is typical for the
joint law reduces to the i.i.d.-joint typical mass for `channelJoint q p`. The pair type is
reindexed to `Fin n → ι × κ` by `Equiv.arrowProdEquivProdArrow`, under which the pair mass is the
i.i.d. product of the joint law (`channelPairSeqProb_eq_prod_channelJoint`). -/
private theorem sum_filter_pair_channelPairSeqProb (q : ι → κ → ℝ) (p : ι → ℝ) {n : ℕ} (ε : ℝ) :
    ∑ xy ∈ univ.filter (fun xy : (Fin n → ι) × (Fin n → κ) =>
        (fun j => (xy.1 j, xy.2 j)) ∈ typicalSeq (channelJoint q p) n ε),
        channelPairSeqProb q p xy
      = ∑ σ ∈ typicalSeq (channelJoint q p) n ε, ∏ j, channelJoint q p (σ j) := by
  classical
  rw [Finset.sum_filter,
    ← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ι) (fun _ => κ))]
  conv_rhs => rw [← Finset.filter_univ_mem (typicalSeq (channelJoint q p) n ε), Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hpair : (fun j => ((Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ι) (fun _ => κ) σ).1 j,
      (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ι) (fun _ => κ) σ).2 j)) = σ := by
    funext j; simp
  rw [hpair]
  split_ifs with h
  · rw [channelPairSeqProb_eq_prod_channelJoint]
    exact Finset.prod_congr rfl fun j _ => by simp
  · rfl

/-- A three-set union bound for a nonnegative summand: `∑_{A ∪ B ∪ C} f ≤ ∑_A f + ∑_B f + ∑_C f`. -/
private theorem sum_triple_union_le {α : Type*} [DecidableEq α] {f : α → ℝ} (hf : ∀ a, 0 ≤ f a)
    (A B C : Finset α) :
    ∑ a ∈ A ∪ B ∪ C, f a ≤ ∑ a ∈ A, f a + ∑ a ∈ B, f a + ∑ a ∈ C, f a := by
  have hAB : (∑ a ∈ A ∪ B, f a) + (∑ a ∈ A ∩ B, f a)
      = (∑ a ∈ A, f a) + (∑ a ∈ B, f a) := Finset.sum_union_inter
  have hAB2 : 0 ≤ ∑ a ∈ A ∩ B, f a := Finset.sum_nonneg fun a _ => hf a
  have hABC : (∑ a ∈ A ∪ B ∪ C, f a) + (∑ a ∈ (A ∪ B) ∩ C, f a)
      = (∑ a ∈ A ∪ B, f a) + (∑ a ∈ C, f a) := Finset.sum_union_inter
  have hABC2 : 0 ≤ ∑ a ∈ (A ∪ B) ∩ C, f a := Finset.sum_nonneg fun a _ => hf a
  linarith

/-- For a total-mass-`t` summand `f`, the complement of a set `P` whose mass is at least `t - c`
has mass at most `c`. -/
private theorem sum_filter_not_le_of_le {α : Type*} [Fintype α] {f : α → ℝ} {P : α → Prop}
    [DecidablePred P] {t c : ℝ} (htot : ∑ a, f a = t)
    (hle : t - c ≤ ∑ a ∈ univ.filter P, f a) :
    ∑ a ∈ univ.filter (fun a => ¬ P a), f a ≤ c := by
  have := Finset.sum_filter_add_sum_filter_not univ P f
  linarith

/-- **The joint asymptotic equipartition property (Nielsen & Chuang, joint AEP; Cover–Thomas, Thm.
7.6.1).** For a channel `q` fed an input distribution `p`, and any tolerance `ε > 0` and margin
`δ > 0`, for all sufficiently large block lengths `n` the jointly typical set carries probability at
least `1 − δ` under the joint input–output law:
`1 − δ ≤ ∑_{(x, y) ∈ channelTypicalPairs q p n ε} channelPairSeqProb q p (x, y)`.

The proof is a union bound over the three typicality events: the pair `(x, y)` fails to be jointly
typical only if its paired sequence, its input `x`, or its output `y` is atypical, and each of those
three atypical events has probability at most `δ / 3` for large `n` by the classical theorem of
typical sequences (`exists_le_sum_typicalSeq`) applied to `channelJoint q p`, `p` and
`channelOutput q p` respectively — using that the input, output and paired marginals of the joint
law are the corresponding i.i.d. products. -/
theorem exists_le_sum_channelTypicalPairs {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      1 - δ ≤ ∑ xy ∈ channelTypicalPairs q p n ε, channelPairSeqProb q p xy := by
  classical
  obtain ⟨N1, hN1pos, hN1⟩ := exists_le_sum_typicalSeq hp0 hp1 hε (by linarith : (0:ℝ) < δ / 3)
  obtain ⟨N2, hN2pos, hN2⟩ := exists_le_sum_typicalSeq (channelOutput_nonneg hN hp0)
    (sum_channelOutput hN hp1) hε (by linarith : (0:ℝ) < δ / 3)
  obtain ⟨N3, hN3pos, hN3⟩ := exists_le_sum_typicalSeq (channelJoint_nonneg hN hp0)
    (sum_channelJoint hN hp1) hε (by linarith : (0:ℝ) < δ / 3)
  refine ⟨max N1 (max N2 N3), lt_of_lt_of_le hN1pos (le_max_left _ _), fun n hn => ?_⟩
  have hn1 : N1 ≤ n := (le_max_left _ _).trans hn
  have hn2 : N2 ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn3 : N3 ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hf0 : ∀ xy : (Fin n → ι) × (Fin n → κ), 0 ≤ channelPairSeqProb q p xy :=
    fun xy => channelPairSeqProb_nonneg hN hp0 xy
  have hT : ∑ xy : (Fin n → ι) × (Fin n → κ), channelPairSeqProb q p xy = 1 :=
    sum_channelPairSeqProb hN hp1
  -- Abbreviations for the three typicality predicates and their filtered "bad" sets.
  set PC := fun xy : (Fin n → ι) × (Fin n → κ) =>
    (fun j => (xy.1 j, xy.2 j)) ∈ typicalSeq (channelJoint q p) n ε with hPC
  set PA := fun xy : (Fin n → ι) × (Fin n → κ) => xy.1 ∈ typicalSeq p n ε with hPA
  set PB := fun xy : (Fin n → ι) × (Fin n → κ) =>
    xy.2 ∈ typicalSeq (channelOutput q p) n ε with hPB
  -- Each atypical event has probability at most δ/3.
  have hbadA : ∑ xy ∈ univ.filter (fun xy => ¬ PA xy), channelPairSeqProb q p xy ≤ δ / 3 :=
    sum_filter_not_le_of_le hT (by rw [sum_filter_fst_channelPairSeqProb hN]; exact hN1 n hn1)
  have hbadB : ∑ xy ∈ univ.filter (fun xy => ¬ PB xy), channelPairSeqProb q p xy ≤ δ / 3 :=
    sum_filter_not_le_of_le hT (by rw [sum_filter_snd_channelPairSeqProb]; exact hN2 n hn2)
  have hbadC : ∑ xy ∈ univ.filter (fun xy => ¬ PC xy), channelPairSeqProb q p xy ≤ δ / 3 :=
    sum_filter_not_le_of_le hT (by rw [sum_filter_pair_channelPairSeqProb]; exact hN3 n hn3)
  -- The complement of the jointly typical set is contained in the union of the three bad sets.
  have hsub : univ \ channelTypicalPairs q p n ε ⊆
      (univ.filter (fun xy => ¬ PA xy)) ∪ (univ.filter (fun xy => ¬ PB xy))
        ∪ (univ.filter (fun xy => ¬ PC xy)) := by
    intro xy hxy
    rw [Finset.mem_sdiff, mem_channelTypicalPairs] at hxy
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  -- Assemble: the jointly typical mass is 1 minus the complement mass, which is at most δ.
  have hcompl : ∑ xy ∈ univ \ channelTypicalPairs q p n ε, channelPairSeqProb q p xy ≤ δ := by
    calc ∑ xy ∈ univ \ channelTypicalPairs q p n ε, channelPairSeqProb q p xy
        ≤ ∑ xy ∈ (univ.filter (fun xy => ¬ PA xy)) ∪ (univ.filter (fun xy => ¬ PB xy))
            ∪ (univ.filter (fun xy => ¬ PC xy)), channelPairSeqProb q p xy :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun xy _ _ => hf0 xy
      _ ≤ (∑ xy ∈ univ.filter (fun xy => ¬ PA xy), channelPairSeqProb q p xy)
            + (∑ xy ∈ univ.filter (fun xy => ¬ PB xy), channelPairSeqProb q p xy)
            + (∑ xy ∈ univ.filter (fun xy => ¬ PC xy), channelPairSeqProb q p xy) :=
          sum_triple_union_le hf0 _ _ _
      _ ≤ δ := by linarith
  have hpart : ∑ xy ∈ univ \ channelTypicalPairs q p n ε, channelPairSeqProb q p xy
      + ∑ xy ∈ channelTypicalPairs q p n ε, channelPairSeqProb q p xy = 1 := by
    rw [Finset.sum_sdiff (Finset.subset_univ _)]; exact hT
  linarith

/-! ### The packing / independence bound -/

/-- The **independent input–output pair law**: the probability
`(∏ⱼ p(xⱼ)) · ∏ⱼ channelOutput q p (yⱼ)` that an *independent* codeword `X̃ⁿ`, drawn i.i.d. from `p`
and statistically independent of the received output string `Yⁿ` (itself distributed as the i.i.d.
output law `(channelOutput q p)ⁿ`), equals `x` while the output equals `y`. It is the product of the
two marginals, in contrast with the true joint law `channelPairSeqProb q p` under which `X̃ⁿ` is the
input that produced `Yⁿ`; it is the measure under which the packing bound estimates the chance that
a wrong codeword looks jointly typical with the true output. -/
noncomputable def channelIndepPairProb (q : ι → κ → ℝ) (p : ι → ℝ) {n : ℕ}
    (xy : (Fin n → ι) × (Fin n → κ)) : ℝ :=
  (∏ j, p (xy.1 j)) * ∏ j, channelOutput q p (xy.2 j)

omit [Fintype κ] in
/-- The independent pair law evaluated at an explicit pair `(x, y)`. -/
@[simp] theorem channelIndepPairProb_mk (q : ι → κ → ℝ) (p : ι → ℝ) {n : ℕ}
    (x : Fin n → ι) (y : Fin n → κ) :
    channelIndepPairProb q p (x, y) = (∏ j, p (x j)) * ∏ j, channelOutput q p (y j) := rfl

open Classical in
/-- **The packing / independence bound** (Nielsen & Chuang, achievability of Theorem 12.7;
Cover–Thomas, Thm. 7.6.1). Under the *independent* pair law `channelIndepPairProb q p` — a codeword
`X̃ⁿ` drawn i.i.d. from `p`, independent of the output `Yⁿ ∼ (channelOutput q p)ⁿ` — the probability
that the pair is jointly typical is at most `exp (-n (H(X : Y) - 3ε))`:

`∑_{(x, y) ∈ channelTypicalPairs q p n ε} channelIndepPairProb q p (x, y)
  ≤ exp (-n (channelMutualInfo q p - 3ε))`.

This is the key estimate of the random-coding argument: a codeword statistically independent of the
received output is jointly typical with it only with exponentially small probability, so the
`exp (n R)` competing (wrong) codewords contribute a vanishing total decoding error whenever the
rate `R` is below the mutual information `H(X : Y)`.

The proof combines two per-element typicality bounds available on the jointly typical set — the
input factor `∏ⱼ p(xⱼ) ≤ exp (-n (H(X) - ε))` and the output factor
`∏ⱼ channelOutput q p (yⱼ) ≤ exp (-n (H(Y) - ε))` (the `mem_typicalSeq` upper bounds for `x`, `y`)
— with a count of the jointly typical pairs: the pair sequence `j ↦ (xⱼ, yⱼ)` is typical for the
joint law, so through the injection `(x, y) ↦ (j ↦ (xⱼ, yⱼ))` there are at most
`|T(channelJoint q p)| ≤ exp (n (H(X, Y) + ε))` of them (`card_typicalSeq_le`). Multiplying, the
exponent is `(H(X, Y) + ε) - (H(X) - ε) - (H(Y) - ε) = -((H(X) + H(Y) - H(X, Y)) - 3ε)`, which is
`-(H(X : Y) - 3ε)` by the three-entropy decomposition
`channelMutualInfo_eq_entropy_add_entropy_sub_entropy`. -/
theorem sum_indep_channelTypicalPairs_le {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) {n : ℕ} {ε : ℝ} :
    ∑ xy ∈ channelTypicalPairs q p n ε, channelIndepPairProb q p xy
      ≤ Real.exp (-(n : ℝ) * (channelMutualInfo q p - 3 * ε)) := by
  classical
  -- The constant per-pair upper bound `c₀ = exp(-n(H(X)-ε)) · exp(-n(H(Y)-ε))`.
  set c₀ := Real.exp (-(n : ℝ) * (entropy p - ε))
    * Real.exp (-(n : ℝ) * (entropy (channelOutput q p) - ε)) with hc₀
  have hc₀0 : 0 ≤ c₀ := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  -- (1) On the jointly typical set every summand is at most `c₀`, by the two marginal typicality
  -- upper bounds on `x` and `y`.
  have hsummand : ∀ xy ∈ channelTypicalPairs q p n ε, channelIndepPairProb q p xy ≤ c₀ := by
    intro xy hxy
    have hmem := mem_channelTypicalPairs.mp hxy
    have hx : ∏ j, p (xy.1 j) ≤ Real.exp (-(n : ℝ) * (entropy p - ε)) :=
      (mem_typicalSeq.mp hmem.2.1).2
    have hy : ∏ j, channelOutput q p (xy.2 j)
        ≤ Real.exp (-(n : ℝ) * (entropy (channelOutput q p) - ε)) :=
      (mem_typicalSeq.mp hmem.2.2).2
    have hynn : 0 ≤ ∏ j, channelOutput q p (xy.2 j) :=
      Finset.prod_nonneg fun j _ => channelOutput_nonneg hN hp0 _
    exact mul_le_mul hx hy hynn (Real.exp_pos _).le
  -- (2) The number of jointly typical pairs is at most `exp(n(H(X,Y)+ε))`: the pair map into the
  -- joint typical set is injective.
  have hAcard : ((channelTypicalPairs q p n ε).card : ℝ)
      ≤ Real.exp ((n : ℝ) * (entropy (channelJoint q p) + ε)) := by
    have hinj : (channelTypicalPairs q p n ε).card
        ≤ (typicalSeq (channelJoint q p) n ε).card := by
      -- the pair map `(x, y) ↦ (j ↦ (xⱼ, yⱼ))` is the inverse of `arrowProdEquivProdArrow`.
      apply Finset.card_le_card_of_injOn (fun xy => fun j => (xy.1 j, xy.2 j))
      · intro xy hxy
        exact (mem_channelTypicalPairs.mp hxy).1
      · exact (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ι) (fun _ => κ)).symm.injective.injOn
    calc ((channelTypicalPairs q p n ε).card : ℝ)
        ≤ ((typicalSeq (channelJoint q p) n ε).card : ℝ) := by exact_mod_cast hinj
      _ ≤ Real.exp ((n : ℝ) * (entropy (channelJoint q p) + ε)) :=
          card_typicalSeq_le (channelJoint_nonneg hN hp0) (sum_channelJoint hN hp1)
  -- (3) The three-entropy decomposition identifies the exponent with the mutual information.
  have hI : channelMutualInfo q p
      = entropy p + entropy (channelOutput q p) - entropy (channelJoint q p) :=
    channelMutualInfo_eq_entropy_add_entropy_sub_entropy hN p
  have hexp : Real.exp ((n : ℝ) * (entropy (channelJoint q p) + ε)) * c₀
      = Real.exp (-(n : ℝ) * (channelMutualInfo q p - 3 * ε)) := by
    rw [hc₀, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hI]; ring
  -- Assemble: bound each summand by `c₀`, count the pairs, and combine the exponentials.
  calc ∑ xy ∈ channelTypicalPairs q p n ε, channelIndepPairProb q p xy
      ≤ ∑ _xy ∈ channelTypicalPairs q p n ε, c₀ := Finset.sum_le_sum hsummand
    _ = ((channelTypicalPairs q p n ε).card : ℝ) * c₀ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp ((n : ℝ) * (entropy (channelJoint q p) + ε)) * c₀ :=
        mul_le_mul_of_nonneg_right hAcard hc₀0
    _ = Real.exp (-(n : ℝ) * (channelMutualInfo q p - 3 * ε)) := hexp

end Real
