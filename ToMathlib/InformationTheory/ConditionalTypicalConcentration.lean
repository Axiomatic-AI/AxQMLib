/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.ConditionalTypicalSequence

/-!
# Random-coding concentration for the conditional typical set (the eq. 12.76 expectation)

The theorem of typical sequences bounds, for a *fixed* i.i.d. source, the probability that a
length-`n` sequence is atypical (`Real.sum_typicalSeq_ge`,
`ToMathlib/InformationTheory/TypicalSequence.lean`). Nielsen and Chuang's proof of the
Holevo–Schumacher–Westmoreland theorem (Theorem 12.8, random-coding achievability) needs a
*two-level* variant: the codeword letters are themselves random. Alice draws a length-`n` codeword
`M : Fin n → α` with letters `Mᵢ` i.i.d. from an ensemble `p : α → ℝ`; each letter `a` carries a
conditional distribution `l a : β → ℝ` (in the quantum application, `l a` is the eigenvalue
distribution of the channel output `E(ρ_a)`). The codeword's *conditional* typical set is
`Real.condTypicalSeq (fun i ↦ l (Mᵢ)) s ε`, and N&C's Eq. 12.76 bounds the **random-coding
expectation** of the atypical weight,

`𝔼_M [ 1 − ∑_{κ ∈ T_M} ∏ᵢ l (Mᵢ) (κᵢ) ]  ≤  δ`.

## Main result

* `Real.sum_weighted_one_sub_condTypicalSeq_le` — with the threshold `s` equal to the
  ensemble-average conditional entropy `∑ₐ p a · H(l a)`, the `p`-weighted average over codewords of
  the conditional-atypical weight is at most `V / (n ε²)`, where
  `V = ∑ₐ p a · ∑_b l a b · (−log (l a b) − s)²` is the per-letter surprisal variance of the joint
  source. As `n → ∞` (with `ε` fixed) this tends to `0` — N&C's Eq. 12.76.

## Proof

The two-level average is a *single-level* deviation bound in disguise. The pairs `(Mᵢ, Kᵢ)` — a
letter and a conditional draw — are i.i.d. under the joint distribution `q (a, b) = p a · l a b` on
`α × β`; the conditional surprisal `g (a, b) = −log (l a b)` has `q`-mean exactly the threshold
`s = ∑ₐ p a · H(l a)`. The double sum `∑_M ∏ p · ∑_{κ ∉ T_M} ∏ l` reindexes, via
`Equiv.arrowProdEquivProdArrow`, to the `q`-mass of the joint deviation set `|(1/n)∑ᵢ g − s| > ε`,
which the finite Chebyshev engine `Real.iid_average_deviation_le`
(`ToMathlib/InformationTheory/IIDConcentration.lean`) bounds by `V / (n ε²)`. Off-support codewords
(`∏ l = 0`) contribute zero, so the multiplicative `condTypicalSeq` and the additive deviation set
agree in mass — the same support bookkeeping as `Real.sum_typicalSeq_ge`.
-/

@[expose] public section

open Finset

namespace Real

/-- **Reindexing the joint deviation mass.** For a predicate `pred` on `(letter, conditional-draw)`
sequence pairs, the `q`-mass over joint sequences `w : Fin n → α × β` (with
`q (a, b) = p a · l a b`) of the pairs whose split `(fun i ↦ (w i).1, fun i ↦ (w i).2)` satisfies
`pred` equals the two-level sum `∑_M ∑_{κ : pred M κ} (∏ p) · (∏ l)`. The
`Equiv.arrowProdEquivProdArrow` identity `(Fin n → α × β) ≃ (Fin n → α) × (Fin n → β)` splits the
joint sequence into a codeword `M` and a conditional sequence `κ`, and `∏ᵢ q (wᵢ)` factors as
`(∏ᵢ p (Mᵢ)) · (∏ᵢ l (Mᵢ) (κᵢ))`. -/
private lemma sum_filter_prod_pair_eq {α β : Type*} [Fintype α] [Fintype β] {n : ℕ}
    (p : α → ℝ) (l : α → β → ℝ) (pred : (Fin n → α) → (Fin n → β) → Prop)
    [∀ M, DecidablePred (pred M)] :
    ∑ w ∈ univ.filter (fun w : Fin n → α × β => pred (fun i => (w i).1) (fun i => (w i).2)),
        ∏ i, (p (w i).1 * l (w i).1 (w i).2)
      = ∑ M : Fin n → α, ∑ κ ∈ univ.filter (pred M), (∏ i, p (M i)) * ∏ i, l (M i) (κ i) := by
  classical
  rw [Finset.sum_filter,
    ← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => α) (fun _ => β)).symm,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun M _ => ?_)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun κ _ => ?_)
  simp only [Equiv.arrowProdEquivProdArrow_symm_apply]
  rw [Finset.prod_mul_distrib]

/-- **Random-coding concentration for the conditional typical set** (Nielsen & Chuang, Theorem 12.8,
Eq. 12.76). Letters are drawn from an ensemble `p : α → ℝ` and each letter `a` carries a conditional
distribution `l a : β → ℝ`. With the threshold `s` equal to the ensemble-average conditional entropy
`∑ₐ p a · H(l a)`, the `p`-weighted average over length-`n` codewords `M : Fin n → α` of the
conditional-atypical weight `1 − ∑_{κ ∈ T_M} ∏ᵢ l (Mᵢ) (κᵢ)` is at most `V / (n ε²)`, where
`V = ∑ₐ p a · ∑_b l a b · (−log (l a b) − s)²` is the per-letter surprisal variance of the joint
`(letter, draw)` source. As `n → ∞` (with `ε` fixed) the right side tends to `0`.

The pairs `(Mᵢ, Kᵢ)` are i.i.d. under `q (a, b) = p a · l a b`, and the conditional surprisal
`g (a, b) = −log (l a b)` has `q`-mean `s`; the two-level average is the `q`-mass of the joint
deviation set, bounded by the Chebyshev engine `Real.iid_average_deviation_le`. Off-support
codewords contribute zero, matching the additive deviation set to the multiplicative
`condTypicalSeq`. The random-coding twin of `Real.sum_typicalSeq_ge`. -/
theorem sum_weighted_one_sub_condTypicalSeq_le
    {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (l : α → β → ℝ) (hl0 : ∀ a b, 0 ≤ l a b) (hl1 : ∀ a, ∑ b, l a b = 1)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    {s : ℝ} (hs : s = ∑ a, p a * Real.entropy (l a)) :
    ∑ M : Fin n → α, (∏ i, p (M i)) *
        (1 - ∑ κ ∈ Real.condTypicalSeq (fun i => l (M i)) s ε, ∏ i, l (M i) (κ i))
      ≤ (∑ a, p a * ∑ b, l a b * (- Real.log (l a b) - s) ^ 2) / (n * ε ^ 2) := by
  classical
  -- The joint `(letter, draw)` source `q` and its conditional surprisal `g`.
  set q : α × β → ℝ := fun w => p w.1 * l w.1 w.2 with hq
  set g : α × β → ℝ := fun w => - Real.log (l w.1 w.2) with hgdef
  have hent : ∀ a, Real.entropy (l a) = ∑ b, l a b * (- Real.log (l a b)) := fun a => by
    rw [Real.entropy_eq_neg_sum_mul_log, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  have hq0 : ∀ w, 0 ≤ q w := fun w => mul_nonneg (hp0 _) (hl0 _ _)
  have hq1 : ∑ w, q w = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [hq, ← Finset.mul_sum, hl1, mul_one, hp1]
  -- The `q`-mean of `g` is the threshold `s`.
  have hm : s = ∑ w, q w * g w := by
    rw [Fintype.sum_prod_type, hs]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hent, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [hq, hgdef]; ring
  -- The joint per-letter variance is the stated `V`.
  have hV : (∑ w, q w * (g w - s) ^ 2)
      = ∑ a, p a * ∑ b, l a b * (- Real.log (l a b) - s) ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [hq, hgdef]; ring
  -- Chebyshev on the joint source, rewritten with `V`.
  have hdev := Real.iid_average_deviation_le q g hq0 hq1 hm hn hε
  rw [hV] at hdev
  refine le_trans ?_ hdev
  -- Reindex the joint deviation mass into the two-level codeword sum.
  set pred : (Fin n → α) → (Fin n → β) → Prop :=
    fun M κ => ε < |(∑ i, - Real.log (l (M i) (κ i))) / (n : ℝ) - s| with hpred
  have hreindex : ∑ w ∈ univ.filter (fun w : Fin n → α × β => ε < |(∑ i, g (w i)) / (n : ℝ) - s|),
        ∏ i, q (w i)
      = ∑ M : Fin n → α, ∑ κ ∈ univ.filter (pred M), (∏ i, p (M i)) * ∏ i, l (M i) (κ i) := by
    convert sum_filter_prod_pair_eq p l pred using 2
  rw [hreindex]
  -- Term by term over codewords `M`: the conditional-atypical weight is the atypical mass.
  refine Finset.sum_le_sum (fun M _ => ?_)
  have hone : ∑ κ : Fin n → β, ∏ i, l (M i) (κ i) = 1 := by
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
    simp only [hl1, Finset.prod_const_one]
  have heq : (1 : ℝ) - ∑ κ ∈ Real.condTypicalSeq (fun i => l (M i)) s ε, ∏ i, l (M i) (κ i)
      = ∑ κ ∈ univ \ Real.condTypicalSeq (fun i => l (M i)) s ε, ∏ i, l (M i) (κ i) := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _), hone]
  rw [heq, Finset.mul_sum, Finset.sdiff_eq_filter, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_le_sum (fun κ _ => ?_)
  have hpl_nn : 0 ≤ (∏ i, p (M i)) * ∏ i, l (M i) (κ i) :=
    mul_nonneg (Finset.prod_nonneg fun i _ => hp0 _) (Finset.prod_nonneg fun i _ => hl0 _ _)
  by_cases hT : κ ∈ Real.condTypicalSeq (fun i => l (M i)) s ε
  · rw [ite_eq_right (not_not.mpr hT)]
    split_ifs
    · exact hpl_nn
    · exact le_refl 0
  · rw [ite_eq_left hT]
    by_cases hpos : 0 < ∏ i, l (M i) (κ i)
    · -- On the support the multiplicative typicality is the additive deviation.
      have hn' : 0 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
      have hnotle : ¬ |(∑ i, - Real.log (l (M i) (κ i))) / (Fintype.card (Fin n) : ℝ) - s| ≤ ε :=
        fun hle => hT ((Real.mem_condTypicalSeq_iff_abs_le hn' hpos).mpr hle)
      have hpredκ : pred M κ := by
        rw [hpred]; rw [Fintype.card_fin] at hnotle; exact not_le.mp hnotle
      rw [ite_eq_left hpredκ]
    · -- Off the support the atypical mass is zero.
      have hz : ∏ i, l (M i) (κ i) = 0 :=
        le_antisymm (not_lt.mp hpos) (Finset.prod_nonneg fun i _ => hl0 _ _)
      rw [hz, mul_zero]
      split_ifs <;> exact le_refl 0

end Real
