/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.ChannelTypicalSequence
public import ToMathlib.InformationTheory.RandomCodingExpectation

/-!
# The random codebook for Shannon's noisy channel coding theorem

The achievability half of Shannon's noisy channel coding theorem (Nielsen & Chuang, Theorem 12.7)
is proved by a *random coding* argument (Cover–Thomas, ch. 7.7): to show that a good `M`-message,
length-`n` code exists, one averages the decoding error over a **random codebook** in which every
codeword letter is drawn independently from the input distribution `p`, and shows the average error
is small. This file records the random-codebook law, the marginalization of an expectation over it,
and the resulting bound on the codebook-averaged decoding error — the probabilistic bookkeeping that
turns "expected error over codebooks" into the joint-AEP and packing estimates of
`ToMathlib.InformationTheory.ChannelTypicalSequence`.

A **codebook** is a map `C : Fin M → (Fin n → ι)` assigning to each of the `M` messages a length-`n`
input string. Drawing every letter `C m j` independently from `p` gives the codebook the product law

`Real.channelCodebookProb p C = ∏ₘ ∏ⱼ p (C m j)`,

a probability distribution on the codebook space (`Real.sum_channelCodebookProb`). The engine behind
every marginalization is the elementary identity `∑_C ∏ₘ g m (C m) = ∏ₘ ∑ₓ g m x` (the sum over a
function space of a product equals the product of the sums), available as the general lemma
`Real.sum_prod_apply_eq_prod_sum`. Its first consequence is the **single-codeword marginal**
`Real.sum_channelCodebookProb_mul_single`: the expectation over the random codebook of a quantity
depending on a *single* codeword `C k` collapses to an expectation over that one codeword drawn
i.i.d. from `p`,

`∑_C channelCodebookProb p C · F (C k) = ∑ₓ (∏ⱼ p (xⱼ)) · F x`,

because the other `M − 1` codewords each marginalize to total mass `1`. Applied to the transmitted
codeword, this reduces the "the true input–output pair is atypical" term of the random-coding error
analysis to the joint AEP (`Real.exists_le_sum_channelTypicalPairs`). Its two-codeword counterpart
`Real.sum_channelCodebookProb_mul_pair` (a specialization of the general
`Real.sum_pi_weight_mul_apply₂`) factorises an expectation depending on two *distinct* codewords
into the product of the two independent i.i.d. marginals.

## The joint-typicality decoder and the random-coding error bound

The random code decodes a received output string `y` by the **joint-typicality rule**
`Real.channelJointTypicalDecode`: return the *unique* message whose codeword is jointly typical with
`y` (else a fixed fallback message). The resulting `Real.ChannelCode` is
`Real.channelJointTypicalCode`. A decoding error for the sent message `m` implies either the true
pair `(C m, y)` is atypical or some competing codeword `C m'` (`m' ≠ m`) is jointly typical with `y`
(`Real.channelJointTypicalDecode_eq_of_unique`). Averaging over the random codebook and bounding the
two contributions by the joint AEP (a single-codeword marginal → `1 − typical mass`) and the packing
bound (two-codeword marginal → `channelIndepPairProb` mass
`≤ exp(-n(H(X:Y)-3ε))` per competing codeword) gives the **expected-error bound**

`Real.sum_channelCodebookProb_condErrorProb_le` (per message) and its message-average
`Real.channelRandomCode_expectedAvgError_le`:

`𝔼_C[avg error] ≤ (1 − ∑_{typ} channelPairSeqProb) + (M − 1) · exp(-n(H(X:Y) − 3ε))`.

Driving this bound to `0` for a rate below `H(X : Y)` (the `n → ∞` limit) is not done in this file,
which proves the exact per-`n` inequality.

## Main declarations

* `Real.channelCodebookProb` — the i.i.d. random-codebook law `∏ₘ ∏ⱼ p (C m j)`.
* `Real.sum_channelCodebookProb` — the codebook law is a probability distribution (total mass `1`).
* `Real.sum_channelCodebookProb_mul_single` — the single-codeword marginal of a codebook
  expectation.
* `Real.sum_channelCodebookProb_mul_pair` — the two-codeword (independence) marginal.
* `Real.channelJointTypicalDecode`, `Real.channelJointTypicalCode` — the joint-typicality decoder
  and the code it defines.
* `Real.channelJointTypicalDecode_eq_of_unique` — the decoder recovers the sent message when its
  codeword is the unique jointly-typical one.
* `Real.sum_channelCodebookProb_condErrorProb_le`,
  `Real.channelRandomCode_expectedAvgError_le` — the codebook-averaged decoding-error bound.
-/

@[expose] public section

open Finset

namespace Real

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### The random-codebook law -/

/-- The **i.i.d. random-codebook law**: the probability `∏ₘ ∏ⱼ p (C m j)` that a random codebook
`C : Fin M → (Fin n → ι)` — assigning to each of the `M` messages a length-`n` input codeword —
arises when every codeword letter `C m j` is drawn independently from the input distribution `p`.
This is the measure over which the random-coding argument averages the decoding error. -/
noncomputable def channelCodebookProb (p : ι → ℝ) {M n : ℕ} (C : Fin M → Fin n → ι) : ℝ :=
  ∏ m, ∏ j, p (C m j)

omit [Fintype ι] in
/-- The random-codebook law is nonnegative for a nonnegative input distribution. -/
theorem channelCodebookProb_nonneg {p : ι → ℝ} (hp0 : ∀ x, 0 ≤ p x) {M n : ℕ}
    (C : Fin M → Fin n → ι) : 0 ≤ channelCodebookProb p C :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => hp0 _

/-- The random-codebook law is a probability distribution: its total mass is `1`. Marginalizing each
of the `M` independent codewords via `sum_prod_apply_eq_prod_sum` leaves
`∏ₘ (∑ₓ ∏ⱼ p (xⱼ)) = ∏ₘ 1 = 1`, the `M`-fold product of the i.i.d. total mass `iid_total_mass`. -/
theorem sum_channelCodebookProb {p : ι → ℝ} (hp1 : ∑ x, p x = 1) {M n : ℕ} :
    ∑ C : Fin M → (Fin n → ι), channelCodebookProb p C = 1 := by
  simp_rw [channelCodebookProb]
  rw [sum_prod_apply_eq_prod_sum (fun (_ : Fin M) (x : Fin n → ι) => ∏ j, p (x j))]
  simp_rw [iid_total_mass, hp1, one_pow, Finset.prod_const_one]

/-- **The single-codeword marginal of a codebook expectation.** The expectation over the random
codebook of a quantity `F` depending on a single codeword `C k` reduces to the expectation over that
one codeword drawn i.i.d. from `p`:

`∑_C channelCodebookProb p C · F (C k) = ∑ₓ (∏ⱼ p (xⱼ)) · F x`.

The other `M − 1` codewords appear only through the codebook law, so each marginalizes to total
mass `1` and drops out (`Finset.prod_eq_single` over `sum_prod_apply_eq_prod_sum`). This is the
identity that, applied to the transmitted codeword, turns the "true pair is atypical" term of the
random-coding error into the joint AEP. -/
theorem sum_channelCodebookProb_mul_single {p : ι → ℝ} (hp1 : ∑ x, p x = 1) {M n : ℕ}
    (F : (Fin n → ι) → ℝ) (k : Fin M) :
    ∑ C : Fin M → (Fin n → ι), channelCodebookProb p C * F (C k)
      = ∑ x, (∏ j, p (x j)) * F x := by
  have hg : ∀ C : Fin M → (Fin n → ι),
      channelCodebookProb p C * F (C k)
        = ∏ m, (∏ j, p (C m j)) * (if m = k then F (C m) else 1) := by
    intro C
    rw [channelCodebookProb, Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  simp_rw [hg]
  rw [sum_prod_apply_eq_prod_sum
      (fun (m : Fin M) (x : Fin n → ι) => (∏ j, p (x j)) * (if m = k then F x else 1)),
    Finset.prod_eq_single k]
  · simp
  · intro m _ hmk
    simp only [ite_eq_right hmk, mul_one]
    rw [iid_total_mass, hp1, one_pow]
  · intro hk
    exact absurd (mem_univ k) hk

open Classical in
/-- Re-fold a doubly-indexed sum over the fibres of a pair-Finset `s` into a single sum over `s`:
`∑ₓ ∑_{y : (x, y) ∈ s} g (x, y) = ∑_{xy ∈ s} g xy`. The bookkeeping identity used to combine the
per-input-string sums of the random-coding error analysis into sums over the jointly typical set. -/
private theorem sum_pair_filter_fold {n : ℕ} (g : (Fin n → ι) × (Fin n → κ) → ℝ)
    (s : Finset ((Fin n → ι) × (Fin n → κ))) :
    ∑ x, ∑ y ∈ univ.filter (fun y => (x, y) ∈ s), g (x, y) = ∑ xy ∈ s, g xy := by
  classical
  conv_rhs => rw [← Finset.filter_univ_mem s, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_filter]

/-- **The two-codeword (independence) marginal of a codebook expectation.** For two *distinct*
messages `k ≠ l`, the expectation over the random codebook of a quantity `F` depending on the two
codewords `C k` and `C l` factorises over the two independent codewords, each drawn i.i.d. from `p`:

`∑_C channelCodebookProb p C · F (C k) (C l) = ∑ₐ ∑_b (∏ⱼ p (aⱼ)) · (∏ⱼ p (bⱼ)) · F a b`.

The remaining `M − 2` codewords each marginalize to total mass `1`; this is the specialization of
the general `sum_pi_weight_mul_apply₂` to the i.i.d. weight `W x = ∏ⱼ p (xⱼ)` (whose total mass is
`1` by `iid_total_mass`). Applied to the transmitted and a competing codeword, it turns the "a wrong
codeword looks jointly typical" term of the random-coding error into the packing bound. -/
theorem sum_channelCodebookProb_mul_pair {p : ι → ℝ} (hp1 : ∑ x, p x = 1) {M n : ℕ}
    (F : (Fin n → ι) → (Fin n → ι) → ℝ) {k l : Fin M} (hkl : k ≠ l) :
    ∑ C : Fin M → (Fin n → ι), channelCodebookProb p C * F (C k) (C l)
      = ∑ a, ∑ b, (∏ j, p (a j)) * (∏ j, p (b j)) * F a b := by
  have hW : ∑ x : Fin n → ι, ∏ j, p (x j) = 1 := by rw [iid_total_mass, hp1, one_pow]
  simpa only [channelCodebookProb] using
    sum_pi_weight_mul_apply₂ (fun x => ∏ j, p (x j)) hW F hkl

/-! ### The joint-typicality decoder and its code -/

open Classical in
/-- The **joint-typicality decoder** for a codebook `C : Fin M → (Fin n → ι)` at block length `n`
and tolerance `ε` (Cover–Thomas, ch. 7.7). On receiving the output string `y`, it decodes to the
*unique* message `m` whose codeword `C m` is jointly typical with `y`
(`(C m, y) ∈ channelTypicalPairs`); if there is no such message, or more than one, it declares a
decoding failure by returning the fallback message `m₀`. -/
noncomputable def channelJointTypicalDecode (q : ι → κ → ℝ) (p : ι → ℝ) (n : ℕ) (ε : ℝ) {M : ℕ}
    (m₀ : Fin M) (C : Fin M → Fin n → ι) (y : Fin n → κ) : Fin M :=
  if h : ∃ m, (C m, y) ∈ channelTypicalPairs q p n ε ∧
      ∀ m', (C m', y) ∈ channelTypicalPairs q p n ε → m' = m
  then h.choose else m₀

/-- The **joint-typicality random code** built from a codebook `C`: it encodes message `m` as the
codeword `C m` and decodes by the joint-typicality rule `channelJointTypicalDecode` (fallback
message `m₀`). This is the code whose codebook-averaged decoding error the random-coding argument
bounds. -/
noncomputable def channelJointTypicalCode (q : ι → κ → ℝ) (p : ι → ℝ) (n : ℕ) (ε : ℝ) {M : ℕ}
    (m₀ : Fin M) (C : Fin M → Fin n → ι) : ChannelCode ι κ n M where
  encode := C
  decode := channelJointTypicalDecode q p n ε m₀ C

open Classical in
/-- **Correctness of the joint-typicality decoder.** If the received output `y` makes the sent
codeword `C m` jointly typical and leaves *no other* codeword jointly typical with `y`, the decoder
recovers `m`. Contrapositively, a decoding error for message `m` forces either the true pair
`(C m, y)` to be atypical or some competing codeword `C m'` (`m' ≠ m`) to be jointly typical with
`y` — the union-bound decomposition of the error event. -/
theorem channelJointTypicalDecode_eq_of_unique {q : ι → κ → ℝ} {p : ι → ℝ} {n : ℕ} {ε : ℝ}
    {M : ℕ} (m₀ : Fin M) {C : Fin M → Fin n → ι} {y : Fin n → κ} {m : Fin M}
    (hm : (C m, y) ∈ channelTypicalPairs q p n ε)
    (huniq : ∀ m', m' ≠ m → (C m', y) ∉ channelTypicalPairs q p n ε) :
    channelJointTypicalDecode q p n ε m₀ C y = m := by
  have hex : ∃ m'', (C m'', y) ∈ channelTypicalPairs q p n ε ∧
      ∀ m', (C m', y) ∈ channelTypicalPairs q p n ε → m' = m'' :=
    ⟨m, hm, fun m' hm' => by by_contra hne; exact huniq m' hne hm'⟩
  unfold channelJointTypicalDecode
  rw [dite_eq_left hex]
  exact (hex.choose_spec.2 m hm).symm

/-! ### The codebook-averaged decoding-error bound -/

open Classical in
/-- **The expected confusion term.** For a competing message `m' ≠ m`, the expectation over the
random codebook of the probability that the (independent) codeword `C m'` looks jointly typical with
the output produced by the sent codeword `C m` is bounded by the packing exponent
`exp(-n (H(X:Y) − 3ε))`. The two-codeword marginal factorises the expectation into the independent
input–output pair law `channelIndepPairProb`, then the packing bound
`sum_indep_channelTypicalPairs_le` closes it. -/
private theorem sum_channelCodebookProb_confusion_le {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) {n : ℕ} {ε : ℝ} {M : ℕ} {m m' : Fin M}
    (hmm' : m' ≠ m) :
    ∑ C : Fin M → (Fin n → ι), channelCodebookProb p C *
        ∑ y ∈ univ.filter (fun y => (C m', y) ∈ channelTypicalPairs q p n ε),
          channelSeqProb q (C m) y
      ≤ Real.exp (-(n : ℝ) * (channelMutualInfo q p - 3 * ε)) := by
  have key : ∑ C : Fin M → (Fin n → ι), channelCodebookProb p C *
      ∑ y ∈ univ.filter (fun y => (C m', y) ∈ channelTypicalPairs q p n ε), channelSeqProb q (C m) y
      = ∑ xy ∈ channelTypicalPairs q p n ε, channelIndepPairProb q p xy := by
    rw [sum_channelCodebookProb_mul_pair hp1
        (fun a b => ∑ y ∈ univ.filter (fun y => (a, y) ∈ channelTypicalPairs q p n ε),
          channelSeqProb q b y) hmm']
    have step : ∀ a : Fin n → ι,
        ∑ b, (∏ j, p (a j)) * (∏ j, p (b j)) *
          ∑ y ∈ univ.filter (fun y => (a, y) ∈ channelTypicalPairs q p n ε), channelSeqProb q b y
        = ∑ y ∈ univ.filter (fun y => (a, y) ∈ channelTypicalPairs q p n ε),
            channelIndepPairProb q p (a, y) := by
      intro a
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [channelIndepPairProb_mk, ← sum_fst_channelPairSeqProb p y, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [channelPairSeqProb_mk]; ring
    simp_rw [step]
    exact sum_pair_filter_fold (channelIndepPairProb q p) (channelTypicalPairs q p n ε)
  rw [key]
  exact sum_indep_channelTypicalPairs_le hN hp0 hp1

open Classical in
/-- **The expected true-atypical term.** The expectation over the random codebook of the probability
that the true input–output pair `(C m, Y)` is *atypical* equals `1 − (typical mass)`, the joint-AEP
complement. The single-codeword marginal collapses it onto the joint sequence law
`channelPairSeqProb`, whose total mass is `1`. -/
private theorem sum_channelCodebookProb_trueAtypical {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp1 : ∑ x, p x = 1) {n : ℕ} {ε : ℝ} {M : ℕ} (m : Fin M) :
    ∑ C : Fin M → (Fin n → ι), channelCodebookProb p C *
        ∑ y ∈ univ.filter (fun y => (C m, y) ∉ channelTypicalPairs q p n ε),
          channelSeqProb q (C m) y
      = 1 - ∑ xy ∈ channelTypicalPairs q p n ε, channelPairSeqProb q p xy := by
  rw [sum_channelCodebookProb_mul_single hp1
      (fun x => ∑ y ∈ univ.filter (fun y => (x, y) ∉ channelTypicalPairs q p n ε),
        channelSeqProb q x y) m]
  have hsplit : ∀ x : Fin n → ι,
      ∑ y ∈ univ.filter (fun y => (x, y) ∉ channelTypicalPairs q p n ε), channelSeqProb q x y
      = 1 - ∑ y ∈ univ.filter (fun y => (x, y) ∈ channelTypicalPairs q p n ε),
          channelSeqProb q x y := by
    intro x
    have h := Finset.sum_filter_add_sum_filter_not univ
      (fun y => (x, y) ∈ channelTypicalPairs q p n ε) (channelSeqProb q x)
    rw [sum_channelSeqProb hN x] at h
    linarith
  simp_rw [hsplit, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [iid_total_mass, hp1, one_pow]
  · simp_rw [Finset.mul_sum]
    rw [← sum_pair_filter_fold (channelPairSeqProb q p) (channelTypicalPairs q p n ε)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [channelPairSeqProb_mk]

/-- **The codebook-averaged conditional decoding-error bound, per message.** For each message `m`,
the expectation over the random codebook of the conditional block-error probability of the
joint-typicality code is bounded by the joint-AEP complement plus `M − 1` competing-codeword packing
terms:

`∑_C channelCodebookProb p C · condErrorProb (channelJointTypicalCode … m₀ C) m
  ≤ (1 − ∑_{typ} channelPairSeqProb) + (M − 1) · exp(-n (H(X:Y) − 3ε))`.

The decoding-error event `{y | decode y ≠ m}` is contained in the "true pair atypical" event union
the `M − 1` "competing codeword jointly typical" events
(`channelJointTypicalDecode_eq_of_unique`); averaging over codebooks bounds the first term by
`sum_channelCodebookProb_trueAtypical` (single marginal) and each competing term by
`sum_channelCodebookProb_confusion_le` (two-codeword marginal + packing). -/
theorem sum_channelCodebookProb_condErrorProb_le {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) {n : ℕ} {ε : ℝ} {M : ℕ} (m₀ m : Fin M) :
    ∑ C : Fin M → (Fin n → ι), channelCodebookProb p C *
        (channelJointTypicalCode q p n ε m₀ C).condErrorProb q m
      ≤ (1 - ∑ xy ∈ channelTypicalPairs q p n ε, channelPairSeqProb q p xy)
        + ((M : ℝ) - 1) * Real.exp (-(n : ℝ) * (channelMutualInfo q p - 3 * ε)) := by
  classical
  have hpt : ∀ C : Fin M → (Fin n → ι),
      (channelJointTypicalCode q p n ε m₀ C).condErrorProb q m
      ≤ (∑ y ∈ univ.filter (fun y => (C m, y) ∉ channelTypicalPairs q p n ε),
            channelSeqProb q (C m) y)
        + ∑ m' ∈ univ.filter (fun m' => m' ≠ m),
            ∑ y ∈ univ.filter (fun y => (C m', y) ∈ channelTypicalPairs q p n ε),
              channelSeqProb q (C m) y := by
    intro C
    have hnn : ∀ y, 0 ≤ channelSeqProb q (C m) y := fun y => channelSeqProb_nonneg hN _ _
    have hce : (channelJointTypicalCode q p n ε m₀ C).condErrorProb q m
        = ∑ y ∈ univ.filter (fun y => channelJointTypicalDecode q p n ε m₀ C y ≠ m),
            channelSeqProb q (C m) y := rfl
    rw [hce]
    have hsub : univ.filter (fun y => channelJointTypicalDecode q p n ε m₀ C y ≠ m)
        ⊆ univ.filter (fun y => (C m, y) ∉ channelTypicalPairs q p n ε)
          ∪ univ.filter (fun y => ∃ m', m' ≠ m ∧ (C m', y) ∈ channelTypicalPairs q p n ε) := by
      intro y hy
      simp only [mem_filter, mem_univ, true_and, mem_union] at hy ⊢
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨h1, h2⟩ := hcon
      exact hy (channelJointTypicalDecode_eq_of_unique m₀ (not_not.mp h1)
        (fun m' hne hin => h2 ⟨m', hne, hin⟩))
    calc ∑ y ∈ univ.filter (fun y => channelJointTypicalDecode q p n ε m₀ C y ≠ m),
            channelSeqProb q (C m) y
        ≤ ∑ y ∈ univ.filter (fun y => (C m, y) ∉ channelTypicalPairs q p n ε)
              ∪ univ.filter (fun y => ∃ m', m' ≠ m ∧ (C m', y) ∈ channelTypicalPairs q p n ε),
            channelSeqProb q (C m) y :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => hnn y)
      _ ≤ (∑ y ∈ univ.filter (fun y => (C m, y) ∉ channelTypicalPairs q p n ε),
              channelSeqProb q (C m) y)
            + ∑ y ∈ univ.filter (fun y => ∃ m', m' ≠ m ∧ (C m', y) ∈ channelTypicalPairs q p n ε),
                channelSeqProb q (C m) y := by
          have hui := Finset.sum_union_inter
            (s₁ := univ.filter (fun y => (C m, y) ∉ channelTypicalPairs q p n ε))
            (s₂ := univ.filter (fun y => ∃ m', m' ≠ m ∧ (C m', y) ∈ channelTypicalPairs q p n ε))
            (f := channelSeqProb q (C m))
          have hnn2 : 0 ≤ ∑ y ∈ (univ.filter (fun y => (C m, y) ∉ channelTypicalPairs q p n ε))
              ∩ univ.filter (fun y => ∃ m', m' ≠ m ∧ (C m', y) ∈ channelTypicalPairs q p n ε),
              channelSeqProb q (C m) y :=
            Finset.sum_nonneg fun y _ => hnn y
          linarith
      _ ≤ (∑ y ∈ univ.filter (fun y => (C m, y) ∉ channelTypicalPairs q p n ε),
              channelSeqProb q (C m) y)
            + ∑ m' ∈ univ.filter (fun m' => m' ≠ m),
                ∑ y ∈ univ.filter (fun y => (C m', y) ∈ channelTypicalPairs q p n ε),
                  channelSeqProb q (C m) y := by
          gcongr
          have hR : ∀ m' : Fin M,
              ∑ y ∈ univ.filter (fun y => (C m', y) ∈ channelTypicalPairs q p n ε),
                channelSeqProb q (C m) y
              = ∑ y, if (C m', y) ∈ channelTypicalPairs q p n ε then channelSeqProb q (C m) y
                  else 0 := fun m' => Finset.sum_filter _ _
          simp_rw [hR]
          rw [Finset.sum_filter, Finset.sum_comm]
          refine Finset.sum_le_sum fun y _ => ?_
          have hnn0 : ∀ i : Fin M,
              0 ≤ if (C i, y) ∈ channelTypicalPairs q p n ε then channelSeqProb q (C m) y else 0 :=
            fun i => by split_ifs <;> first | exact hnn y | exact le_rfl
          by_cases h : ∃ m', m' ≠ m ∧ (C m', y) ∈ channelTypicalPairs q p n ε
          · rw [ite_eq_left h]
            obtain ⟨m', hm'ne, hm'Q⟩ := h
            have hmem : m' ∈ univ.filter (fun m'' : Fin M => m'' ≠ m) :=
              Finset.mem_filter.mpr ⟨mem_univ m', hm'ne⟩
            have hterm := Finset.single_le_sum
              (f := fun i => if (C i, y) ∈ channelTypicalPairs q p n ε
                then channelSeqProb q (C m) y else 0)
              (fun i _ => hnn0 i) hmem
            rwa [ite_eq_left hm'Q] at hterm
          · rw [ite_eq_right h]
            exact Finset.sum_nonneg fun m'' _ => hnn0 m''
  calc ∑ C, channelCodebookProb p C * (channelJointTypicalCode q p n ε m₀ C).condErrorProb q m
      ≤ ∑ C, channelCodebookProb p C *
          ((∑ y ∈ univ.filter (fun y => (C m, y) ∉ channelTypicalPairs q p n ε),
              channelSeqProb q (C m) y)
            + ∑ m' ∈ univ.filter (fun m' => m' ≠ m),
                ∑ y ∈ univ.filter (fun y => (C m', y) ∈ channelTypicalPairs q p n ε),
                  channelSeqProb q (C m) y) :=
        Finset.sum_le_sum fun C _ =>
          mul_le_mul_of_nonneg_left (hpt C) (channelCodebookProb_nonneg hp0 C)
    _ = (∑ C, channelCodebookProb p C *
            ∑ y ∈ univ.filter (fun y => (C m, y) ∉ channelTypicalPairs q p n ε),
              channelSeqProb q (C m) y)
          + ∑ m' ∈ univ.filter (fun m' => m' ≠ m),
              ∑ C, channelCodebookProb p C *
                ∑ y ∈ univ.filter (fun y => (C m', y) ∈ channelTypicalPairs q p n ε),
                  channelSeqProb q (C m) y := by
        simp_rw [mul_add, Finset.mul_sum]
        rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ (1 - ∑ xy ∈ channelTypicalPairs q p n ε, channelPairSeqProb q p xy)
          + ((M : ℝ) - 1) * Real.exp (-(n : ℝ) * (channelMutualInfo q p - 3 * ε)) := by
        gcongr ?_ + ?_
        · exact le_of_eq (sum_channelCodebookProb_trueAtypical hN hp1 m)
        · calc ∑ m' ∈ univ.filter (fun m' => m' ≠ m),
                  ∑ C, channelCodebookProb p C *
                    ∑ y ∈ univ.filter (fun y => (C m', y) ∈ channelTypicalPairs q p n ε),
                      channelSeqProb q (C m) y
              ≤ ∑ _m' ∈ univ.filter (fun m' => m' ≠ m),
                  Real.exp (-(n : ℝ) * (channelMutualInfo q p - 3 * ε)) :=
                Finset.sum_le_sum fun m' hm' =>
                  sum_channelCodebookProb_confusion_le hN hp0 hp1 (Finset.mem_filter.mp hm').2
            _ = ((M : ℝ) - 1) * Real.exp (-(n : ℝ) * (channelMutualInfo q p - 3 * ε)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
                congr 1
                rw [Finset.filter_ne', Finset.card_erase_of_mem (mem_univ m),
                  Finset.card_univ, Fintype.card_fin, Nat.cast_sub (m.pos), Nat.cast_one]

/-- **The codebook-averaged decoding-error bound (message-average form).** Averaging the per-message
bound `sum_channelCodebookProb_condErrorProb_le` over the `M` messages, the expectation over the
random codebook of the *average* decoding error of the joint-typicality code satisfies

`∑_C channelCodebookProb p C · (M⁻¹ ∑ₘ condErrorProb (channelJointTypicalCode … m₀ C) m)
  ≤ (1 − ∑_{typ} channelPairSeqProb) + (M − 1) · exp(-n (H(X:Y) − 3ε))`.

This is the exact per-`n` inequality of the random-coding argument: the first term vanishes by the
joint AEP and, for a rate `R` with `R · log 2 < H(X : Y)`, the second vanishes as `n → ∞`, so a good
code exists — the achievability half of Theorem 12.7. -/
theorem channelRandomCode_expectedAvgError_le {q : ι → κ → ℝ} (hN : IsChannel q) {p : ι → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) {n : ℕ} {ε : ℝ} {M : ℕ} (m₀ : Fin M) :
    ∑ C : Fin M → (Fin n → ι), channelCodebookProb p C *
        ((M : ℝ)⁻¹ * ∑ m, (channelJointTypicalCode q p n ε m₀ C).condErrorProb q m)
      ≤ (1 - ∑ xy ∈ channelTypicalPairs q p n ε, channelPairSeqProb q p xy)
        + ((M : ℝ) - 1) * Real.exp (-(n : ℝ) * (channelMutualInfo q p - 3 * ε)) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast m₀.pos
  have hrw : ∑ C : Fin M → (Fin n → ι), channelCodebookProb p C *
        ((M : ℝ)⁻¹ * ∑ m, (channelJointTypicalCode q p n ε m₀ C).condErrorProb q m)
      = (M : ℝ)⁻¹ * ∑ m, ∑ C, channelCodebookProb p C *
          (channelJointTypicalCode q p n ε m₀ C).condErrorProb q m := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun C _ => by ring
  rw [hrw]
  calc (M : ℝ)⁻¹ * ∑ m, ∑ C, channelCodebookProb p C *
          (channelJointTypicalCode q p n ε m₀ C).condErrorProb q m
      ≤ (M : ℝ)⁻¹ * ∑ _m : Fin M,
          ((1 - ∑ xy ∈ channelTypicalPairs q p n ε, channelPairSeqProb q p xy)
            + ((M : ℝ) - 1) * Real.exp (-(n : ℝ) * (channelMutualInfo q p - 3 * ε))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun m _ =>
          sum_channelCodebookProb_condErrorProb_le hN hp0 hp1 m₀ m
    _ = (1 - ∑ xy ∈ channelTypicalPairs q p n ε, channelPairSeqProb q p xy)
          + ((M : ℝ) - 1) * Real.exp (-(n : ℝ) * (channelMutualInfo q p - 3 * ε)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (ne_of_gt hMR), one_mul]

end Real
