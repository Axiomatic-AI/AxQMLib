/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.TypicalSequence

/-!
# Shannon's noiseless channel coding theorem (data compression)

For a finite alphabet `α` and an i.i.d. classical information source with probability mass function
`p : α → ℝ` (`0 ≤ p x`, `∑ x, p x = 1`), a **rate-`R` compression scheme** at block length `n`
compresses a source sequence `x : Fin n → α` into a bit string of length `⌊n R⌋` and decompresses
it back to a sequence. Following Nielsen & Chuang (p. 540) we model such a scheme as the structure

`Real.CompressionScheme α n numBits`,

bundling an `encode : (Fin n → α) → (Fin numBits → Bool)` (their `Cₙ`, mapping to a length-`numBits`
bit string) and a `decode : (Fin numBits → Bool) → (Fin n → α)` (their `Dₙ`), with the intended
`numBits = ⌊n R⌋` (`Nat.floor`, matching N&C's convention `nR := ⌊nR⌋`). Its

`sch.successProb p = ∑ {x : decode (encode x) = x}, ∏ i, p (x i)`

is the probability that the source sequence is recovered exactly, `p(Dₙ(Cₙ(x)) = x)`. A scheme
*family* `sch : (n : ℕ) → CompressionScheme α n ⌊n R⌋` is **reliable** when `sch.successProb p → 1`
as `n → ∞`, i.e. `Tendsto (fun n => (sch n).successProb p) atTop (𝓝 1)` — exactly N&C's criterion
that the recovery probability "approaches one".

**Theorem 12.4 (Shannon's noiseless channel coding theorem).** *For an i.i.d. source with entropy
rate `H(X)`: if `R > H(X)` a reliable rate-`R` compression scheme exists; conversely if `R < H(X)`
no rate-`R` scheme is reliable.*

## Units

`Real.entropy p` is the Shannon entropy in **nats** (natural logarithm), whereas N&C's rate `R` and
its `2^{nR}` bit strings are **base 2**. The threshold `H(X) < R` (both in bits) is therefore
written `entropy p < R * Real.log 2` (both in nats): a rate of `R` bits equals `R log 2` nats, and a
length-`⌊nR⌋` bit string encodes `2 ^ ⌊nR⌋ = exp (⌊nR⌋ log 2)` messages. No separate base-`2`
entropy notion is introduced.

## Main results (this file)

- `Real.CompressionScheme`: the encode/decode model of a rate-`R` scheme (Nielsen & Chuang, `Cₙ`,
  `Dₙ`).
- `Real.CompressionScheme.successProb`: the exact-recovery probability `p(Dₙ(Cₙ(x)) = x)`, with
  `successProb_nonneg` and `successProb_le_one` (it is a probability).
- `Real.exists_compressionScheme_sum_typicalSeq_le`: the achievability construction — whenever the
  `ε`-typical set fits in the compressed space (`|T(n, ε)| ≤ 2 ^ numBits`), there is a scheme whose
  success probability is at least the total probability `∑_{T(n,ε)} ∏ᵢ p` of the typical set
  (index the typical sequences into the bit strings; anything typical is recovered).
- `Real.exists_card_typicalSeq_le_two_pow`: for `H + ε < R log 2`, the typical set fits in the
  compressed space for all sufficiently large `n` (`|T(n, ε)| ≤ 2 ^ ⌊n R⌋`), from the Eq. 12.28
  upper bound `|T(n, ε)| ≤ exp (n (H + ε))`.
- `Real.exists_reliable_compressionScheme`: **Theorem 12.4, direct part.** If
  `entropy p < R log 2` then a reliable rate-`R` compression scheme family exists — its success
  probability tends to `1`.
- `Real.CompressionScheme.card_correctlyDecoded_le`: the counting core of the converse — a scheme's
  exactly-recovered set has at most `2 ^ numBits` members (`encode` is injective on it).
- `Real.CompressionScheme.successProb_tendsto_zero_of_lt`: **Theorem 12.4, converse
  (quantitative).** For a nonnegative bit-rate below the entropy, `0 ≤ R` and `entropy p > R log 2`,
  the success probability of *every* rate-`R` scheme family tends to `0`.
- `Real.not_reliable_compressionScheme`: **Theorem 12.4, converse.** Under the same hypotheses no
  rate-`R` scheme family is reliable (the success probability does not tend to `1`).

The converse builds on the small-set bound `Real.exists_sum_prod_le_of_card_le_exp` (Nielsen &
Chuang, Theorem 12.2 (3)): a rate-`R` scheme recovers at most `2 ^ ⌊n R⌋ ≤ exp (n (R log 2))`
sequences exactly, a set of vanishing total probability when `R log 2 < H`. The rate being
nonnegative (`0 ≤ R`) is part of what "rate" means and is genuinely needed — a deterministic source
with a negative "rate" would be a spurious counterexample.
-/

@[expose] public section

open Finset Filter Topology

namespace Real

variable {α : Type*} [Fintype α]

/-- A **rate-`R` compression scheme** for a length-`n` source over the alphabet `α`
(Nielsen & Chuang, p. 540): an `encode` (their `Cₙ`) mapping a source sequence `x : Fin n → α` to a
`numBits`-bit string, and a matching `decode` (their `Dₙ`) mapping bit strings back to sequences.
The intended block-length dependence is `numBits = ⌊n R⌋`, so the compressed space carries `⌊n R⌋`
bits per block. -/
structure CompressionScheme (α : Type*) (n numBits : ℕ) where
  /-- The compression map `Cₙ`: a source sequence is compressed to a `numBits`-bit string. -/
  encode : (Fin n → α) → (Fin numBits → Bool)
  /-- The decompression map `Dₙ`: a `numBits`-bit string is decompressed back to a source
  sequence. -/
  decode : (Fin numBits → Bool) → (Fin n → α)

open Classical in
/-- The **success probability** of a compression scheme under the i.i.d. product distribution `p`:
the total probability of the source sequences `x` that are recovered exactly,
`decode (encode x) = x`. This is Nielsen & Chuang's `p(Dₙ(Cₙ(x)) = x)`. -/
noncomputable def CompressionScheme.successProb (p : α → ℝ) {n numBits : ℕ}
    (sch : CompressionScheme α n numBits) : ℝ :=
  ∑ x ∈ univ.filter (fun x => sch.decode (sch.encode x) = x), ∏ i, p (x i)

/-- The success probability is nonnegative (it is a sum of products of probabilities). -/
theorem CompressionScheme.successProb_nonneg (p : α → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    {n numBits : ℕ} (sch : CompressionScheme α n numBits) : 0 ≤ sch.successProb p := by
  rw [CompressionScheme.successProb]
  exact Finset.sum_nonneg fun s _ => Finset.prod_nonneg fun i _ => hp0 _

/-- The success probability is at most `1`: the successfully-recovered sequences form a subset of
all sequences, whose total probability is `(∑ x, p x) ^ n = 1`. -/
theorem CompressionScheme.successProb_le_one (p : α → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) {n numBits : ℕ} (sch : CompressionScheme α n numBits) :
    sch.successProb p ≤ 1 := by
  classical
  have htotal : ∑ s : Fin n → α, ∏ i, p (s i) = 1 := by rw [iid_total_mass, hp1, one_pow]
  rw [CompressionScheme.successProb, ← htotal]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun s _ _ => Finset.prod_nonneg fun i _ => hp0 _)

/-- **Achievability construction.** If the `ε`-typical set fits into the compressed space, i.e.
`|T(n, ε)| ≤ 2 ^ numBits`, then there is a compression scheme whose success probability is at least
the total probability `∑_{T(n,ε)} ∏ᵢ p` of the typical set.

The typical sequences are injected into the `2 ^ numBits` bit strings (`encode`), and `decode`
inverts that injection (any non-image bit string decompresses to an arbitrary fixed guess); every
typical sequence is therefore recovered exactly, so the success set contains `T(n, ε)`. This is the
compression side of Nielsen & Chuang's scheme: store an index of the typical sequence, give up on
the atypical ones. -/
theorem exists_compressionScheme_sum_typicalSeq_le [Nonempty α] (p : α → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) {n numBits : ℕ} {ε : ℝ}
    (hcard : (typicalSeq p n ε).card ≤ 2 ^ numBits) :
    ∃ sch : CompressionScheme α n numBits,
      ∑ s ∈ typicalSeq p n ε, ∏ i, p (s i) ≤ sch.successProb p := by
  classical
  -- Index the typical sequences into the `2 ^ numBits` bit strings.
  obtain ⟨e⟩ : Nonempty ({x // x ∈ typicalSeq p n ε} ↪ (Fin numBits → Bool)) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    exact hcard
  -- A fixed fallback sequence for atypical inputs / non-image bit strings.
  let g0 : Fin n → α := Classical.arbitrary _
  let enc : (Fin n → α) → (Fin numBits → Bool) :=
    fun x => if h : x ∈ typicalSeq p n ε then e ⟨x, h⟩ else default
  let dec : (Fin numBits → Bool) → (Fin n → α) :=
    fun b => if h : ∃ a : {x // x ∈ typicalSeq p n ε}, e a = b then (h.choose).1 else g0
  refine ⟨⟨enc, dec⟩, ?_⟩
  -- Every typical sequence is recovered exactly, so `T(n, ε)` sits inside the success set.
  have hsub : typicalSeq p n ε ⊆ univ.filter (fun x => dec (enc x) = x) := by
    intro x hx
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have henc : enc x = e ⟨x, hx⟩ := dite_eq_left hx
    have hex : ∃ a : {x // x ∈ typicalSeq p n ε}, e a = e ⟨x, hx⟩ := ⟨⟨x, hx⟩, rfl⟩
    rw [henc, show dec (e ⟨x, hx⟩) = (hex.choose).1 from dite_eq_left hex]
    have hchoose : hex.choose = (⟨x, hx⟩ : {x // x ∈ typicalSeq p n ε}) :=
      e.injective hex.choose_spec
    rw [hchoose]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun s _ _ => Finset.prod_nonneg fun i _ => hp0 _)

/-- For a rate above the entropy (`H + ε < R log 2`), the `ε`-typical set fits into the compressed
space `2 ^ ⌊n R⌋` for all sufficiently large `n`: `|T(n, ε)| ≤ 2 ^ ⌊n R⌋`.

By the Eq. 12.28 upper bound `|T(n, ε)| ≤ exp (n (H + ε))`, and `2 ^ ⌊n R⌋ = exp (⌊n R⌋ log 2)`
with `⌊n R⌋ > n R - 1`; the gap `γ = R log 2 - (H + ε) > 0` makes `n (H + ε) < ⌊n R⌋ log 2` once
`n ≥ log 2 / γ`. -/
theorem exists_card_typicalSeq_le_two_pow (p : α → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) {ε R : ℝ} (hHR : entropy p + ε < R * Real.log 2) :
    ∃ N : ℕ, ∀ n ≥ N, (typicalSeq p n ε).card ≤ 2 ^ ⌊(n : ℝ) * R⌋₊ := by
  set H := entropy p
  set γ := R * Real.log 2 - (H + ε) with hγ
  have hγpos : 0 < γ := by rw [hγ]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.log 2 / γ)
  refine ⟨N, fun n hn => ?_⟩
  have hcard := card_typicalSeq_le hp0 hp1 (n := n) (ε := ε)
  have hnge : Real.log 2 / γ ≤ (n : ℝ) := le_trans hN (by exact_mod_cast hn)
  have hnγ : Real.log 2 ≤ (n : ℝ) * γ := by rw [div_le_iff₀ hγpos] at hnge; linarith
  have hfloor : (n : ℝ) * R - 1 < (⌊(n : ℝ) * R⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one ((n : ℝ) * R); linarith
  have hkey : (n : ℝ) * (H + ε) < (⌊(n : ℝ) * R⌋₊ : ℝ) * Real.log 2 := by
    have h1 := mul_lt_mul_of_pos_right hfloor hlog2
    nlinarith [hnγ]
  have hexp : Real.exp ((n : ℝ) * (H + ε)) < (2 : ℝ) ^ ⌊(n : ℝ) * R⌋₊ := by
    have h2 : (2 : ℝ) ^ ⌊(n : ℝ) * R⌋₊
        = Real.exp ((⌊(n : ℝ) * R⌋₊ : ℝ) * Real.log 2) := by
      rw [mul_comm, Real.exp_natCast_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [h2]; exact Real.exp_lt_exp.mpr hkey
  have hlt := lt_of_le_of_lt hcard hexp
  exact_mod_cast le_of_lt hlt

/-- **Nielsen & Chuang, Theorem 12.4 — direct part (achievability).** If the rate exceeds the
entropy rate, `entropy p < R * Real.log 2` (i.e. `R > H(X)` in bits), then a **reliable** rate-`R`
compression scheme family exists: a family `sch n : CompressionScheme α n ⌊n R⌋` whose success
probability tends to `1` as `n → ∞`.

Fix `ε = (R log 2 - H)/2 > 0`, so `H + ε < R log 2`. For large `n` the typical set fits in the
compressed space (`exists_card_typicalSeq_le_two_pow`), so the achievability construction
(`exists_compressionScheme_sum_typicalSeq_le`) yields a scheme whose success probability is at least
the typical mass `∑_{T(n,ε)} ∏ᵢ p ≥ 1 - V/(n ε²)` (Theorem 12.2 (1), `sum_typicalSeq_ge`); for
smaller `n` any scheme is used. Squeezing `1 - V/(n ε²) ≤ successProb ≤ 1` with `V/(n ε²) → 0` gives
the limit. -/
theorem exists_reliable_compressionScheme (p : α → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {R : ℝ} (hR : entropy p < R * Real.log 2) :
    ∃ sch : (n : ℕ) → CompressionScheme α n ⌊(n : ℝ) * R⌋₊,
      Tendsto (fun n => (sch n).successProb p) atTop (𝓝 1) := by
  classical
  have hne : Nonempty α := by
    rcases isEmpty_or_nonempty α with h | h
    · simp only [Finset.univ_eq_empty, Finset.sum_empty] at hp1; norm_num at hp1
    · exact h
  set ε := (R * Real.log 2 - entropy p) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hHε : entropy p + ε < R * Real.log 2 := by rw [hεdef]; linarith
  obtain ⟨Ncard, hNcard⟩ := exists_card_typicalSeq_le_two_pow p hp0 hp1 hHε
  -- Use the achievability construction where the typical set fits; any scheme otherwise.
  let sch : (n : ℕ) → CompressionScheme α n ⌊(n : ℝ) * R⌋₊ := fun n =>
    if h : (typicalSeq p n ε).card ≤ 2 ^ ⌊(n : ℝ) * R⌋₊
    then (exists_compressionScheme_sum_typicalSeq_le p hp0 h).choose
    else ⟨fun _ => default, fun _ => Classical.arbitrary _⟩
  refine ⟨sch, ?_⟩
  set V := ∑ x, p x * (-Real.log (p x) - entropy p) ^ 2 with hVdef
  have hlo : ∀ n ≥ max Ncard 1, 1 - V / (n * ε ^ 2) ≤ (sch n).successProb p := by
    intro n hn
    have hn1 : 0 < n := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hn)
    have hc : (typicalSeq p n ε).card ≤ 2 ^ ⌊(n : ℝ) * R⌋₊ :=
      hNcard n (le_trans (le_max_left _ _) hn)
    have hsucc : ∑ s ∈ typicalSeq p n ε, ∏ i, p (s i) ≤ (sch n).successProb p := by
      have hdef : sch n = (exists_compressionScheme_sum_typicalSeq_le p hp0 hc).choose :=
        dite_eq_left hc
      rw [hdef]; exact (exists_compressionScheme_sum_typicalSeq_le p hp0 hc).choose_spec
    have hquant := sum_typicalSeq_ge hp0 hp1 hn1 hεpos
    linarith
  have hhi : ∀ n, (sch n).successProb p ≤ 1 :=
    fun n => CompressionScheme.successProb_le_one p hp0 hp1 _
  have hlt : Tendsto (fun n : ℕ => 1 - V / (n * ε ^ 2)) atTop (𝓝 1) := by
    have hz : Tendsto (fun n : ℕ => V / (n * ε ^ 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (V / ε ^ 2) / n) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      apply h1.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      field_simp
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hz
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlt tendsto_const_nhds
    (eventually_atTop.mpr ⟨max Ncard 1, hlo⟩) (Eventually.of_forall hhi)

open Classical in
/-- **The counting core of the converse.** The set of source sequences a scheme recovers *exactly*
(`decode (encode x) = x`) has at most `2 ^ numBits` elements. Indeed `encode` is injective on this
set — if `encode x = encode y` for two exactly-recovered `x, y` then
`x = decode (encode x) = decode (encode y) = y` — and it maps into the `2 ^ numBits` bit strings
`Fin numBits → Bool`. So a scheme with a `numBits`-bit codeword can recover at most `2 ^ numBits`
sequences, however clever its `encode`/`decode`. -/
theorem CompressionScheme.card_correctlyDecoded_le {n numBits : ℕ}
    (sch : CompressionScheme α n numBits) :
    (univ.filter (fun x => sch.decode (sch.encode x) = x)).card ≤ 2 ^ numBits := by
  classical
  have hcard : (univ.filter (fun x => sch.decode (sch.encode x) = x)).card
      ≤ (univ : Finset (Fin numBits → Bool)).card :=
    Finset.card_le_card_of_injOn sch.encode (fun a _ => mem_univ _) (by
      intro x hx y hy hxy
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hx hy
      calc x = sch.decode (sch.encode x) := hx.symm
        _ = sch.decode (sch.encode y) := by rw [hxy]
        _ = y := hy)
  simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using hcard

/-- **Nielsen & Chuang, Theorem 12.4 — converse, quantitative form.** For a genuine nonnegative
bit-rate below the entropy rate — `0 ≤ R` and `R * Real.log 2 < entropy p` (i.e. `R < H(X)` in bits)
— the success probability of *every* rate-`R` compression scheme family tends to `0`.

A rate-`R` scheme recovers at most `2 ^ ⌊n R⌋` sequences exactly (`card_correctlyDecoded_le`), and
`2 ^ ⌊n R⌋ = exp (⌊n R⌋ log 2) ≤ exp (n (R log 2))` since `⌊n R⌋ ≤ n R` (`Nat.floor_le`, using
`0 ≤ R`). So its success probability is the total probability of a set of at most
`exp (n (R log 2))` sequences; because `R log 2 < H`, the small-set bound
`exists_sum_prod_le_of_card_le_exp` (Theorem 12.2 (3)) forces that mass eventually below any
`δ > 0`. With `successProb ≥ 0` this squeezes the success probability to `0`.

The hypothesis `0 ≤ R` is not a weakening — a rate is a number of bits per symbol and is nonnegative
by definition. It is genuinely needed: for a *deterministic* source (`H(X) = 0`) a "rate" `R < 0`
would satisfy `R log 2 < H` yet the single most-probable sequence is recovered with probability `1`,
so the claim fails without it. Once `0 ≤ R` and `R log 2 < H`, necessarily `H > 0`, so the source is
nondeterministic. -/
theorem CompressionScheme.successProb_tendsto_zero_of_lt (p : α → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : R * Real.log 2 < entropy p)
    (sch : (n : ℕ) → CompressionScheme α n ⌊(n : ℝ) * R⌋₊) :
    Tendsto (fun n => (sch n).successProb p) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N, hNpos, hN⟩ := exists_sum_prod_le_of_card_le_exp hp0 hp1 hR (half_pos hδ)
  refine ⟨N, fun n hn => ?_⟩
  -- The success set has at most `2 ^ ⌊n R⌋ ≤ exp (n (R log 2))` members.
  have hcardnat : (univ.filter (fun x => (sch n).decode ((sch n).encode x) = x)).card
      ≤ 2 ^ ⌊(n : ℝ) * R⌋₊ := (sch n).card_correctlyDecoded_le
  have hcard : ((univ.filter (fun x => (sch n).decode ((sch n).encode x) = x)).card : ℝ)
      ≤ Real.exp ((n : ℝ) * (R * Real.log 2)) := by
    have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    have hfloor : (⌊(n : ℝ) * R⌋₊ : ℝ) ≤ (n : ℝ) * R := Nat.floor_le (by positivity)
    calc ((univ.filter (fun x => (sch n).decode ((sch n).encode x) = x)).card : ℝ)
        ≤ ((2 : ℝ) ^ ⌊(n : ℝ) * R⌋₊) := by exact_mod_cast hcardnat
      _ = Real.exp ((⌊(n : ℝ) * R⌋₊ : ℝ) * Real.log 2) := by
          rw [mul_comm, Real.exp_natCast_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp ((n : ℝ) * (R * Real.log 2)) :=
          Real.exp_le_exp.mpr (by nlinarith [hfloor, hlog2])
  -- The small-set bound then caps the success probability by `δ / 2 < δ`.
  have hsucc : (sch n).successProb p ≤ δ / 2 := by
    rw [CompressionScheme.successProb]; exact hN n hn _ hcard
  have hnonneg : 0 ≤ (sch n).successProb p := (sch n).successProb_nonneg p hp0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith

/-- **Nielsen & Chuang, Theorem 12.4 — converse.** For a genuine nonnegative bit-rate below the
entropy rate — `0 ≤ R` and `R * Real.log 2 < entropy p` (i.e. `R < H(X)` in bits) — *no* rate-`R`
compression scheme family is **reliable**: the success probability does not tend to `1`, exactly
N&C's "any compression scheme will not be reliable".

Immediate from the quantitative converse `successProb_tendsto_zero_of_lt`: the success probability
tends to `0`, so by uniqueness of limits it cannot also tend to `1`. -/
theorem not_reliable_compressionScheme (p : α → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : R * Real.log 2 < entropy p)
    (sch : (n : ℕ) → CompressionScheme α n ⌊(n : ℝ) * R⌋₊) :
    ¬ Tendsto (fun n => (sch n).successProb p) atTop (𝓝 1) := by
  intro hreliable
  have hzero := CompressionScheme.successProb_tendsto_zero_of_lt p hp0 hp1 hR0 hR sch
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique hreliable hzero
  norm_num at h10

end Real
