/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.TypicalSequence
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Log

/-!
# Variable-length zero-error data compression (Nielsen & Chuang, Exercise 12.5)

Nielsen & Chuang's Exercise 12.5 asks to turn a *heuristic* variable-length compression scheme into
a rigorous argument: an i.i.d. source with entropy rate `H(X)` can be compressed to an **average of
`R` bits per source symbol, for any `R > H(X)`, with zero probability of error**. The heuristic:
encode a length-`n` block `x` by first testing whether it is `ε`-typical; if so send a short index
(`⌈log₂ |T(n, ε)|⌉` bits) into the typical set, otherwise send an uncompressed index
(`⌈log₂ dⁿ⌉` bits, `d = |α|`). A leading flag bit records which branch was taken, so the code is
losslessly (zero-error) decodable.

This file builds the **code itself** and proves its two structural properties — that it is
zero-error (injective) and what its codeword lengths are. The asymptotic expected-length bound
(`𝔼[len] / n ≤ R` for `R > H(X)` and large `n`) is a separate development building on these facts
and the theorem of typical sequences (`ToMathlib/InformationTheory/TypicalSequence.lean`).

The entropy convention is nats (natural log), matching `Real.entropy` and `Real.typicalSeq`;
Nielsen & Chuang's base-`2` "bits" are the same quantities rescaled by `log 2`. The codeword
lengths here are genuine bit counts (`List Bool` lengths), so the average length is measured in
bits and compared to `R` bits per symbol in the expected-length bound.

## Main definitions

- `Real.binBlockCode`: the reusable **fixed-length binary block code** — an injective map from any
  finite type of at most `2 ^ w` elements into the length-`w` binary strings `Fin w → Bool`.
- `Real.typicalWidth` / `Real.atypicalWidth`: the two codeword body widths `⌈log₂ |T(n, ε)|⌉` and
  `⌈log₂ dⁿ⌉` (via `Nat.clog`).
- `Real.typicalCode`: the variable-length encoder `(Fin n → α) → List Bool` of the heuristic.

## Main results

- `Real.typicalCode_length`: the codeword length is `typicalWidth + 1` on typical inputs and
  `atypicalWidth + 1` on atypical inputs (the `+ 1` is the flag bit).
- `Real.typicalCode_injective`: **zero probability of error** — the encoder is injective, so the
  decoder recovers every source block exactly.
-/

@[expose] public section

open Finset

namespace Real

variable {α : Type*} [Fintype α]

/-- **Fixed-length binary block code.** A finite type `β` with at most `2 ^ w` elements embeds
injectively into the length-`w` binary strings `Fin w → Bool` (there are `2 ^ w` of them). This is
the elementary combinatorial core of a block code: distinct source symbols receive distinct `w`-bit
codewords. Noncomputable, as it merely selects *some* injection via cardinality. -/
noncomputable def binBlockCode (β : Type*) [Fintype β] {w : ℕ}
    (h : Fintype.card β ≤ 2 ^ w) : β ↪ (Fin w → Bool) :=
  Classical.choice <| Function.Embedding.nonempty_iff_card_le.mpr <| by
    rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- The number of bits used to index the `ε`-typical sequences: `⌈log₂ |T(n, ε)|⌉`. -/
noncomputable def typicalWidth (p : α → ℝ) (n : ℕ) (ε : ℝ) : ℕ :=
  Nat.clog 2 (typicalSeq p n ε).card

/-- The number of bits used to index an arbitrary length-`n` sequence uncompressed: `⌈log₂ dⁿ⌉`,
where `d = |α|` is the alphabet size (`dⁿ = |α|ⁿ` is the number of length-`n` sequences). -/
noncomputable def atypicalWidth (α : Type*) [Fintype α] (n : ℕ) : ℕ :=
  Nat.clog 2 (Fintype.card (Fin n → α))

/-- The `ε`-typical set has at most `2 ^ typicalWidth` elements, so it embeds into
`typicalWidth`-bit codewords. -/
theorem card_typicalSeq_le_two_pow_typicalWidth (p : α → ℝ) (n : ℕ) (ε : ℝ) :
    Fintype.card (typicalSeq p n ε) ≤ 2 ^ typicalWidth p n ε := by
  rw [Fintype.card_coe, typicalWidth]
  exact Nat.le_pow_clog one_lt_two _

/-- There are at most `2 ^ atypicalWidth` length-`n` sequences, so they embed into
`atypicalWidth`-bit codewords. -/
theorem card_le_two_pow_atypicalWidth (n : ℕ) :
    Fintype.card (Fin n → α) ≤ 2 ^ atypicalWidth α n := by
  rw [atypicalWidth]
  exact Nat.le_pow_clog one_lt_two _

open Classical in
/-- **The variable-length zero-error compression code of Nielsen & Chuang, Exercise 12.5.** A
length-`n` block `x` is encoded as a leading flag bit followed by a fixed-length index:

* if `x` is `ε`-typical, the flag `false` followed by a `typicalWidth`-bit index into `T(n, ε)`;
* otherwise the flag `true` followed by an `atypicalWidth`-bit uncompressed index of `x`.

The flag bit lets the decoder tell the two branches apart, making the code losslessly decodable
(`typicalCode_injective`). Noncomputable, inheriting the block-code choice from `binBlockCode`. -/
noncomputable def typicalCode (p : α → ℝ) (n : ℕ) (ε : ℝ) (x : Fin n → α) : List Bool :=
  if h : x ∈ typicalSeq p n ε then
    false :: List.ofFn (binBlockCode _ (card_typicalSeq_le_two_pow_typicalWidth p n ε) ⟨x, h⟩)
  else
    true :: List.ofFn (binBlockCode _ (card_le_two_pow_atypicalWidth n) x)

open Classical in
/-- The codeword length of `typicalCode`: `typicalWidth + 1` bits on `ε`-typical inputs and
`atypicalWidth + 1` bits otherwise (the `+ 1` accounts for the leading flag bit). -/
theorem typicalCode_length (p : α → ℝ) (n : ℕ) (ε : ℝ) (x : Fin n → α) :
    (typicalCode p n ε x).length =
      if x ∈ typicalSeq p n ε then typicalWidth p n ε + 1 else atypicalWidth α n + 1 := by
  simp only [typicalCode]
  split_ifs with h <;> simp [List.length_ofFn]

open Classical in
/-- **Zero probability of error** (Nielsen & Chuang, Exercise 12.5). The encoder `typicalCode` is
injective: distinct source blocks receive distinct codewords, so a decoder recovers every block
exactly (`typicalCode` has an exact left inverse). The flag bit separates the typical and atypical
branches, and within each branch `binBlockCode` is injective. -/
theorem typicalCode_injective (p : α → ℝ) (n : ℕ) (ε : ℝ) :
    Function.Injective (typicalCode p n ε) := by
  intro x y hxy
  simp only [typicalCode] at hxy
  by_cases hx : x ∈ typicalSeq p n ε <;> by_cases hy : y ∈ typicalSeq p n ε
  · rw [dite_eq_left hx, dite_eq_left hy, List.cons.injEq] at hxy
    exact congrArg Subtype.val
      ((binBlockCode _ (card_typicalSeq_le_two_pow_typicalWidth p n ε)).injective
        (List.ofFn_injective hxy.2))
  · rw [dite_eq_left hx, dite_eq_right hy] at hxy; simp at hxy
  · rw [dite_eq_right hx, dite_eq_left hy] at hxy; simp at hxy
  · rw [dite_eq_right hx, dite_eq_right hy, List.cons.injEq] at hxy
    exact (binBlockCode _ (card_le_two_pow_atypicalWidth n)).injective
      (List.ofFn_injective hxy.2)

/-- **Integer bound on the uncompressed-index width.** Each of the `n` source symbols needs at most
`⌈log₂ d⌉` bits (`d = |α|` the alphabet size), so `atypicalWidth α n ≤ n · ⌈log₂ d⌉`. Proved by
`dⁿ ≤ (2 ^ ⌈log₂ d⌉)ⁿ = 2 ^ (n · ⌈log₂ d⌉)` and monotonicity of `Nat.clog`. -/
theorem atypicalWidth_le (n : ℕ) :
    atypicalWidth α n ≤ Nat.clog 2 (Fintype.card α) * n := by
  rw [atypicalWidth, Fintype.card_fun, Fintype.card_fin]
  calc Nat.clog 2 (Fintype.card α ^ n)
      ≤ Nat.clog 2 ((2 ^ Nat.clog 2 (Fintype.card α)) ^ n) :=
        Nat.clog_mono_right 2 (Nat.pow_le_pow_left (Nat.le_pow_clog one_lt_two _) n)
    _ = Nat.clog 2 (2 ^ (Nat.clog 2 (Fintype.card α) * n)) := by rw [← pow_mul]
    _ = Nat.clog 2 (Fintype.card α) * n := Nat.clog_pow 2 _ one_lt_two

/-- **Real bound on the typical-set index width.** The ceiling of the base-2 logarithm of the
typical-set size is at most `n(H+ε)/log 2 + 1`. Combining `Real.card_typicalSeq_le`
(`|T(n,ε)| ≤ exp(n(H+ε))`) with `2 ^ ⌈n(H+ε)/log 2⌉ ≥ exp(n(H+ε))` gives an integer `K` with
`|T| ≤ 2 ^ K`, whence `⌈log₂|T|⌉ ≤ K ≤ n(H+ε)/log 2 + 1`. The hypothesis `0 ≤ entropy p + ε`
(true whenever `ε ≥ 0`, since `entropy p ≥ 0`) keeps the ceiling argument nonnegative. -/
theorem typicalWidth_le {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (n : ℕ) {ε : ℝ}
    (hε : 0 ≤ entropy p + ε) :
    (typicalWidth p n ε : ℝ) ≤ ↑n * (entropy p + ε) / Real.log 2 + 1 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  set y : ℝ := ↑n * (entropy p + ε) / Real.log 2 with hy
  have hy0 : 0 ≤ y := by
    rw [hy]; exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hε) hlog2.le
  set K : ℕ := ⌈y⌉₊ with hK
  have hexp2K : (2 : ℝ) ^ K = Real.exp (↑K * Real.log 2) := by
    rw [Real.exp_natCast_mul, Real.exp_log (by positivity)]
  have hcardR : ((typicalSeq p n ε).card : ℝ) ≤ (2 : ℝ) ^ K := by
    refine le_trans (card_typicalSeq_le hp0 hp1) ?_
    rw [hexp2K]
    refine Real.exp_le_exp.mpr ?_
    have hKy : y ≤ (K : ℝ) := Nat.le_ceil y
    have hyl : y * Real.log 2 = ↑n * (entropy p + ε) := by rw [hy]; field_simp
    nlinarith [mul_le_mul_of_nonneg_right hKy hlog2.le]
  have hcard : (typicalSeq p n ε).card ≤ 2 ^ K := by exact_mod_cast hcardR
  have hwK : typicalWidth p n ε ≤ K := (Nat.clog_le_iff_le_pow one_lt_two).mpr hcard
  calc (typicalWidth p n ε : ℝ) ≤ (K : ℝ) := by exact_mod_cast hwK
    _ ≤ y + 1 := (Nat.ceil_lt_add_one hy0).le
    _ = ↑n * (entropy p + ε) / Real.log 2 + 1 := by rw [hy]

open Classical in
/-- **Nielsen & Chuang, Exercise 12.5 (variable-length zero-error data compression).** For any rate
`R` strictly above the base-2 entropy `H(X) = entropy p / log 2` — equivalently
`entropy p < log 2 · R` — there is a typical-set width `ε > 0` and a block length `N` such that for
all `n ≥ N` the variable-length code `typicalCode p n ε`

* is **injective**, hence decodable with **zero probability of error**, and
* compresses the i.i.d. source `p` to an average of at most `R` bits per source symbol:
  `∑ₓ pⁿ(x) · (len x) ≤ n · R`, where `pⁿ(x) = ∏ᵢ p(xᵢ)` is the i.i.d. block probability.

This turns Nielsen & Chuang's heuristic into a rigorous statement. Splitting the expected length
over the typical set `T(n,ε)` and its complement, the typical branch contributes
`(⌈log₂|T|⌉ + 1) · P(T) ≤ ⌈log₂|T|⌉ + 1 ≤ n(H+ε)/log 2 + 2` (using `P(T) ≤ 1` and the width bound),
while the atypical branch contributes `(⌈log₂ dⁿ⌉ + 1) · (1 - P(T)) ≤ (n·⌈log₂ d⌉ + 1) · δ` (using
`1 - P(T) ≤ δ` from the theorem of typical sequences). Choosing `ε := γ/2` and
`δ := γ / (2 log 2 (C+1))` with `γ := log 2 · R - entropy p > 0` and `C := ⌈log₂ d⌉` makes the
per-symbol rate `(H+ε)/log 2 + (C+1)δ` equal to `R`, so for `n` large the additive constants are
absorbed and the average length drops to `n · R`. -/
theorem exists_typicalCode_expectedLength_le {p : α → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {R : ℝ} (hR : entropy p < Real.log 2 * R) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      Function.Injective (typicalCode p n ε) ∧
        (∑ x, (∏ i, p (x i)) * ((typicalCode p n ε x).length : ℝ)) ≤ (n : ℝ) * R := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hp_le_one : ∀ x, p x ≤ 1 := fun x => by
    rw [← hp1]; exact Finset.single_le_sum (fun i _ => hp0 i) (Finset.mem_univ x)
  have hHnn : 0 ≤ entropy p := Real.entropy_nonneg hp0 hp_le_one
  set C : ℕ := Nat.clog 2 (Fintype.card α) with hCdef
  set γ : ℝ := Real.log 2 * R - entropy p with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  set ε : ℝ := γ / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  set δ : ℝ := γ / (2 * Real.log 2 * (↑C + 1)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos hγ (by positivity)
  refine ⟨ε, hεpos, ?_⟩
  -- The key algebraic identity: the per-symbol rate equals `R`.
  have hAval : (entropy p + ε) / Real.log 2 = R - (↑C + 1) * δ := by
    rw [hεdef, hδdef, hγdef]; field_simp; ring
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge ((2 + δ) / δ)
  obtain ⟨N₁, _, hN₁⟩ := exists_le_sum_typicalSeq hp0 hp1 hεpos hδpos
  refine ⟨max (max N₀ N₁) 1, Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), ?_⟩
  intro n hn
  rw [ge_iff_le, max_le_iff, max_le_iff] at hn
  obtain ⟨⟨hnN0, hnN1⟩, _⟩ := hn
  refine ⟨typicalCode_injective p n ε, ?_⟩
  have hqnn : ∀ x : Fin n → α, 0 ≤ ∏ i, p (x i) := fun x =>
    Finset.prod_nonneg fun i _ => hp0 (x i)
  -- The codeword length as a two-branch real quantity.
  have hlen : ∀ x, ((typicalCode p n ε x).length : ℝ)
      = if x ∈ typicalSeq p n ε then (↑(typicalWidth p n ε) + 1 : ℝ)
        else (↑(atypicalWidth α n) + 1 : ℝ) := by
    intro x; rw [typicalCode_length]; split_ifs <;> push_cast <;> ring
  -- The total i.i.d. mass is `1`.
  have htot : ∑ x : Fin n → α, (∏ i, p (x i)) = 1 := by rw [iid_total_mass, hp1, one_pow]
  set PT : ℝ := ∑ x ∈ typicalSeq p n ε, ∏ i, p (x i) with hPTdef
  have hcompl : ∑ x ∈ (typicalSeq p n ε)ᶜ, ∏ i, p (x i) = 1 - PT := by
    have h := Finset.sum_add_sum_compl (typicalSeq p n ε) (fun x => ∏ i, p (x i))
    rw [htot, ← hPTdef] at h; linarith
  -- Split the expected length over the typical set and its complement.
  have hsplit : (∑ x, (∏ i, p (x i)) * ((typicalCode p n ε x).length : ℝ))
      = PT * (↑(typicalWidth p n ε) + 1) + (1 - PT) * (↑(atypicalWidth α n) + 1) := by
    rw [← Finset.sum_add_sum_compl (typicalSeq p n ε)]
    congr 1
    · rw [hPTdef, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x hx => by rw [hlen x, ite_eq_left hx]
    · rw [← hcompl, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x hx => by rw [hlen x, ite_eq_right (Finset.mem_compl.mp hx)]
  -- Bounds on the typical mass.
  have hPTnn : 0 ≤ PT := Finset.sum_nonneg fun x _ => hqnn x
  have hcomplnn : 0 ≤ 1 - PT := by rw [← hcompl]; exact Finset.sum_nonneg fun x _ => hqnn x
  have hPT1 : PT ≤ 1 := by linarith
  have hPTδ : 1 - PT ≤ δ := by
    have := hN₁ n hnN1; rw [← hPTdef] at this; linarith
  -- Width bounds.
  have hwT : (↑(typicalWidth p n ε) : ℝ) ≤ ↑n * (entropy p + ε) / Real.log 2 + 1 :=
    typicalWidth_le hp0 hp1 n (by linarith)
  have hwA : (↑(atypicalWidth α n) : ℝ) ≤ ↑C * ↑n := by
    have h : atypicalWidth α n ≤ C * n := atypicalWidth_le n
    exact_mod_cast h
  -- Combine.
  have hbound1 : PT * (↑(typicalWidth p n ε) + 1) ≤ ↑n * (entropy p + ε) / Real.log 2 + 2 := by
    have h1 : PT * (↑(typicalWidth p n ε) + 1) ≤ ↑(typicalWidth p n ε) + 1 :=
      mul_le_of_le_one_left (by positivity) hPT1
    linarith
  have hbound2 : (1 - PT) * (↑(atypicalWidth α n) + 1) ≤ (↑C * ↑n + 1) * δ := by
    calc (1 - PT) * (↑(atypicalWidth α n) + 1)
        ≤ (1 - PT) * (↑C * ↑n + 1) := by
          apply mul_le_mul_of_nonneg_left _ hcomplnn; linarith
      _ ≤ δ * (↑C * ↑n + 1) := by
          apply mul_le_mul_of_nonneg_right hPTδ; positivity
      _ = (↑C * ↑n + 1) * δ := mul_comm _ _
  have hfin : ↑n * (entropy p + ε) / Real.log 2 + 2 + (↑C * ↑n + 1) * δ ≤ ↑n * R := by
    rw [mul_div_assoc, hAval]
    have hexpand : ↑n * (R - (↑C + 1) * δ) + 2 + (↑C * ↑n + 1) * δ
        = ↑n * R + (2 + δ - ↑n * δ) := by ring
    rw [hexpand]
    have hnδ : 2 + δ ≤ ↑n * δ :=
      (div_le_iff₀ hδpos).mp (le_trans hN₀ (by exact_mod_cast hnN0))
    linarith
  rw [hsplit]
  linarith [hbound1, hbound2, hfin]

end Real
