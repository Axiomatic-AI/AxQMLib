/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.TypicalSequence
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi

/-!
# Conditional typical sequences (typical sequences for a product of *distinct* distributions)

The theorem of typical sequences (`ToMathlib.InformationTheory.TypicalSequence`) concerns the i.i.d.
source: a single distribution `p : α → ℝ` repeated `n` times, with sequence probability
`∏ i, p (s i)`. Nielsen and Chuang's proof of the Holevo–Schumacher–Westmoreland theorem (Theorem
12.8, the random-coding argument) needs a variant in which each coordinate carries a **different**
distribution — the *conditional* typical set `T_M` of a product codeword
`σ_M = σ_{M₁} ⊗ ⋯ ⊗ σ_{Mₙ}`, whose factors are drawn from an ensemble and so are in general
distinct (N&C Eqs. 12.74–12.77).

Fix a finite index type `ι` (the coordinates, `n = |ι|`), a family of finite alphabets
`β : ι → Type` and a family of distributions `p : (i : ι) → β i → ℝ` (each `p i` a probability
distribution). For a threshold `s` and tolerance `ε`, a *dependent* sequence `κ : (i : ι) → β i` is
**`(s, ε)`-typical** when its product probability `∏ i, p i (κ i)` lies between `exp (-n (s + ε))`
and `exp (-n (s - ε))` — equivalently (on the support) when its per-coordinate empirical surprisal
`(∑ i, -log (p i (κ i))) / n` is within `ε` of `s` (N&C Eq. 12.75, with `s = S̄` the
ensemble-average entropy).

## Main definitions and results

* `Real.condTypicalSeq` — the conditional typical set `T(s, ε)` (N&C Eq. 12.75), the
  distinct-distribution generalisation of `Real.typicalSeq`.
* `Real.mem_condTypicalSeq` — its membership predicate (the multiplicative squeeze).
* `Real.mem_condTypicalSeq_iff_abs_le` — **Eq. 12.75.** On the support, typicality is the additive
  empirical-surprisal condition `|(∑ i, -log (p i (κ i)))/n - s| ≤ ε`.
* `Real.card_condTypicalSeq_le` — **the dimension bound** (N&C Eq. 12.77): `|T(s, ε)| ≤ exp (n (s +
  ε))`, for *every* `n` (a deterministic combinatorial bound, independent of the ensemble). Each
  typical sequence has probability at least `exp (-n (s + ε))`, and the sequences carry total mass
  at most `1` (the total mass being `∏ i, ∑ b, p i b = 1`), so `|T| · exp (-n (s + ε)) ≤ 1`.

This is the distinct-distribution twin of `Real.typicalSeq` / `Real.card_typicalSeq_le`; the
quantum wrapper (the conditional typical *subspace* projector `P_M` and `tr(P_M) ≤ exp(n(S̄+ε))`)
is `AxQM.State.condTypicalSubspaceProj` in `AxQM/Postulates/API`.
-/

@[expose] public section

open Finset

namespace Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]

open Classical in
/-- The **conditional typical set** `T(s, ε)` of a product of distinct per-coordinate distributions
`p : (i : ι) → β i → ℝ` (Nielsen & Chuang, Eq. 12.75, `n = |ι|`): the dependent sequences
`κ : (i : ι) → β i` whose product probability `∏ i, p i (κ i)` lies between `exp (-n (s + ε))` and
`exp (-n (s - ε))`. The lower bound being a positive exponential, this automatically excludes
zero-probability sequences. The distinct-distribution generalisation of `Real.typicalSeq` (which is
this set for a constant family `p i = p`, over `ι = Fin n`). -/
noncomputable def condTypicalSeq (p : (i : ι) → β i → ℝ) (s ε : ℝ) : Finset ((i : ι) → β i) :=
  univ.filter fun κ => Real.exp (-(Fintype.card ι : ℝ) * (s + ε)) ≤ ∏ i, p i (κ i) ∧
    ∏ i, p i (κ i) ≤ Real.exp (-(Fintype.card ι : ℝ) * (s - ε))

/-- Membership in the conditional typical set: `κ` is typical iff its product probability is
squeezed between `exp (-n (s + ε))` and `exp (-n (s - ε))`. -/
theorem mem_condTypicalSeq {p : (i : ι) → β i → ℝ} {s ε : ℝ} {κ : (i : ι) → β i} :
    κ ∈ condTypicalSeq p s ε ↔
      Real.exp (-(Fintype.card ι : ℝ) * (s + ε)) ≤ ∏ i, p i (κ i) ∧
      ∏ i, p i (κ i) ≤ Real.exp (-(Fintype.card ι : ℝ) * (s - ε)) := by
  simp only [condTypicalSeq, mem_filter, mem_univ, true_and]

/-- **Nielsen & Chuang, Eq. 12.75.** On the support of the product distribution
(`0 < ∏ i, p i (κ i)`, i.e. `p i (κ i) > 0` for all `i`), `κ` is `(s, ε)`-typical iff its
per-coordinate empirical surprisal `(∑ i, -log (p i (κ i))) / n` is within `ε` of the threshold `s`.
This is the equivalence between the multiplicative definition and N&C's additive reformulation,
valid precisely on the support (where `log (∏ i, p i (κ i)) = ∑ i, log (p i (κ i))`). -/
theorem mem_condTypicalSeq_iff_abs_le {p : (i : ι) → β i → ℝ} (hn : 0 < Fintype.card ι) {s ε : ℝ}
    {κ : (i : ι) → β i} (hpos : 0 < ∏ i, p i (κ i)) :
    κ ∈ condTypicalSeq p s ε ↔
      |(∑ i, -Real.log (p i (κ i))) / (Fintype.card ι : ℝ) - s| ≤ ε := by
  have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hne : ∀ i, p i (κ i) ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.mp hpos.ne') i (mem_univ i)
  have hsum : (∑ i, -Real.log (p i (κ i))) = -Real.log (∏ i, p i (κ i)) := by
    rw [Real.log_prod (fun x _ => hne x)]
    exact Finset.sum_neg_distrib _
  rw [mem_condTypicalSeq, ← Real.le_log_iff_exp_le hpos, ← Real.log_le_iff_le_exp hpos]
  set L := Real.log (∏ i, p i (κ i))
  rw [hsum]
  have hfrac : (-L) / (Fintype.card ι : ℝ) - s = (-L - s * Fintype.card ι) / Fintype.card ι := by
    field_simp
  rw [hfrac, abs_div, abs_of_pos hn0, div_le_iff₀ hn0, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-- **The dimension bound** (Nielsen & Chuang, Eq. 12.77): the number of `(s, ε)`-typical dependent
sequences satisfies `|T(s, ε)| ≤ exp (n (s + ε))`, for every `n = |ι|`. A deterministic
combinatorial bound — it needs only that each `p i` is a probability distribution, not that `s` is
any particular value. Each typical sequence has probability at least `exp (-n (s + ε))`, and the
typical sequences
carry total probability at most `1` (the total mass over *all* sequences being
`∑ κ, ∏ i, p i (κ i) = ∏ i, ∑ b, p i b = 1`), so `|T| · exp (-n (s + ε)) ≤ 1`. The
distinct-distribution generalisation of `Real.card_typicalSeq_le`. -/
theorem card_condTypicalSeq_le {p : (i : ι) → β i → ℝ} (hp0 : ∀ i b, 0 ≤ p i b)
    (hp1 : ∀ i, ∑ b, p i b = 1) (s ε : ℝ) :
    ((condTypicalSeq p s ε).card : ℝ) ≤ Real.exp ((Fintype.card ι : ℝ) * (s + ε)) := by
  have hnn : ∀ κ : (i : ι) → β i, (0 : ℝ) ≤ ∏ i, p i (κ i) :=
    fun κ => Finset.prod_nonneg fun i _ => hp0 i _
  -- Total mass over all sequences is `∏ i, ∑ b, p i b = 1`.
  have htotal : (∑ κ : (i : ι) → β i, ∏ i, p i (κ i)) = 1 := by
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
    simp only [hp1, Finset.prod_const_one]
  have hsum_le_one : ∑ κ ∈ condTypicalSeq p s ε, ∏ i, p i (κ i) ≤ 1 := by
    rw [← htotal]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun κ _ _ => hnn κ
  have hlb : ((condTypicalSeq p s ε).card : ℝ) * Real.exp (-(Fintype.card ι : ℝ) * (s + ε))
      ≤ ∑ κ ∈ condTypicalSeq p s ε, ∏ i, p i (κ i) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun κ hκ => (mem_condTypicalSeq.mp hκ).1
  have hexp : Real.exp (-(Fintype.card ι : ℝ) * (s + ε))
      = (Real.exp ((Fintype.card ι : ℝ) * (s + ε)))⁻¹ := by rw [neg_mul, Real.exp_neg]
  rw [hexp] at hlb
  have hcard :
      ((condTypicalSeq p s ε).card : ℝ) / Real.exp ((Fintype.card ι : ℝ) * (s + ε)) ≤ 1 := by
    rw [div_eq_mul_inv]; exact hlb.trans hsum_le_one
  rw [div_le_iff₀ (Real.exp_pos _)] at hcard
  simpa using hcard

end Real
