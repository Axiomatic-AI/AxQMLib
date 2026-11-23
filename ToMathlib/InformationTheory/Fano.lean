/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.JointEntropy
public import ToMathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Fano's inequality

For finite types `ι`, `κ` and a joint distribution `p : ι × κ → ℝ` of a pair of random variables
`(X, Y)` (`0 ≤ p` and `∑ p = 1`), suppose we try to infer `X` from `Y` by a guess `X̃ = g Y` for
some `g : κ → ι`. Let

`Real.fanoErrorProb p g = p(X ≠ g Y) = 1 − ∑_y p (g y, y)`

be the probability the guess is wrong. **Fano's inequality** (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Box 12.2 on p. 536, eq. (12.16)) bounds the conditional
entropy `H(X | Y)` in terms of this error probability and the alphabet size `|ι|`:

`H(X | Y) ≤ H(pₑ) + pₑ · log (|ι| − 1)`,

where `H(·)` is the binary entropy (`Real.binEntropy`). Equivalently, the right-hand side is the
`|ι|`-ary entropy `Real.qaryEntropy |ι| pₑ`. Qualitatively: if `H(X | Y)` is large then the error
probability `pₑ` must also be large — knowledge of `Y` can only pin down `X` as well as its
residual conditional entropy allows.

## Main declarations

* `Real.fanoErrorProb` — the error probability `p(X ≠ g Y)` of the guess `X̃ = g Y`, with
  `Real.fanoErrorProb_nonneg` and `Real.fanoErrorProb_le_one`.
* `Real.condEntropy_le_binEntropy_add_mul_log` — Fano's inequality in the form of N&C eq. (12.16):
  `H(X | Y) ≤ binEntropy pₑ + pₑ · log (|ι| − 1)`.
* `Real.condEntropy_le_qaryEntropy` — the same bound packaged as the `|ι|`-ary entropy of `pₑ`.

## Context

This is pure classical information theory, a statement about `Real.condEntropy`, `Real.entropy`
and `Real.binEntropy`, built on the joint-entropy and binary-entropy developments. It is the
classical prerequisite for the
converse of Shannon's noisy channel coding theorem (N&C Theorem 12.7,
`ToMathlib/InformationTheory/NoisyChannel.lean`) and for the quantum Fano inequality (N&C Theorem
12.9).

Entropies are in *nats* (natural logarithm), as elsewhere in the library; N&C measures the binary
entropy `H(pₑ)` and `log (|ι| − 1)` in bits. The inequality is base-independent (both sides scale by
the same `log 2` factor when converting), so this is a faithful reformulation, not a weakening.

## Proof

Rather than N&C's chain-rule argument (which introduces an auxiliary error random variable), the
proof here is a single application of Gibbs' inequality
(`Real.entropy_le_cross_entropy_of_sum_le`) to the joint `p` against the comparison distribution

`qd (x, y) = p_Y(y) · (if x = g y then 1 − pₑ else pₑ / (|ι| − 1))`,

whose per-`y` conditional puts mass `1 − pₑ` on the guess `g y` and spreads `pₑ` over the other
`|ι| − 1` symbols. The cross-entropy `−∑ p log qd` telescopes to
`H(Y) + binEntropy pₑ + pₑ log(|ι|−1)`, and subtracting `H(Y)` yields the bound. The only division
is by the *constant* `|ι| − 1`, so no
conditioning on `p_Y(y) = 0` is needed.

The lemma `Real.entropy_le_qaryEntropy` is the *single-distribution* kernel `H(r) ≤ qaryEntropy |ι|
(1 − r i₀)`; its docstring suggests obtaining Fano by averaging that per-symbol bound over the
conditioning variable `Y`. That averaging route is deliberately not taken here: the library has no
`condEntropy p = ∑_y p_Y(y) · H(X | Y = y)` decomposition to average against, and supplying one
means dividing each conditional by `p_Y(y)` (with its `p_Y(y) = 0` edge cases and a Jensen
step). The direct Gibbs route above avoids that machinery and divides only by the constant
`|ι| − 1`, so it is both shorter and division-safe.
-/

@[expose] public section

namespace Real

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The **Fano error probability** of guessing the first coordinate `X` of a joint distribution
`p : ι × κ → ℝ` from the second coordinate `Y` via a guess function `g : κ → ι`: the probability
`p(X ≠ g Y) = 1 − ∑_y p (g y, y)` that the guess `X̃ = g Y` is incorrect. -/
noncomputable def fanoErrorProb (p : ι × κ → ℝ) (g : κ → ι) : ℝ := 1 - ∑ y, p (g y, y)

omit [Fintype ι] in
/-- The Fano error probability is at most `1`. -/
theorem fanoErrorProb_le_one {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (g : κ → ι) :
    fanoErrorProb p g ≤ 1 := by
  have : 0 ≤ ∑ y, p (g y, y) := Finset.sum_nonneg fun y _ => hp _
  rw [fanoErrorProb]; linarith

/-- The Fano error probability is nonnegative (the correct-guess probability `∑_y p (g y, y)` is at
most the total mass `1`). -/
theorem fanoErrorProb_nonneg {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) (g : κ → ι) :
    0 ≤ fanoErrorProb p g := by
  have h1 : ∑ y, p (g y, y) ≤ ∑ y, marginalSnd p y :=
    Finset.sum_le_sum fun y _ => le_marginalSnd hp (g y) y
  rw [sum_marginalSnd, hsum] at h1
  rw [fanoErrorProb]; linarith

/-- A joint distribution `p : ι × κ → ℝ` of total mass `1` forces its first alphabet to be
nonempty: `1 ≤ Fintype.card ι`. (An empty `ι` empties the joint sum `∑ q, p q`, contradicting
`∑ q, p q = 1`.) The shared kernel of the `|ι| ≥ 1` step in the Fano bounds below, so
`Nonempty ι` need not be assumed. -/
private theorem one_le_card_of_sum_eq_one {p : ι × κ → ℝ} (hsum : ∑ q, p q = 1) :
    1 ≤ Fintype.card ι := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h
    rw [Fintype.sum_prod_type, Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact absurd hsum (by norm_num)
  · exact h

/-- **Fano's inequality** (Nielsen & Chuang, Box 12.2 on p. 536, eq. (12.16)). If we guess the
first coordinate `X` of a joint distribution `p : ι × κ → ℝ` from the second coordinate `Y` via
`X̃ = g Y`, with error probability `pₑ = Real.fanoErrorProb p g = p(X ≠ g Y)`, then the conditional
entropy is bounded by

`H(X | Y) ≤ binEntropy pₑ + pₑ · log (|ι| − 1)`.

Thus a large conditional entropy forces a large error probability. -/
theorem condEntropy_le_binEntropy_add_mul_log
    {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) (g : κ → ι) :
    condEntropy p ≤ binEntropy (fanoErrorProb p g)
      + fanoErrorProb p g * Real.log ((Fintype.card ι : ℝ) - 1) := by
  classical
  have hpe_nonneg := fanoErrorProb_nonneg hp hsum g
  have hpe_le_one := fanoErrorProb_le_one hp g
  have hcorrect : ∑ y, p (g y, y) = 1 - fanoErrorProb p g := by simp only [fanoErrorProb]; ring
  set pe := fanoErrorProb p g with hpe_def
  set c : ℝ := (Fintype.card ι : ℝ) - 1 with hc_def
  -- `ι` is nonempty (hence `c = |ι| − 1 ≥ 0`), so `Nonempty ι` need not be assumed.
  have hcp : 1 ≤ Fintype.card ι := one_le_card_of_sum_eq_one hsum
  have hcard1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcp
  have hc_nonneg : 0 ≤ c := by rw [hc_def]; linarith
  -- Edge fact: `c = 0` (i.e. `|ι| = 1`) forces `pe = 0` (the sole symbol is always guessed right).
  have hc0 : c = 0 → pe = 0 := by
    intro hc
    have hcard_eq : Fintype.card ι = 1 := by
      have h1 : (Fintype.card ι : ℝ) = 1 := by rw [hc_def] at hc; linarith
      exact_mod_cast h1
    have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcard_eq.le
    have hdiag : ∀ z, p (g z, z) = marginalSnd p z := by
      intro z
      rw [marginalSnd_apply]
      refine (Fintype.sum_eq_single (f := fun x => p (x, z)) (g z) ?_).symm
      intro x hx
      exact absurd (Subsingleton.elim x (g z)) hx
    have hsum1 : ∑ z, p (g z, z) = 1 := by simp_rw [hdiag]; rw [sum_marginalSnd, hsum]
    rw [hpe_def]; simp only [fanoErrorProb]; rw [hsum1]; ring
  -- The comparison distribution.
  set r : ι × κ → ℝ := fun xy => if xy.1 = g xy.2 then 1 - pe else pe / c with hr_def
  set qd : ι × κ → ℝ := fun xy => marginalSnd p xy.2 * r xy with hqd_def
  have hr_nonneg : ∀ xy, 0 ≤ r xy := by
    rintro ⟨x, y⟩; simp only [hr_def]; split_ifs
    · linarith
    · exact div_nonneg hpe_nonneg hc_nonneg
  have hqd_nonneg : ∀ xy, 0 ≤ qd xy := by
    rintro ⟨x, y⟩; simp only [hqd_def]
    exact mul_nonneg (marginalSnd_nonneg hp _) (hr_nonneg _)
  -- Support condition: `qd (x, y) = 0 → p (x, y) = 0`.
  have hsupp : ∀ xy, qd xy = 0 → p xy = 0 := by
    rintro ⟨x, y⟩ hq0
    rcases eq_or_ne (marginalSnd p y) 0 with hms | hms
    · have hle' := le_marginalSnd hp x y
      rw [hms] at hle'
      exact le_antisymm hle' (hp _)
    · have hr0 : r (x, y) = 0 := by
        have hq' : marginalSnd p y * r (x, y) = 0 := by simp only [hqd_def] at hq0; exact hq0
        rcases mul_eq_zero.mp hq' with h | h
        · exact absurd h hms
        · exact h
      simp only [hr_def] at hr0
      split_ifs at hr0 with hx
      · -- `x = g y`, so `1 − pe = 0`, i.e. `pe = 1`: no correct guess has positive mass.
        have hpe1 : pe = 1 := by linarith
        have hz : ∑ z, p (g z, z) = 0 := by rw [hcorrect, hpe1]; ring
        have hgy := (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hp (g z, z)).mp hz y
          (Finset.mem_univ y)
        rw [hx]; exact hgy
      · -- `x ≠ g y`, so `pe / c = 0`, i.e. `pe = 0`: the guess is right a.s. and off-diagonal mass
        -- vanishes.
        have hpe0 : pe = 0 := by
          rcases div_eq_zero_iff.mp hr0 with h | h
          · exact h
          · exact hc0 h
        have hdiag_all : ∀ z, marginalSnd p z = p (g z, z) := by
          have hs0 : ∑ z, (marginalSnd p z - p (g z, z)) = 0 := by
            rw [Finset.sum_sub_distrib, sum_marginalSnd, hsum, hcorrect, hpe0]; ring
          have hnn : ∀ z ∈ Finset.univ, 0 ≤ marginalSnd p z - p (g z, z) :=
            fun z _ => sub_nonneg.mpr (le_marginalSnd hp (g z) z)
          intro z
          have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hs0 z (Finset.mem_univ z)
          linarith
        have hoff : ∑ x' ∈ Finset.univ.erase (g y), p (x', y) = 0 := by
          rw [Finset.sum_erase_eq_sub (Finset.mem_univ (g y)), ← marginalSnd_apply, hdiag_all y]
          ring
        exact (Finset.sum_eq_zero_iff_of_nonneg fun x' _ => hp (x', y)).mp hoff x
          (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)
  -- `qd` has total mass at most `1`, since each conditional `∑ₓ r (x, y) ≤ 1`.
  have hsumr_le : ∀ y, ∑ x, r (x, y) ≤ 1 := by
    intro y
    have hre : ∀ x, r (x, y) = pe / c + (if x = g y then (1 - pe) - pe / c else 0) := by
      intro x; simp only [hr_def]; split_ifs with hx <;> ring
    rw [Finset.sum_congr rfl fun x _ => hre x, Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true, Finset.card_univ, nsmul_eq_mul]
    have hccancel : ((Fintype.card ι : ℝ) - 1) * (pe / c) ≤ pe := by
      rcases eq_or_ne c 0 with hc | hc
      · rw [hc0 hc]; simp
      · rw [show ((Fintype.card ι : ℝ) - 1) = c from hc_def.symm, mul_div_cancel₀ pe hc]
    have hfact : (Fintype.card ι : ℝ) * (pe / c) + ((1 - pe) - pe / c)
        = ((Fintype.card ι : ℝ) - 1) * (pe / c) + (1 - pe) := by ring
    rw [hfact]; linarith
  have hle : ∑ xy, qd xy ≤ ∑ q, p q := by
    have hstep : ∑ xy, qd xy ≤ ∑ y, marginalSnd p y := by
      simp only [hqd_def]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_le_sum
      intro y _
      change ∑ x, marginalSnd p y * r (x, y) ≤ marginalSnd p y
      rw [← Finset.mul_sum]
      exact mul_le_of_le_one_right (marginalSnd_nonneg hp y) (hsumr_le y)
    rwa [sum_marginalSnd] at hstep
  -- The conditional distribution of the joint over the second coordinate.
  have hinner : ∀ y, ∑ x, p (x, y) * Real.log (r (x, y))
      = marginalSnd p y * Real.log (pe / c)
        + p (g y, y) * (Real.log (1 - pe) - Real.log (pe / c)) := by
    intro y
    have hrw : ∀ x, p (x, y) * Real.log (r (x, y))
        = p (x, y) * Real.log (pe / c)
          + (if x = g y then p (x, y) * (Real.log (1 - pe) - Real.log (pe / c)) else 0) := by
      intro x; simp only [hr_def]; split_ifs with hx <;> ring
    rw [Finset.sum_congr rfl fun x _ => hrw x, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← marginalSnd_apply, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
  -- The pointwise cross-entropy split: `p log qd = p log p_Y + p log r`.
  have hpoint : ∀ (x : ι) (y : κ), p (x, y) * Real.log (qd (x, y))
      = p (x, y) * Real.log (marginalSnd p y) + p (x, y) * Real.log (r (x, y)) := by
    intro x y
    rcases eq_or_ne (p (x, y)) 0 with h0 | h0
    · rw [h0]; ring
    · have hpos : (0 : ℝ) < p (x, y) := (hp _).lt_of_ne (Ne.symm h0)
      have hms : marginalSnd p y ≠ 0 := ne_of_gt (lt_of_lt_of_le hpos (le_marginalSnd hp x y))
      have hrne : r (x, y) ≠ 0 := by
        intro hr0'
        refine h0 (hsupp (x, y) ?_)
        simp only [hqd_def]; rw [hr0']; ring
      simp only [hqd_def]
      rw [Real.log_mul hms hrne]; ring
  -- Assemble the cross-entropy.
  have hcross : (-∑ xy, p xy * Real.log (qd xy))
      = entropy (marginalSnd p) + (binEntropy pe + pe * Real.log c) := by
    have hSB : ∑ y, ∑ x, p (x, y) * Real.log (r (x, y))
        = (1 - pe) * Real.log (1 - pe) + pe * Real.log (pe / c) := by
      rw [Finset.sum_congr rfl fun y _ => hinner y, Finset.sum_add_distrib, ← Finset.sum_mul,
        ← Finset.sum_mul, sum_marginalSnd, hsum, hcorrect]
      ring
    have hkey : ∑ xy, p xy * Real.log (qd xy)
        = (∑ y, marginalSnd p y * Real.log (marginalSnd p y))
          + ((1 - pe) * Real.log (1 - pe) + pe * Real.log (pe / c)) := by
      have hsplit : ∑ xy, p xy * Real.log (qd xy)
          = (∑ y, ∑ x, p (x, y) * Real.log (marginalSnd p y))
            + (∑ y, ∑ x, p (x, y) * Real.log (r (x, y))) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro y _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro x _
        exact hpoint x y
      rw [hsplit, hSB]
      congr 1
      apply Finset.sum_congr rfl; intro y _
      rw [← Finset.sum_mul, ← marginalSnd_apply]
    rw [hkey, neg_add]
    congr 1
    · rw [entropy_eq_neg_sum_mul_log]
    · have hlogdiv : pe * Real.log (pe / c) = pe * (Real.log pe - Real.log c) := by
        rcases eq_or_ne pe 0 with h | h
        · rw [h]; ring
        · rw [Real.log_div h fun hc => h (hc0 hc)]
      rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      simp only [Real.negMulLog]
      rw [hlogdiv]; ring
  -- Gibbs' inequality plus the cross-entropy identity give the bound.
  have hgibbs : entropy p ≤ -∑ xy, p xy * Real.log (qd xy) :=
    entropy_le_cross_entropy_of_sum_le hp hqd_nonneg hsupp hle
  rw [hcross] at hgibbs
  rw [condEntropy_eq]
  linarith

-- **Fano's inequality**, packaged with the `|ι|`-ary entropy: `H(X | Y) ≤ qaryEntropy |ι| pₑ`,
-- where `pₑ = Real.fanoErrorProb p g` is the probability that the guess `X̃ = g Y` for `X` is
-- wrong. This is `Real.condEntropy_le_binEntropy_add_mul_log` repackaged via
-- `Real.qaryEntropy_eq_log_add_binEntropy`.
--
theorem condEntropy_le_qaryEntropy
    {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) (g : κ → ι) :
    condEntropy p ≤ qaryEntropy (Fintype.card ι) (fanoErrorProb p g) := by
  refine (condEntropy_le_binEntropy_add_mul_log hp hsum g).trans (le_of_eq ?_)
  rw [qaryEntropy_eq_log_add_binEntropy]
  push_cast
  ring

/-- The mutual information equals the first-marginal entropy minus the conditional entropy,
`I(X : Y) = H(X) − H(X | Y)`. A pure rewriting of the definitions (`Real.mutualInfo_eq`,
`Real.condEntropy_eq`); it holds for every `p : ι × κ → ℝ`, with no positivity or normalization
hypothesis. -/
theorem mutualInfo_eq_entropy_marginalFst_sub_condEntropy (p : ι × κ → ℝ) :
    mutualInfo p = entropy (marginalFst p) - condEntropy p := by
  rw [mutualInfo_eq, condEntropy_eq]; ring

/-- **Fano's inequality in mutual-information form.** For a joint distribution `p : ι × κ → ℝ`
(`0 ≤ p`, `∑ p = 1`) and any guess `X̃ = g Y`, the first-marginal (input) entropy is controlled by
the mutual information plus a Fano penalty:

`H(X) ≤ I(X : Y) + log 2 + pₑ · log |ι|`,

where `pₑ = Real.fanoErrorProb p g`. This is the identity `H(X) = I(X : Y) + H(X | Y)`
(`Real.mutualInfo_eq_entropy_marginalFst_sub_condEntropy`) combined with Fano's inequality
`H(X | Y) ≤ binEntropy pₑ + pₑ · log (|ι| − 1) ≤ log 2 + pₑ · log |ι|`
(`Real.condEntropy_le_binEntropy_add_mul_log`, `Real.binEntropy_le_log_two`). It is the
converse-coding workhorse: a small error probability `pₑ` forces the input entropy `H(X)` down to
essentially the mutual information `I(X : Y)` that the channel actually conveys. -/
theorem entropy_marginalFst_le_mutualInfo_add
    {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) (g : κ → ι) :
    entropy (marginalFst p)
      ≤ mutualInfo p + Real.log 2 + fanoErrorProb p g * Real.log (Fintype.card ι) := by
  have hpe_nonneg := fanoErrorProb_nonneg hp hsum g
  have hfano := condEntropy_le_binEntropy_add_mul_log hp hsum g
  have hbin : binEntropy (fanoErrorProb p g) ≤ Real.log 2 := binEntropy_le_log_two
  -- `|ι| ≥ 1`, so `log (|ι| − 1) ≤ log |ι|`.
  have hcard1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast one_le_card_of_sum_eq_one hsum
  have hlog_le : Real.log ((Fintype.card ι : ℝ) - 1) ≤ Real.log (Fintype.card ι) := by
    rcases eq_or_lt_of_le hcard1 with h | h
    · rw [← h]; norm_num
    · exact Real.log_le_log (by linarith) (by linarith)
  have hmul : fanoErrorProb p g * Real.log ((Fintype.card ι : ℝ) - 1)
      ≤ fanoErrorProb p g * Real.log (Fintype.card ι) :=
    mul_le_mul_of_nonneg_left hlog_le hpe_nonneg
  have hI := mutualInfo_eq_entropy_marginalFst_sub_condEntropy p
  linarith

/-- **Fano's converse inequality for a uniform input.** When the first marginal of `p` is uniform
(`marginalFst p i = |ι|⁻¹`, so that `H(X) = log |ι|`), the mutual-information Fano bound
(`Real.entropy_marginalFst_le_mutualInfo_add`) rearranges to

`(1 − pₑ) · log |ι| ≤ log 2 + I(X : Y)`,

the per-block converse of the noisy-channel coding theorem (Nielsen & Chuang, eqs. (12.98)–
(12.101)): the reliably conveyable rate `log |ι|` is, up to the error penalty `pₑ · log |ι|` and the
additive `log 2`, no larger than the mutual information the channel provides. -/
theorem one_sub_fanoErrorProb_mul_log_card_le
    {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1)
    (huniform : ∀ i, marginalFst p i = (Fintype.card ι : ℝ)⁻¹) (g : κ → ι) :
    (1 - fanoErrorProb p g) * Real.log (Fintype.card ι) ≤ Real.log 2 + mutualInfo p := by
  have hHX : entropy (marginalFst p) = Real.log (Fintype.card ι) := by
    have huf : marginalFst p = fun _ : ι => (Fintype.card ι : ℝ)⁻¹ := funext huniform
    rw [huf, entropy_uniform]
  have h := entropy_marginalFst_le_mutualInfo_add hp hsum g
  rw [hHX] at h
  have hexpand : (1 - fanoErrorProb p g) * Real.log (Fintype.card ι)
      = Real.log (Fintype.card ι) - fanoErrorProb p g * Real.log (Fintype.card ι) := by ring
  rw [hexpand]; linarith

end Real
