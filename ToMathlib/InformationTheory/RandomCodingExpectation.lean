/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy
public import Mathlib.Logic.Equiv.Prod

/-!
# Random-coding expectation: marginals of a product weight over a codebook

The random-coding argument of the Holevo–Schumacher–Westmoreland theorem
(Nielsen & Chuang, Theorem 12.8, eqs. (12.80)–(12.82)) averages a per-codebook quantity over a
**random codebook**: a family `w : ι → β` of `|ι|` independently drawn codewords, each `w M : β`
chosen with weight `W (w M)`, so the codebook `w` carries the product weight `∏ M, W (w M)`. The
error estimate then reduces the expectation of a sum of trace terms — each depending on *one* or
*two* of the codewords — to marginal expectations, using that distinct codewords are
**independent**.

This file provides the two elementary combinatorial identities behind that reduction, for a
distribution `W : β → ℝ` (`∑ b, W b = 1`) over the codeword type `β`:

* `Real.sum_pi_weight_mul_apply` — the **single-codeword marginal**: for a quantity `f (w j)`
  depending only on codeword `j`,

  `∑_{w : ι → β} (∏ M, W (w M)) · f (w j)  =  ∑ b, W b · f b`,

  i.e. averaging over the whole codebook collapses to averaging over the single codeword `j` (the
  other codewords sum out to total mass `1`).

* `Real.sum_pi_weight_mul_apply₂` — the **two-codeword (independence) marginal**: for a quantity
  `g (w j) (w j')` depending on two *distinct* codewords `j ≠ j'`,

  `∑_{w : ι → β} (∏ M, W (w M)) · g (w j) (w j')  =  ∑ v, ∑ v', W v · W v' · g v v'`,

  i.e. the expectation factorises over the two independent codewords.

In the HSW error estimate `W v = ∏ᵢ p (vᵢ)` is the i.i.d. per-codeword weight over length-`n`
sequences `v : Fin n → α` (`∑ v, W v = 1` is `AxQM.sum_iidProdWeight`), `ι = Fin K` indexes
the `K` messages, and the codeword output `σ_M` and its conditional typical projector `P_M` depend
only on codeword `M`; the single-codeword marginal handles the diagonal error terms
`𝔼 tr(σ_M (I − P)) = tr(σ̄^⊗n (I − P))` and `𝔼 tr(σ_M (I − P_M))`, while the two-codeword marginal
handles the false-decoding/confusion term `𝔼 tr(P σ_M P P_{M'})` for `M ≠ M'`, whose two factors
depend on the independent codewords `M` and `M'`.

Everything is a finite sum over `ι → β`; no measure theory is used, matching the elementary
finite-distribution convention of `ToMathlib/InformationTheory/IIDConcentration.lean` (a
distribution
is a bare `W : β → ℝ`, the hypothesis `∑ W = 1` supplied to the lemmas).

## Main results

- `Real.sum_pi_weight_mul_apply`: the single-codeword marginal.
- `Real.sum_pi_weight_mul_apply₂`: the two-codeword independence marginal.
-/

@[expose] public section

open Finset

namespace Real

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

/-- **Single-codeword marginal of a product weight.** For a distribution `W : β → ℝ`
(`∑ b, W b = 1`) and an observable `f (w j)` of the codebook `w : ι → β` depending only on the
single codeword `j`, the product-weight average over the whole codebook collapses to the average
over that one codeword:

`∑_{w : ι → β} (∏ M, W (w M)) · f (w j) = ∑ b, W b · f b`.

Random-coding statement: since the other `|ι| − 1` codewords are independent and their weights sum
to `1`, they marginalise out. This is the tool that turns the expectation of a diagonal error term
(depending on a single random codeword, e.g. `tr(σ_M (I − P_M))`) into a single-codeword
expectation. -/
theorem sum_pi_weight_mul_apply (W : β → ℝ) (hW : ∑ b, W b = 1) (f : β → ℝ) (j : ι) :
    ∑ w : ι → β, (∏ M, W (w M)) * f (w j) = ∑ b, W b * f b := by
  classical
  -- Write the summand as a coordinatewise product `∏ M, W (w M) · [M = j] f (w M)`.
  have hsummand : ∀ w : ι → β,
      (∏ M, W (w M)) * f (w j) = ∏ M, (W (w M) * (if M = j then f (w M) else 1)) := by
    intro w
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' univ j (fun M => f (w M)),
        ite_eq_left (mem_univ j)]
  simp_rw [hsummand]
  -- `∑_w ∏_M h M (w M) = ∏_M ∑_b h M b` (sum of products = product of sums over a pi `Fintype`).
  have hpiv : (∏ M, ∑ b, W b * (if M = j then f b else 1))
      = ∑ x : ι → β, ∏ M, W (x M) * (if M = j then f (x M) else 1) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [← hpiv, ← Finset.mul_prod_erase univ
    (fun M => ∑ b, W b * (if M = j then f b else 1)) (mem_univ j)]
  -- The `M = j` factor is `∑ b, W b · f b`; every other factor is `∑ b, W b = 1`.
  have h1 : (∑ b, W b * (if j = j then f b else 1)) = ∑ b, W b * f b := by simp
  have h2 : (∏ M ∈ univ.erase j, ∑ b, W b * (if M = j then f b else 1)) = 1 := by
    apply Finset.prod_eq_one
    intro M hM
    simp only [ite_eq_right (Finset.ne_of_mem_erase hM), mul_one]; exact hW
  rw [h1, h2, mul_one]

/-- **Two-codeword (independence) marginal of a product weight.** For a distribution `W : β → ℝ`
(`∑ b, W b = 1`) and an observable `g (w j) (w j')` of the codebook `w : ι → β` depending on two
*distinct* codewords `j ≠ j'`, the product-weight average factorises over the two independent
codewords:

`∑_{w : ι → β} (∏ M, W (w M)) · g (w j) (w j') = ∑ v, ∑ v', W v · W v' · g v v'`.

Random-coding statement: distinct codewords are independent, so their joint expectation is the
product of marginals. This is the tool that turns the expectation of the HSW false-decoding
(confusion) term `tr(P σ_M P P_{M'})` — whose two factors `σ_M` and `P_{M'}` depend on the two
independent random codewords `M ≠ M'` — into `tr(P 𝔼(σ_M) P 𝔼(P_{M'}))`.

Proof: split the codebook at coordinate `j'` via `Equiv.funSplitAt`, writing `w` as a value `v'` at
`j'` together with the remaining codewords `u : {M // M ≠ j'} → β`; the product weight factors as
`W v' · ∏ M, W (u M)`, and the inner sum over `u` is the single-codeword marginal
(`sum_pi_weight_mul_apply`) at the codeword `⟨j, hjj'⟩` of the reduced index. -/
theorem sum_pi_weight_mul_apply₂ (W : β → ℝ) (hW : ∑ b, W b = 1) (g : β → β → ℝ)
    {j j' : ι} (hjj' : j ≠ j') :
    ∑ w : ι → β, (∏ M, W (w M)) * g (w j) (w j') = ∑ v, ∑ v', W v * W v' * g v v' := by
  classical
  -- For a fixed value `v'` of codeword `j'`, marginalise the remaining codewords `u`.
  have step : ∀ v' : β,
      (∑ u : {M // M ≠ j'} → β,
        (∏ M, W ((Equiv.funSplitAt j' β).symm (v', u) M)) *
          g ((Equiv.funSplitAt j' β).symm (v', u) j) ((Equiv.funSplitAt j' β).symm (v', u) j'))
      = ∑ v, W v * W v' * g v v' := by
    intro v'
    have hsymm : ∀ (u : {M // M ≠ j'} → β) (M : ι),
        (Equiv.funSplitAt j' β).symm (v', u) M = if h : M = j' then v' else u ⟨M, h⟩ :=
      fun u M => by simp [Equiv.funSplitAt, Equiv.piSplitAt]
    calc ∑ u : {M // M ≠ j'} → β,
          (∏ M, W ((Equiv.funSplitAt j' β).symm (v', u) M)) *
            g ((Equiv.funSplitAt j' β).symm (v', u) j) ((Equiv.funSplitAt j' β).symm (v', u) j')
        = ∑ u : {M // M ≠ j'} → β, (W v' * ∏ M : {M // M ≠ j'}, W (u M)) * g (u ⟨j, hjj'⟩) v' := by
          refine Finset.sum_congr rfl fun u _ => ?_
          -- The product weight factors off the `j'`-coordinate.
          have hprod : (∏ M, W ((Equiv.funSplitAt j' β).symm (v', u) M))
              = W v' * ∏ M : {M // M ≠ j'}, W (u M) := by
            rw [← Finset.mul_prod_erase univ
              (fun M => W ((Equiv.funSplitAt j' β).symm (v', u) M)) (mem_univ j')]
            congr 1
            · rw [hsymm]; simp
            · rw [Finset.prod_subtype (univ.erase j') (p := fun x => x ≠ j')
                  (fun x => by simp [Finset.mem_erase])
                  (fun M => W ((Equiv.funSplitAt j' β).symm (v', u) M))]
              exact Finset.prod_congr rfl fun M _ => by rw [hsymm, dite_eq_right M.2]
          rw [hprod, hsymm, hsymm, dite_eq_right hjj', dite_eq_left rfl]
      _ = W v' * ∑ u : {M // M ≠ j'} → β, (∏ M : {M // M ≠ j'}, W (u M)) * g (u ⟨j, hjj'⟩) v' := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
      _ = W v' * ∑ v, W v * g v v' := by
          congr 1
          exact Real.sum_pi_weight_mul_apply W hW (fun b => g b v') (⟨j, hjj'⟩ : {M // M ≠ j'})
      _ = ∑ v, W v * W v' * g v v' := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
  -- Reindex the codebook by (value at `j'`, remaining codewords) and apply `step`.
  rw [← Equiv.sum_comp (Equiv.funSplitAt j' β).symm
      (fun w => (∏ M, W (w M)) * g (w j) (w j')), Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun v' _ => step v', Finset.sum_comm]

/-- **Derandomisation: a real weighted mean below a bound has a term below the bound.** For a
distribution `W : β → ℝ` (`∑ b, W b = 1`, `W ≥ 0`) and any `f : β → ℝ`, if the weighted mean
`∑ b, W b · f b` is at most `C`, then some `b` attains `f b ≤ C`.

The derandomisation step of a random-coding argument: the *expected* per-code quantity `f` over the
random codebook (distribution `W`) being at most `C` forces some concrete codebook `b` to have
`f b ≤ C`. If every `f b` exceeded `C`, then — since some weight `W b₀` is positive (as
`∑ W = 1 > 0`) — the mean `∑ b, W b · f b` would strictly exceed `∑ b, W b · C = C`, a
contradiction. -/
theorem exists_le_of_weighted_sum_le (W : β → ℝ) (hW0 : ∀ b, 0 ≤ W b) (hW1 : ∑ b, W b = 1)
    (f : β → ℝ) (C : ℝ) (h : ∑ b, W b * f b ≤ C) : ∃ b, f b ≤ C := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  obtain ⟨b0, hb0⟩ : ∃ b, 0 < W b := by
    by_contra h0
    simp only [not_exists, not_lt] at h0
    have hle : ∑ b, W b ≤ 0 := Finset.sum_nonpos fun b _ => h0 b
    rw [hW1] at hle
    linarith
  have hlt : C < ∑ b, W b * f b := by
    have hCeq : C = ∑ b, W b * C := by rw [← Finset.sum_mul, hW1, one_mul]
    rw [hCeq]
    refine Finset.sum_lt_sum (fun b _ => mul_le_mul_of_nonneg_left (hcon b).le (hW0 b)) ?_
    exact ⟨b0, Finset.mem_univ _, mul_lt_mul_of_pos_left (hcon b0) hb0⟩
  linarith

end Real
