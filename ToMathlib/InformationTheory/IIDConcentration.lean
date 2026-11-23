/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Concentration of the empirical mean for a finite i.i.d. source

For a finite type `α` and a function `p : α → ℝ` (a probability mass function when `0 ≤ p x` and
`∑ x, p x = 1`), the **`n`-fold i.i.d. product distribution** assigns to a length-`n` sequence
`s : Fin n → α` the weight `∏ i, p (s i)`. Given an observable `g : α → ℝ` with mean
`m = ∑ x, p x * g x`, this file proves the elementary (Chebyshev) **weak law of large numbers**:
the product-distribution probability that the empirical mean `(∑ i, g (s i)) / n` deviates from
`m` by more than `ε` is at most `(∑ x, p x * (g x - m) ^ 2) / (n * ε ^ 2)`.

This is the concentration engine behind the theorem of typical sequences
(Nielsen & Chuang, Theorem 12.2 / the classical asymptotic equipartition property): applied to the
surprisal `g x = -Real.log (p x)`, whose mean is the Shannon entropy `Real.entropy p`, it shows
that with high probability a length-`n` sequence has log-probability close to `-n * H`.

Everything is a finite sum over `Fin n → α`; no measure theory is used. This mirrors the elementary
finite-distribution convention of `ToMathlib/Analysis/SpecialFunctions/ShannonEntropy.lean` (a
distribution is a bare `p : α → ℝ`, hypotheses `0 ≤ p`, `∑ p = 1` supplied to lemmas), and gives a
self-contained, finite-`n`-explicit concentration bound — exactly the form the counting arguments
of the typical-sequence theorem consume.

## Main results

- `Real.iid_total_mass`: the total mass `∑ s, ∏ i, p (s i)` equals `(∑ x, p x) ^ n`.
- `Real.iid_centered_sq`: the second-moment identity
  `∑ s, (∏ i, p (s i)) * (∑ i, g (s i) - m) ^ 2 = n * ∑ x, p x * (g x - m) ^ 2`
  (variance of a sum of `n` i.i.d. terms is `n` times the per-sample variance).
- `Real.iid_average_deviation_le`: the Chebyshev weak law, the concentration bound above.
-/

@[expose] public section

open Finset

namespace Real

variable {α : Type*} [Fintype α]

/-- Summing a coordinatewise product `∏ i, φ i (s i)` over all length-`n` sequences `s` factors as
the product `∏ i, ∑ x, φ i x` of the coordinatewise sums. -/
lemma sum_prod_apply_eq_prod_sum {n : ℕ} (φ : Fin n → α → ℝ) :
    ∑ s : Fin n → α, ∏ i, φ i (s i) = ∏ i, ∑ x, φ i x := by
  classical
  rw [Finset.prod_univ_sum, ← Fintype.piFinset_univ]

/-- The total mass of the `n`-fold i.i.d. product distribution `s ↦ ∏ i, p (s i)` is
`(∑ x, p x) ^ n`. In particular it is `1` when `p` sums to one. -/
theorem iid_total_mass (p : α → ℝ) (n : ℕ) :
    ∑ s : Fin n → α, ∏ i, p (s i) = (∑ x, p x) ^ n := by
  rw [sum_prod_apply_eq_prod_sum (fun _ => p), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- Split a sum over length-`(n+1)` sequences on the first coordinate: peel off the head via
`Fin.cons`. -/
private lemma sum_fin_succ {n : ℕ} (F : (Fin (n + 1) → α) → ℝ) :
    ∑ s : Fin (n + 1) → α, F s = ∑ a : α, ∑ t : Fin n → α, F (Fin.cons a t) := by
  classical
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ => α) F, Fintype.sum_prod_type]
  rfl

/-- **Second-moment identity.** For a probability distribution `p` (summing to one) and an
observable `g` with mean `m = ∑ x, p x * g x`, the `p`-`n`-fold-product average of the squared
centered sum `(∑ i, g (s i) - m) ^ 2` equals `n` times the per-sample variance
`∑ x, p x * (g x - m) ^ 2`. Proof by induction on `n`: peeling one coordinate contributes the
variance `∑ x, p x * (g x - m) ^ 2` (diagonal) plus the previous total (via the inductive
hypothesis); the cross term vanishes because the centered mean `∑ x, p x * (g x - m)` is zero. -/
theorem iid_centered_sq (p g : α → ℝ) (hp1 : ∑ x, p x = 1)
    {m : ℝ} (hm : m = ∑ x, p x * g x) (n : ℕ) :
    ∑ s : Fin n → α, (∏ i, p (s i)) * (∑ i, (g (s i) - m)) ^ 2
      = n * ∑ x, p x * (g x - m) ^ 2 := by
  classical
  have hmass : ∀ k : ℕ, ∑ s : Fin k → α, ∏ i, p (s i) = 1 := fun k => by
    rw [iid_total_mass, hp1, one_pow]
  have hmean0 : ∑ x, p x * (g x - m) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, ← hm, sub_self]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_fin_succ]
    have hcons : ∀ (a : α) (t : Fin n → α),
        (∏ i, p ((Fin.cons a t : Fin (n + 1) → α) i))
            * (∑ i, (g ((Fin.cons a t : Fin (n + 1) → α) i) - m)) ^ 2
          = p a * (∏ i, p (t i)) * ((g a - m) + ∑ i, (g (t i) - m)) ^ 2 := by
      intro a t
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
      simp [Fin.cons_zero, Fin.cons_succ]
    simp_rw [hcons]
    -- distribute the square into diagonal, cross, and tail parts
    have expand : ∀ (a : α) (t : Fin n → α),
        p a * (∏ i, p (t i)) * ((g a - m) + ∑ i, (g (t i) - m)) ^ 2
          = (p a * (g a - m) ^ 2) * (∏ i, p (t i))
            + 2 * (p a * (g a - m)) * ((∏ i, p (t i)) * (∑ i, (g (t i) - m)))
            + p a * ((∏ i, p (t i)) * (∑ i, (g (t i) - m)) ^ 2) := by
      intro a t; ring
    simp_rw [expand, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    have hcross : ∑ a, 2 * (p a * (g a - m)) = 0 := by
      rw [← Finset.mul_sum, hmean0, mul_zero]
    rw [hmass n, ih, hp1, hcross]
    push_cast
    ring

/-- **Chebyshev weak law of large numbers for a finite i.i.d. source.** With `m = ∑ x, p x * g x`
the mean of the observable `g`, the `n`-fold product-distribution probability that the empirical
mean `(∑ i, g (s i)) / n` deviates from `m` by more than `ε` is at most
`(∑ x, p x * (g x - m) ^ 2) / (n * ε ^ 2)`. -/
theorem iid_average_deviation_le (p g : α → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {m : ℝ} (hm : m = ∑ x, p x * g x) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∑ s ∈ univ.filter (fun s : Fin n → α => ε < |(∑ i, g (s i)) / n - m|), ∏ i, p (s i)
      ≤ (∑ x, p x * (g x - m) ^ 2) / (n * ε ^ 2) := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set V := ∑ x, p x * (g x - m) ^ 2 with hVdef
  set S := univ.filter (fun s : Fin n → α => ε < |(∑ i, g (s i)) / n - m|) with hSdef
  have hsecond : ∑ s : Fin n → α, (∏ i, p (s i)) * (∑ i, (g (s i) - m)) ^ 2 = n * V :=
    iid_centered_sq p g hp1 hm n
  -- Chebyshev step: `(n·ε)² · P(S) ≤ Σ_S ∏p·(Σ(g−m))² ≤ n·V`.
  have hstepA : ((n : ℝ) * ε) ^ 2 * ∑ s ∈ S, ∏ i, p (s i)
      ≤ ∑ s ∈ S, (∏ i, p (s i)) * (∑ i, (g (s i) - m)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s hs => ?_
    rw [hSdef, Finset.mem_filter] at hs
    obtain ⟨_, hs2⟩ := hs
    have hpnn : 0 ≤ ∏ i, p (s i) := Finset.prod_nonneg fun i _ => hp0 _
    have hrw : (∑ i, g (s i)) / (n : ℝ) - m = (∑ i, (g (s i) - m)) / n := by
      have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    rw [hrw, abs_div, abs_of_pos hnpos, lt_div_iff₀ hnpos] at hs2
    have hdev : (n : ℝ) * ε < |∑ i, (g (s i) - m)| := by rw [mul_comm]; exact hs2
    have h2 : ((n : ℝ) * ε) ^ 2 ≤ (∑ i, (g (s i) - m)) ^ 2 := by
      nlinarith [sq_abs (∑ i, (g (s i) - m)), abs_nonneg (∑ i, (g (s i) - m)),
        mul_pos hnpos hε, hdev]
    calc ((n : ℝ) * ε) ^ 2 * ∏ i, p (s i)
        ≤ (∑ i, (g (s i) - m)) ^ 2 * ∏ i, p (s i) := mul_le_mul_of_nonneg_right h2 hpnn
      _ = (∏ i, p (s i)) * (∑ i, (g (s i) - m)) ^ 2 := by ring
  have hstepB : ∑ s ∈ S, (∏ i, p (s i)) * (∑ i, (g (s i) - m)) ^ 2
      ≤ ∑ s : Fin n → α, (∏ i, p (s i)) * (∑ i, (g (s i) - m)) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    exact fun s _ _ => mul_nonneg (Finset.prod_nonneg fun i _ => hp0 _) (sq_nonneg _)
  have hcheb : ((n : ℝ) * ε) ^ 2 * ∑ s ∈ S, ∏ i, p (s i) ≤ n * V :=
    (hstepA.trans hstepB).trans_eq hsecond
  -- cancel one factor of `n` and rearrange into the divided form.
  have hcheb' : ((n : ℝ) * ε ^ 2) * ∑ s ∈ S, ∏ i, p (s i) ≤ V := by
    have hrw2 : ((n : ℝ) * ε) ^ 2 * ∑ s ∈ S, ∏ i, p (s i)
        = (n : ℝ) * (((n : ℝ) * ε ^ 2) * ∑ s ∈ S, ∏ i, p (s i)) := by ring
    rw [hrw2] at hcheb
    exact le_of_mul_le_mul_left hcheb hnpos
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * ε ^ 2), mul_comm]
  exact hcheb'

end Real
