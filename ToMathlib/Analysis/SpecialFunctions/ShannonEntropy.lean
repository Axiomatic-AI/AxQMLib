/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.BinaryEntropy
public import ToMathlib.Analysis.SpecialFunctions.Log.Basic
public import ToMathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import ToMathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Shannon entropy of a discrete distribution

For a finite type `ι` and a function `p : ι → ℝ` (interpreted as a probability mass function
when `p i ∈ [0, 1]` and `∑ i, p i = 1`), the **Shannon entropy** of `p` is

`Real.entropy p := ∑ i, Real.negMulLog (p i)`.

The function is defined on raw `ι → ℝ` input rather than on a bundled probability mass
function, mirroring the `Real.binEntropy : ℝ → ℝ` convention of accepting any real input and
providing distribution-hypothesis-driven API lemmas separately. Junk-valued on negative inputs
(where `Real.negMulLog` is itself junk-valued).

Entropy is measured in nats (natural log), matching the convention in
`Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean`.

## Main definitions

- `Real.entropy : (ι → ℝ) → ℝ`

## Main results

- `Real.entropy_eq` (rfl-lemma exposing the sum form).
- `Real.entropy_zero` (@[simp]): the all-zero distribution has zero entropy.
- `Real.entropy_const`: closed form on constant inputs.
- `Real.entropy_nonneg`: nonneg under the probability hypothesis `0 ≤ p i ≤ 1`.
- `Real.entropy_fin_two_eq_binEntropy`: reconciliation with the binary entropy function.
- `Real.entropy_prod`: product additivity for an independent joint distribution.
- `Real.entropy_sigma_mul`: grouping / chain rule `H(⟨i,k⟩ ↦ pᵢ · wᵢₖ) = H(p) + ∑ᵢ pᵢ H(wᵢ)` for a
  dependent (sigma-indexed) mixture distribution.
- `Real.entropy_le_log_card`: Jensen's-inequality-based upper bound by `log (card ι)`.
- `Real.entropy_uniform`: the uniform distribution `i ↦ (card ι)⁻¹` attains that bound.
- `Real.entropy_eq_log_card_iff`: **equality condition** (Nielsen–Chuang Theorem 11.2) — the
  bound `log (card ι)` is attained iff `p` is the uniform distribution.
- `Real.entropy_lt_log_card_of_ne_uniform`: **strict** form of the two above — a non-uniform `p`
  has entropy strictly below `log (card ι)`; the uniform distribution is the unique maximiser.
- `Real.entropy_eq_zero_iff`: **entropy-zero characterization** (Nielsen–Chuang Theorem 11.8,
  part (1)) — `entropy p = 0` iff `p` is a point mass (some `p i = 1`, the rest `0`); the
  minimum-entropy peer of `entropy_eq_log_card_iff`.
- `Real.sum_negMulLog_le`: **weighted grouping bound** (analytic kernel of Fannes' inequality,
  Nielsen–Chuang Theorem 11.6) — for nonnegative `a : ι → ℝ` not required to sum to `1`,
  `∑ negMulLog (a i) ≤ (∑ a i) * log (card ι) + negMulLog (∑ a i)`; the un-normalized
  generalization of `entropy_le_log_card`.
- `Real.entropy_le_qaryEntropy`: **grouping inequality** (single-distribution kernel of
  Fano's inequality) — `entropy r ≤ qaryEntropy (card ι) (1 - r i₀)`.
- `Real.entropy_concave`: concavity of `entropy` on the convex set of nonneg functions.
- `Real.entropy_le_cross_entropy_of_sum_le`: **sub-normalized cross-entropy bound**, the shared
  kernel — entropy is at most cross-entropy when `p`'s support lies in `q`'s and `∑ q ≤ ∑ p`. The
  per-term real-analysis facts `Real.mul_log_div_le_sub_of_nonneg` and `Real.mul_log_div` live
  in `ToMathlib/Analysis/SpecialFunctions/Log/Basic.lean`.
- `Real.entropy_le_cross_entropy_of_support_subset`: **Gibbs' inequality, support-aware
  form** — the equal-mass (`∑ p = ∑ q`) corollary of `entropy_le_cross_entropy_of_sum_le`.
- `Real.entropy_le_cross_entropy_of_sum_eq_one`: **Gibbs' inequality** (a.k.a. classical
  Klein's inequality) for strictly-positive `q`, a corollary of the support-aware form.
  Foundational classical input to the operator Klein inequality (Nielsen-Chuang Thm 11.7)
  via spectral decomposition + Jensen.
- `Real.sum_mul_sum_mul_log_le_neg_entropy_of_doubly_stochastic`: **doubly-stochastic
  Klein-classical bound** consumed by operator Klein's inequality. For prob dists `p, q` and
  doubly-stochastic weights `W`, `∑ p_i * ∑ W_ij log q_j ≤ -entropy p`. Proof: inner Jensen
  on `log` + bridge distribution `r_i := ∑ W_ij q_j` + outer Gibbs.
- `Real.relativeEntropy_nonneg`: **Gibbs' inequality**, `D(p‖q) ≥ 0` for prob dists with
  `q > 0`; `Real.relativeEntropy_nonneg_of_support_subset` is the support-aware form
  (`supp p ⊆ supp q`, equal total mass `∑ p = ∑ q`), and
  `Real.relativeEntropy_nonneg_of_sum_le` the **sub-normalized** form (`∑ q ≤ ∑ p`), which
  deduces `H(Y | X) ≥ 0` from the conditional-entropy relative-entropy expression (N&C Ex. 11.7).
- `Real.relativeEntropy_eq_zero_iff`: **equality condition** — `D(p‖q) = 0 ↔ p = q` under the
  same support/absolute-continuity hypothesis (`q x = 0 → p x = 0`, equal total mass). With the
  support-aware nonneg result this is the faithful real-valued rendering of Nielsen–Chuang
  Theorem 11.1 ("non-negative, with equality iff `p = q`") on the domain where `relativeEntropy`
  equals N&C's `H(p‖q)`. `Real.relativeEntropy_pos_of_ne` is the sharp `p ≠ q → D(p‖q) > 0`
  contrapositive form.
- `Real.abs_negMulLog_sub_le`: **continuity kernel of Fannes' inequality** (Nielsen–Chuang
  Theorem 11.6, eq. 11.47) — for `x, y ∈ [0, 1]` with `|x - y| ≤ 1/2`,
  `|negMulLog x - negMulLog y| ≤ negMulLog |x - y|`, i.e. `negMulLog` has itself as a modulus
  of continuity on scales `≤ 1/2`. `Real.strictMonoOn_negMulLog_Icc`: `negMulLog` is strictly
  increasing on `[0, e⁻¹]` (used to lift the bound to the trace distance). The supporting
  facts `Real.negMulLog_one_sub_le` (`η(1 - δ) ≤ η(δ)` for `δ ∈ [0, 1/2]`) and
  `Real.monotoneOn_negMulLog_sub_add` (the increment `η t - η (t + δ)` is monotone in `t`)
  are of independent interest. `Real.negMulLog_le_exp_neg_one`: `negMulLog x ≤ e⁻¹` for `x ≥ 0`
  (the maximum of `η`, attained at `e⁻¹`), the constant in the weaker unconditional Fannes bound
  (Nielsen–Chuang eq. 11.45).
-/

@[expose] public section

namespace Real

variable {ι : Type*} [Fintype ι]

/-- The Shannon entropy (in nats) of a discrete distribution `p : ι → ℝ`. -/
noncomputable def entropy (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

theorem entropy_eq (p : ι → ℝ) : entropy p = ∑ i, Real.negMulLog (p i) := rfl

/-- Entropy as the negated sum of `p i * log (p i)`: `entropy p = -∑ i, p i * log (p i)`
(since `negMulLog x = -(x * log x)`). -/
theorem entropy_eq_neg_sum_mul_log (p : ι → ℝ) :
    entropy p = -∑ i, p i * Real.log (p i) := by
  simp only [entropy_eq, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]

@[simp]
theorem entropy_zero : entropy (0 : ι → ℝ) = 0 := by simp [entropy_eq]

/-- Closed form for the entropy of a constant function. Specializes to `entropy 0 = 0`
and `entropy 1 = 0` (since `negMulLog 0 = 0` and `negMulLog 1 = 0`). -/
theorem entropy_const (c : ℝ) : entropy (fun _ : ι ↦ c) = Fintype.card ι * c.negMulLog := by
  simp [entropy_eq, Finset.sum_const, Finset.card_univ]

/-- The Shannon entropy `p ↦ ∑ i, negMulLog (p i)` is a continuous function of the distribution. -/
theorem continuous_entropy : Continuous (entropy : (ι → ℝ) → ℝ) := by
  unfold entropy
  exact continuous_finsetSum _ fun i _ => Real.continuous_negMulLog.comp (continuous_apply i)

@[simp]
theorem entropy_one : entropy (1 : ι → ℝ) = 0 := by
  rw [Pi.one_def]; simpa using entropy_const (ι := ι) 1

@[simp]
theorem entropy_isEmpty [IsEmpty ι] (p : ι → ℝ) : entropy p = 0 := by
  simp [entropy_eq]

/-- The **classical relative entropy** (Kullback–Leibler divergence) of `p` with respect to
`q`: `D(p‖q) = ∑ x, p x * (log (p x) - log (q x))`. With Mathlib's junk-value
`Real.log 0 = 0`, boundary terms vanish where `p x = 0`; nonnegativity holds under
`∑ p = ∑ q = 1` and absolute continuity (see `Real.entropy_le_cross_entropy_of_sum_eq_one`
and `Real.entropy_le_cross_entropy_of_support_subset`). -/
noncomputable def relativeEntropy (p q : ι → ℝ) : ℝ :=
  ∑ x, p x * (Real.log (p x) - Real.log (q x))

theorem relativeEntropy_eq (p q : ι → ℝ) :
    relativeEntropy p q = ∑ x, p x * (Real.log (p x) - Real.log (q x)) := rfl

/-- The relative entropy of a distribution with itself is `0`. -/
@[simp]
theorem relativeEntropy_self (p : ι → ℝ) : relativeEntropy p p = 0 := by
  simp [relativeEntropy_eq]

@[simp]
theorem relativeEntropy_isEmpty [IsEmpty ι] (p q : ι → ℝ) : relativeEntropy p q = 0 := by
  simp [relativeEntropy_eq]

/-- The relative entropy splits as `(∑ x, p x * log (p x)) - ∑ x, p x * log (q x)`. The
first sum is `-entropy p` (since `entropy p = ∑ x, negMulLog (p x) = -∑ x, p x * log (p x)`)
and the second is the cross-entropy `-∑ x, p x * log (q x)` up to sign, so equivalently
`relativeEntropy p q = -entropy p - (-cross-entropy)`. This is the reusable form feeding
Gibbs' inequality (`relativeEntropy p q ≥ 0`). -/
theorem relativeEntropy_eq_sub (p q : ι → ℝ) :
    relativeEntropy p q = (∑ x, p x * Real.log (p x)) - ∑ x, p x * Real.log (q x) := by
  simp only [relativeEntropy_eq, mul_sub, Finset.sum_sub_distrib]

/-- The Shannon entropy of a probability distribution (taking values in `[0, 1]`) is nonneg. -/
theorem entropy_nonneg {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) :
    0 ≤ entropy p :=
  Finset.sum_nonneg fun i _ ↦ Real.negMulLog_nonneg (h0 i) (h1 i)

/-- The entropy of a two-outcome distribution `(p, 1 - p)` is the binary entropy of `p`. -/
theorem entropy_fin_two_eq_binEntropy (p : ℝ) : entropy ![p, 1 - p] = binEntropy p := by
  simp [entropy_eq, binEntropy_eq_negMulLog_add_negMulLog_one_sub, Fin.sum_univ_succ]

variable {κ : Type*} [Fintype κ]

/-- **Product additivity**: the Shannon entropy of an independent joint distribution
`r (i, j) := p i * q j` is the sum of the marginal entropies, provided both marginals sum
to one. -/
theorem entropy_prod {p : ι → ℝ} {q : κ → ℝ} (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) :
    entropy (fun ij : ι × κ ↦ p ij.1 * q ij.2) = entropy p + entropy q := by
  rw [entropy_eq, Fintype.sum_prod_type, entropy_eq, entropy_eq]
  calc ∑ x, ∑ y, negMulLog (p x * q y)
      = ∑ x, ∑ y, (q y * negMulLog (p x) + p x * negMulLog (q y)) := by simp_rw [negMulLog_mul]
    _ = ∑ x, ((∑ y, q y) * negMulLog (p x) + p x * ∑ y, negMulLog (q y)) := by
        simp_rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ x, negMulLog (p x) + (∑ x, p x) * ∑ y, negMulLog (q y) := by
        rw [hq]; simp [Finset.sum_add_distrib, Finset.sum_mul]
    _ = ∑ x, negMulLog (p x) + ∑ y, negMulLog (q y) := by rw [hp, one_mul]

/-- **Grouping / chain rule** for the Shannon entropy of a mixture. If the inner family `w i` is a
probability distribution for each `i` (`∑ₖ w i k = 1`), the entropy of the joint distribution
`⟨i, k⟩ ↦ p i · w i k` splits as the entropy of the outer weights `p` plus the `p`-weighted average
of the inner entropies:

`H(⟨i, k⟩ ↦ pᵢ · wᵢₖ) = H(p) + ∑ᵢ pᵢ · H(wᵢ)`.

Unlike `entropy_prod` the inner distribution `w i` may depend on the outer index `i` (a genuine
mixture, not an independent product). This is the classical kernel of the orthogonal-support
mixture-entropy identity and the joint-entropy theorem (Nielsen & Chuang Theorem 11.8 parts 4–5,
Theorem 11.10): if states `ρᵢ` have eigenvalue distributions `wᵢ` and orthogonal supports, the
mixed spectrum is `⟨i, k⟩ ↦ pᵢ · wᵢₖ` and its entropy splits this way. -/
theorem entropy_sigma_mul {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (p : ι → ℝ) (w : (i : ι) → κ i → ℝ) (hw : ∀ i, ∑ k, w i k = 1) :
    entropy (fun ik : Σ i, κ i ↦ p ik.1 * w ik.1 ik.2)
      = entropy p + ∑ i, p i * entropy (w i) := by
  rw [entropy_eq, Fintype.sum_sigma, entropy_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  calc ∑ k, negMulLog (p i * w i k)
      = ∑ k, (w i k * negMulLog (p i) + p i * negMulLog (w i k)) := by simp_rw [negMulLog_mul]
    _ = (∑ k, w i k) * negMulLog (p i) + p i * ∑ k, negMulLog (w i k) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ = negMulLog (p i) + p i * entropy (w i) := by rw [hw i, one_mul, entropy_eq]

/-- **Grouping / chain rule** for the Shannon entropy of a mixture over a *product* index. If the
inner family `q x` is a probability distribution for each `x` (`∑ₖ q x k = 1`), the entropy of the
joint distribution `⟨x, k⟩ ↦ pₓ · q x k` on `ι × κ` splits as the entropy of the outer weights `p`
plus the `p`-weighted average of the inner entropies:

`H(⟨x, k⟩ ↦ pₓ · q x k) = H(p) + ∑ₓ pₓ · H(q x)`.

This is the constant-fibre (`ι × κ`) form of `entropy_sigma_mul`: as there, the inner distribution
`q x` may depend on the outer index `x` (a genuine mixture, not an independent product as in
`entropy_prod`). It is the classical chain rule `H(X, Y) = H(X) + H(Y | X)` for a joint given by a
conditional kernel `q x = p(· | x)`, and the classical kernel of the Holevo χ ↔ mutual-information
identity (Nielsen & Chuang Problem 12.1). -/
theorem entropy_prod_mul {p : ι → ℝ} {q : ι → κ → ℝ} (hq : ∀ i, ∑ k, q i k = 1) :
    entropy (fun ik : ι × κ ↦ p ik.1 * q ik.1 ik.2) = entropy p + ∑ i, p i * entropy (q i) := by
  rw [entropy_eq, Fintype.sum_prod_type, entropy_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  calc ∑ k, negMulLog (p i * q i k)
      = ∑ k, (q i k * negMulLog (p i) + p i * negMulLog (q i k)) := by simp_rw [negMulLog_mul]
    _ = (∑ k, q i k) * negMulLog (p i) + p i * ∑ k, negMulLog (q i k) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ = negMulLog (p i) + p i * entropy (q i) := by rw [hq i, one_mul, entropy_eq]

/-- **Multiset-eq bridge for Shannon entropy.** If two finite-indexed sequences `f : ι → ℝ`
and `g : κ → ℝ` produce equal multisets of values (i.e., the underlying-Multiset of the
universe-image agrees), their Shannon entropies agree. The key bridge from
`<X>_eigenvalues_multiset_eq` capstones to entropy equality — used in
`LinearMap.IsSymmetric.vonNeumannEntropy_tensorPow_of_sum_eigenvalues_eq_one` and
`LinearMap.IsSymmetric.vonNeumannEntropy_tensorOp_of_sum_eigenvalues_eq_one`. -/
theorem entropy_eq_of_multiset_map_eq {f : ι → ℝ} {g : κ → ℝ}
    (h : (Finset.univ : Finset ι).val.map f = (Finset.univ : Finset κ).val.map g) :
    entropy f = entropy g := by
  rw [entropy_eq, entropy_eq, ← Finset.sum_map_val, ← Finset.sum_map_val]
  simp only [← Function.comp_def Real.negMulLog]
  rw [← Multiset.map_map Real.negMulLog f, ← Multiset.map_map Real.negMulLog g, h]

/-- **Product-distribution entropy additivity** (per-coordinate form): for a family of probability
distributions `r j : ι → ℝ` (each `∑ₓ r j x = 1`), the Shannon entropy of the product distribution
`y ↦ ∏ⱼ r j (y j)` over `Fin n → ι` is the sum `∑ⱼ H(r j)` of the coordinate entropies.

Proof: induction on `n`; the inductive step peels the last coordinate through `Fin.succFunEquiv`
(bridging `Fin (n+1) → ι ≃ (Fin n → ι) × ι`) and applies `entropy_prod`, whose outer marginal (the
product over the first `n` coordinates) sums to one via `Finset.sum_prod_piFinset`. The i.i.d.
tensor power `entropy_pi_prod_of_sum_eq_one` (`H(p^{⊗n}) = n · H(p)`) is the special case
`r j = p`. It is the "noise entropy single-letterizes" ingredient in the converse of Shannon's noisy
channel coding theorem (Nielsen & Chuang Theorem 12.7): the conditional output entropy
`H(Yⁿ | Xⁿ = xⁿ) = H(∏ⱼ q(·|xⱼ))` of the memoryless `n`-use channel splits as `∑ⱼ H(q(·|xⱼ))`. -/
theorem entropy_pi_prod :
    ∀ {n : ℕ} {r : Fin n → ι → ℝ}, (∀ j, ∑ x, r j x = 1) →
      entropy (fun y : Fin n → ι ↦ ∏ j, r j (y j)) = ∑ j, entropy (r j) := by
  intro n
  induction n with
  | zero =>
      intro r _
      rw [Fin.sum_univ_zero, entropy_eq]
      refine Finset.sum_eq_zero fun y _ ↦ ?_
      simp [Real.negMulLog_one]
  | succ n ih =>
      intro r hr
      -- The outer marginal (product over the first `n` coordinates) is a probability distribution.
      have hout_sum : ∑ z : Fin n → ι, ∏ i, r i.castSucc (z i) = 1 := by
        rw [← Fintype.piFinset_univ, Finset.sum_prod_piFinset]
        simp [hr]
      -- Bridge `Fin (n+1) → ι ≃ (Fin n → ι) × ι` (peel the last coordinate).
      have hbij : entropy (fun y : Fin (n + 1) → ι ↦ ∏ j, r j (y j))
          = entropy (fun pair : (Fin n → ι) × ι ↦
              (∏ i, r i.castSucc (pair.1 i)) * r (Fin.last n) pair.2) := by
        rw [entropy_eq, entropy_eq, ← (Fin.succFunEquiv ι n).sum_comp]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        simp only [Fin.succFunEquiv_apply, Fin.prod_univ_castSucc]
        rfl
      rw [hbij, entropy_prod hout_sum (hr (Fin.last n)),
        ih (r := fun i ↦ r i.castSucc) (fun i ↦ hr i.castSucc), Fin.sum_univ_castSucc]

/-- **Pi-tensor-power additivity**: the Shannon entropy of the n-fold independent
product distribution `κ ↦ ∏ i, p (κ i)` over `Fin n → ι` is `n * entropy p`, provided
`p` sums to one. This is the i.i.d. special case `r j = p` of the per-coordinate
`Real.entropy_pi_prod`. -/
theorem entropy_pi_prod_of_sum_eq_one {p : ι → ℝ} (hp : ∑ i, p i = 1) (n : ℕ) :
    entropy (fun κ : Fin n → ι ↦ ∏ i, p (κ i)) = n * entropy p := by
  rw [entropy_pi_prod (fun _ ↦ hp), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- **Jensen's upper bound**: the Shannon entropy of a probability distribution on a
nonempty finite type is at most `log (card ι)`. The bound is tight for the uniform
distribution. -/
theorem entropy_le_log_card [Nonempty ι] {p : ι → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    entropy p ≤ Real.log (Fintype.card ι) := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have h_uniform : ∑ i, (n⁻¹ : ℝ) • p i = n⁻¹ := by
    rw [← Finset.smul_sum, hsum, smul_eq_mul, mul_one]
  -- Apply Jensen with uniform weights `wᵢ = 1/n`.
  have hjensen :
      ∑ i, (n⁻¹ : ℝ) • negMulLog (p i) ≤ negMulLog (∑ i, (n⁻¹ : ℝ) • p i) := by
    refine concaveOn_negMulLog.le_map_sum ?_ ?_ fun i _ ↦ h0 i
    · intro i _; positivity
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def, mul_inv_cancel₀ hn.ne']
  rw [← Finset.smul_sum, h_uniform, negMulLog_inv, smul_eq_mul] at hjensen
  rw [entropy_eq]
  exact (mul_le_mul_iff_of_pos_left (inv_pos.mpr hn)).mp hjensen

/-- The uniform distribution `i ↦ (card ι)⁻¹` attains the maximal entropy `log (card ι)` — the
tight case of `entropy_le_log_card`. Holds unconditionally: for empty `ι` both sides are `0`. -/
theorem entropy_uniform :
    entropy (fun _ : ι ↦ (Fintype.card ι : ℝ)⁻¹) = Real.log (Fintype.card ι) := by
  rw [entropy_const, negMulLog_inv]
  rcases eq_or_ne (Fintype.card ι : ℝ) 0 with h | h
  · rw [h]; simp
  · rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]

/-- **Equality in the entropy bound** (Nielsen–Chuang, *Quantum Computation and Quantum
Information*, Theorem 11.2): for a probability distribution `p` on a nonempty finite type, the
Shannon entropy attains its maximum value `log (card ι)` **if and only if** `p` is the uniform
distribution `i ↦ (card ι)⁻¹`. Together with `entropy_le_log_card` (the inequality
`entropy p ≤ log (card ι)`) this is the full statement `H(X) ≤ log d` with equality iff `X` is
uniformly distributed over its `d = card ι` outcomes.

Proof: the equality case of strict Jensen (`StrictConcaveOn.map_sum_eq_iff` applied to
`strictConcaveOn_negMulLog`) with the uniform weights `wᵢ = (card ι)⁻¹`. Jensen's equality holds
iff every `p j` equals the weighted average `∑ i, (card ι)⁻¹ • p i = (card ι)⁻¹`, and the left-hand
side of that Jensen equality rescales to `entropy p = log (card ι)` after cancelling the common
factor `(card ι)⁻¹ > 0`. -/
theorem entropy_eq_log_card_iff [Nonempty ι] {p : ι → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    entropy p = Real.log (Fintype.card ι) ↔ ∀ i, p i = (Fintype.card ι : ℝ)⁻¹ := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have hw_pos : ∀ i ∈ (Finset.univ : Finset ι), (0 : ℝ) < n⁻¹ := fun i _ ↦ by positivity
  have hw_sum : ∑ _i : ι, (n⁻¹ : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def, mul_inv_cancel₀ hn.ne']
  have hmem : ∀ i ∈ (Finset.univ : Finset ι), p i ∈ Set.Ici (0 : ℝ) := fun i _ ↦ h0 i
  -- Equality case of strict Jensen with uniform weights `wᵢ = n⁻¹`.
  have key := strictConcaveOn_negMulLog.map_sum_eq_iff (t := Finset.univ)
    (w := fun _ : ι ↦ (n⁻¹ : ℝ)) (p := p) hw_pos hw_sum hmem
  have h_uniform : ∑ i, (n⁻¹ : ℝ) • p i = n⁻¹ := by
    rw [← Finset.smul_sum, hsum, smul_eq_mul, mul_one]
  have h_rhs : ∑ i, (n⁻¹ : ℝ) • negMulLog (p i) = n⁻¹ * entropy p := by
    rw [← Finset.smul_sum, smul_eq_mul, ← entropy_eq]
  -- `key : n⁻¹ * log n = n⁻¹ * entropy p ↔ ∀ i, p i = n⁻¹`.
  simp only [h_uniform, h_rhs, negMulLog_inv, Finset.mem_univ, forall_const] at key
  rw [← key, mul_right_inj' (inv_ne_zero hn.ne')]
  exact eq_comm

/-- **Strict maximum-entropy principle**: for a probability distribution `p` on a nonempty finite
type that is *not* the uniform distribution `i ↦ (card ι)⁻¹`, the Shannon entropy is strictly below
the maximal value `log (card ι)` (attained by the uniform distribution, `entropy_uniform`). This is
the strict sharpening of `entropy_le_log_card` supplied by its equality condition
`entropy_eq_log_card_iff`: the uniform distribution is the *unique* entropy maximiser, so any bias
strictly lowers the entropy. -/
theorem entropy_lt_log_card_of_ne_uniform [Nonempty ι] {p : ι → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hne : ¬ ∀ i, p i = (Fintype.card ι : ℝ)⁻¹) :
    entropy p < Real.log (Fintype.card ι) := by
  exact (entropy_le_log_card h0 hsum).lt_of_ne fun h => hne ((entropy_eq_log_card_iff h0 hsum).mp h)

/-- **Entropy vanishes exactly at a point mass** (Nielsen–Chuang, *Quantum Computation and Quantum
Information*, Theorem 11.8, part (1)): for a probability distribution `p` on a finite type, the
Shannon entropy is zero **if and only if** `p` is a point mass — some outcome `i` has `p i = 1` and
every other `p j = 0`. Together with `entropy_nonneg` (`H ≥ 0`) this is the classical content behind
the first item of Theorem 11.8 (`S(ρ) = 0` iff `ρ` is pure); it is the entropy-zero peer of the
maximum-entropy characterization `entropy_eq_log_card_iff`.

Forward: `entropy p = ∑ i, negMulLog (p i)` is a sum of non-negative terms (`negMulLog_nonneg`, as
`0 ≤ p i ≤ 1`), so it vanishes iff every term does (`Finset.sum_eq_zero_iff_of_nonneg`); each
vanishing term forces `p i ∈ {0, 1}` (`negMulLog_eq_zero`, the roots of `-x log x` on `[0, ∞)`).
As `∑ p = 1 ≠ 0`, some `p k ≠ 0` (`Finset.exists_ne_zero_of_sum_ne_zero`), forcing
`p k = 1`, and then `∑_{j ≠ k} p j = 1 - 1 = 0` forces the rest to vanish (`Finset.sum_erase_eq_sub`
+ `Finset.sum_eq_zero_iff_of_nonneg`). Reverse: the entropy sum collapses to
`negMulLog 1 + ∑ negMulLog 0 = 0`. -/
theorem entropy_eq_zero_iff {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    entropy p = 0 ↔ ∃ i, p i = 1 ∧ ∀ j, j ≠ i → p j = 0 := by
  classical
  have hle1 : ∀ i, p i ≤ 1 := fun i =>
    (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)).trans hsum.le
  constructor
  · intro hent
    rw [entropy_eq] at hent
    -- Each `negMulLog (p i) ≥ 0`, so the vanishing sum forces every term to vanish.
    have hterm : ∀ i, (p i).negMulLog = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => negMulLog_nonneg (h0 j) (hle1 j))).mp hent i
        (Finset.mem_univ i)
    -- `negMulLog (p i) = 0` with `p i ≥ 0` forces `p i ∈ {0, 1}`.
    have hdich : ∀ i, p i = 0 ∨ p i = 1 := fun i => (negMulLog_eq_zero (h0 i)).mp (hterm i)
    -- Since `∑ p = 1 ≠ 0`, some `p k ≠ 0`, hence `p k = 1`; the rest then vanish.
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
    have hpk : p k = 1 := (hdich k).resolve_left hk
    refine ⟨k, hpk, fun j hj => ?_⟩
    have hsub : ∑ i ∈ Finset.univ.erase k, p i = 0 := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ k), hsum, hpk]; norm_num
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h0 i)).mp hsub j
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  · rintro ⟨i, hi1, hi0⟩
    rw [entropy_eq, Finset.sum_eq_single i (fun j _ hji => by rw [hi0 j hji, negMulLog_zero])
      (fun hi => absurd (Finset.mem_univ i) hi), hi1, negMulLog_one]

/-- **Weighted grouping bound** for the (un-normalized) Shannon entropy, the analytic kernel of
Fannes' inequality (Nielsen–Chuang, *Quantum Computation and Quantum Information*, Theorem 11.6,
eq. (11.48)): for **nonnegative** weights `a : ι → ℝ` — *not* required to sum to `1` —

`∑ i, negMulLog (a i) ≤ (∑ i, a i) * log (card ι) + negMulLog (∑ i, a i)`.

Writing `Δ := ∑ i, a i`, this is the exact identity `∑ η(aᵢ) = Δ · H(a / Δ) + η(Δ)` combined with
the maximum-entropy bound `H(a / Δ) ≤ log (card ι)` (`entropy_le_log_card`); it generalizes
`entropy_le_log_card` from a probability distribution (`Δ = 1`, where it reduces to `H ≤ log d`) to
an arbitrary nonnegative weight vector. In Fannes' inequality it is applied to `aᵢ = |rᵢ - sᵢ|`,
the absolute differences of the sorted eigenvalue spectra of two density operators, to bound
`∑ η(|rᵢ - sᵢ|) ≤ Δ · log d + η(Δ)`.

The proof rescales `a` to the probability distribution `pᵢ := aᵢ / Δ` (when `Δ > 0`) and expands
`η(Δ · pᵢ) = pᵢ · η(Δ) + Δ · η(pᵢ)` via `negMulLog_mul`; the degenerate `Δ = 0` case forces every
`aᵢ = 0`, whence both sides vanish. -/
theorem sum_negMulLog_le {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    ∑ i, negMulLog (a i) ≤ (∑ i, a i) * Real.log (Fintype.card ι) + negMulLog (∑ i, a i) := by
  set Δ : ℝ := ∑ i, a i with hΔ
  have hΔ0 : 0 ≤ Δ := Finset.sum_nonneg fun i _ ↦ ha i
  rcases hΔ0.eq_or_lt with h0 | hpos
  · -- Degenerate case `Δ = 0`: every `a i = 0`, so both sides are `0`.
    have hall : ∀ i, a i = 0 := fun i ↦
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ ha j).mp h0.symm i (Finset.mem_univ i)
    rw [← h0]
    simp [hall]
  · -- Main case `Δ > 0`: rescale to the probability distribution `p i = a i / Δ`.
    have hne : Nonempty ι := by
      rw [← not_isEmpty_iff]
      intro h
      rw [hΔ, Finset.univ_eq_empty, Finset.sum_empty] at hpos
      exact lt_irrefl 0 hpos
    set p : ι → ℝ := fun i ↦ a i / Δ with hp
    have hp_nn : ∀ i, 0 ≤ p i := fun i ↦ div_nonneg (ha i) hΔ0
    have hp_sum : ∑ i, p i = 1 := by
      have e : ∑ i, p i = (∑ i, a i) * Δ⁻¹ := by
        simp only [hp, div_eq_mul_inv]
        rw [← Finset.sum_mul]
      rw [e, ← hΔ, mul_inv_cancel₀ hpos.ne']
    have hkey : entropy p ≤ Real.log (Fintype.card ι) := entropy_le_log_card hp_nn hp_sum
    have hax : ∀ i, a i = Δ * p i := fun i ↦ by rw [hp]; field_simp
    calc ∑ i, negMulLog (a i)
        = ∑ i, (p i * negMulLog Δ + Δ * negMulLog (p i)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hax i, negMulLog_mul]
      _ = (∑ i, p i) * negMulLog Δ + Δ * ∑ i, negMulLog (p i) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      _ = negMulLog Δ + Δ * entropy p := by rw [hp_sum, one_mul, entropy_eq]
      _ ≤ negMulLog Δ + Δ * Real.log (Fintype.card ι) := by gcongr
      _ = Δ * Real.log (Fintype.card ι) + negMulLog Δ := by ring

/-- **Grouping inequality** (the single-distribution kernel of Fano's inequality): for a
probability distribution `r : ι → ℝ` and a distinguished element `i₀`, the Shannon entropy is
bounded by the `q`-ary entropy of the "error probability" `1 - r i₀`:
`H(r) ≤ H_q(1 - r i₀)` with `q = |ι|`. Equivalently `entropy r ≤ binEntropy (1 - r i₀) +
(1 - r i₀) · log (|ι| - 1)`. Averaging this per-symbol over a conditioning variable yields
Fano's inequality. -/
theorem entropy_le_qaryEntropy {r : ι → ℝ} (hr_nn : ∀ i, 0 ≤ r i) (hr_sum : ∑ i, r i = 1)
    (i₀ : ι) : entropy r ≤ qaryEntropy (Fintype.card ι) (1 - r i₀) := by
  classical
  have : Nonempty ι := ⟨i₀⟩
  set e : ℝ := 1 - r i₀ with he_def
  set t : Finset ι := Finset.univ.erase i₀ with ht_def
  -- Mass on the complement of `i₀` is exactly the error probability `e`.
  have ht_sum : ∑ i ∈ t, r i = e := by
    have := Finset.add_sum_erase Finset.univ r (Finset.mem_univ i₀)
    rw [he_def]; linarith [this, hr_sum]
  -- The `q - 1` cast in `qaryEntropy` reconciles with the real-valued `card - 1`.
  have hcast : ((Fintype.card ι : ℤ) - 1 : ℤ) = ((Fintype.card ι : ℝ) - 1 : ℝ) := by push_cast; ring
  -- Unfold the `q`-ary entropy and split the entropy sum off at the `i₀` term.
  rw [qaryEntropy_eq_log_add_binEntropy, binEntropy_eq_negMulLog_add_negMulLog_one_sub, hcast,
    show (1 : ℝ) - e = r i₀ by rw [he_def]; ring,
    entropy_eq, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀), ← ht_def]
  -- The `negMulLog (r i₀)` terms cancel; it suffices to bound the complement sum `(★)`.
  suffices h : ∑ i ∈ t, negMulLog (r i) ≤ negMulLog e + e * Real.log ((Fintype.card ι : ℝ) - 1) by
    linarith
  rcases t.eq_empty_or_nonempty with ht0 | ht1
  · -- `|ι| = 1`: the complement is empty, so `e = 0` and both sides vanish.
    have he0 : e = 0 := by rw [← ht_sum, ht0, Finset.sum_empty]
    rw [ht0, Finset.sum_empty, he0, negMulLog_zero, zero_mul, add_zero]
  · -- `|ι| ≥ 2`: average over the complement with uniform weights `m⁻¹`, then rescale.
    set m : ℝ := (t.card : ℝ) with hm_def
    have hm_pos : 0 < m := by
      rw [hm_def]; exact_mod_cast Finset.card_pos.mpr ht1
    have hm_card : m = (Fintype.card ι : ℝ) - 1 := by
      rw [hm_def, ht_def, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
        Nat.cast_sub Fintype.card_pos, Nat.cast_one]
    have hjensen :
        ∑ i ∈ t, m⁻¹ • negMulLog (r i) ≤ negMulLog (∑ i ∈ t, m⁻¹ • r i) := by
      refine concaveOn_negMulLog.le_map_sum (fun i _ ↦ by positivity) ?_ (fun i _ ↦ hr_nn i)
      rw [Finset.sum_const, nsmul_eq_mul, ← hm_def, mul_inv_cancel₀ hm_pos.ne']
    have harg : ∑ i ∈ t, m⁻¹ • r i = m⁻¹ * e := by
      rw [← Finset.smul_sum, ht_sum, smul_eq_mul]
    rw [← Finset.smul_sum, smul_eq_mul, harg] at hjensen
    -- Multiply the Jensen bound through by `m > 0` and simplify `m · negMulLog (e / m)`.
    calc ∑ i ∈ t, negMulLog (r i)
        = m * (m⁻¹ * ∑ i ∈ t, negMulLog (r i)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hm_pos.ne', one_mul]
      _ ≤ m * negMulLog (m⁻¹ * e) := by gcongr
      _ = negMulLog e + e * Real.log m := by
          rw [negMulLog_mul, negMulLog_inv]; field_simp; ring
      _ = negMulLog e + e * Real.log ((Fintype.card ι : ℝ) - 1) := by rw [hm_card]

/-- **Sub-normalized cross-entropy bound** (the shared kernel of the support-aware Gibbs
inequalities): for `p, q : ι → ℝ` with `p ≥ 0`, `q ≥ 0`, the support condition `q i = 0 → p i = 0`
(the support of `p` is contained in that of `q`), and `q` carrying *at most* the total mass of `p`
(`∑ q ≤ ∑ p`), the Shannon entropy of `p` is at most the cross-entropy `-∑ p_i log q_i`.

The per-term Gibbs bound `p i * log (q i / p i) ≤ q i - p i` (robust to `q i = 0`, where then
`p i = 0`) sums to `∑ p_i log (q_i / p_i) ≤ ∑ (q i - p i) = ∑ q - ∑ p ≤ 0`; splitting the left side
as `∑ p_i log q_i - ∑ p_i log p_i` gives `entropy p ≤ -∑ p_i log q_i`. Both the equal-mass
support-aware form (`entropy_le_cross_entropy_of_support_subset`) and the sub-normalized relative
entropy nonnegativity (`relativeEntropy_nonneg_of_sum_le`) are corollaries. -/
theorem entropy_le_cross_entropy_of_sum_le {p q : ι → ℝ}
    (hp_nn : ∀ i, 0 ≤ p i) (hq_nn : ∀ i, 0 ≤ q i) (hsupp : ∀ i, q i = 0 → p i = 0)
    (hqp_sum : ∑ i, q i ≤ ∑ i, p i) :
    entropy p ≤ -∑ i, p i * Real.log (q i) := by
  -- Per-term Gibbs bound `pᵢ log (qᵢ / pᵢ) ≤ qᵢ - pᵢ`, robust to `qᵢ = 0` since then `pᵢ = 0`.
  have hterm : ∀ i, p i * Real.log (q i / p i) ≤ q i - p i := fun i ↦ by
    rcases eq_or_lt_of_le (hq_nn i) with hq0 | hq0
    · simp [← hq0, hsupp i hq0.symm]
    · exact mul_log_div_le_sub_of_nonneg (hp_nn i) hq0
  have h_sum_le : ∑ i, p i * Real.log (q i / p i) ≤ 0 :=
    calc ∑ i, p i * Real.log (q i / p i)
        ≤ ∑ i, (q i - p i) := Finset.sum_le_sum fun i _ ↦ hterm i
      _ = (∑ i, q i) - ∑ i, p i := by rw [Finset.sum_sub_distrib]
      _ ≤ 0 := by linarith
  -- Split `pᵢ log (qᵢ / pᵢ) = pᵢ log qᵢ - pᵢ log pᵢ`, again handling `qᵢ = 0 ⟹ pᵢ = 0`.
  have h_sum_split : ∑ i, p i * Real.log (q i / p i) =
      ∑ i, p i * Real.log (q i) - ∑ i, p i * Real.log (p i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases eq_or_lt_of_le (hp_nn i) with hp0 | hp0
    · simp [← hp0]
    · rw [Real.log_div (fun hq0 ↦ hp0.ne' (hsupp i hq0)) hp0.ne', mul_sub]
  simp only [entropy_eq, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff]
  linarith [h_sum_le, h_sum_split]

/-- **Gibbs' inequality with support condition** (classical Klein's inequality, general
form): for `p, q : ι → ℝ` with `p ≥ 0`, `q ≥ 0`, equal total mass `∑ p = ∑ q`, and the
support condition `q i = 0 → p i = 0` (the support of `p` is contained in that of `q`), the
Shannon entropy of `p` is at most the cross-entropy `-∑ p_i log q_i`.

The equal-mass specialization of `entropy_le_cross_entropy_of_sum_le` (`∑ q ≤ ∑ p` degenerating to
`∑ q = ∑ p`); itself the support-aware generalization of `entropy_le_cross_entropy_of_sum_eq_one`,
absorbing the `q i = 0` terms (where then `p i = 0`) so no strict positivity of `q` is needed. -/
theorem entropy_le_cross_entropy_of_support_subset {p q : ι → ℝ}
    (hp_nn : ∀ i, 0 ≤ p i) (hq_nn : ∀ i, 0 ≤ q i) (hsupp : ∀ i, q i = 0 → p i = 0)
    (hpq_sum : ∑ i, p i = ∑ i, q i) :
    entropy p ≤ -∑ i, p i * Real.log (q i) :=
  entropy_le_cross_entropy_of_sum_le hp_nn hq_nn hsupp hpq_sum.ge

/-- **Gibbs' inequality** (classical Klein's inequality at the discrete-distribution level):
for probability distributions `p, q : ι → ℝ` (`p ≥ 0`, `q > 0`, each summing to one), the
Shannon entropy of `p` is at most the cross-entropy `-∑ p_i log q_i`. Equivalently the
Kullback–Leibler divergence `∑ p_i log (p_i / q_i)` is nonneg.

The strictly-positive-`q` corollary of `entropy_le_cross_entropy_of_support_subset`. The
classical input to Nielsen–Chuang Theorem 11.7 (operator Klein's inequality) via spectral
decomposition + Jensen on `log`. -/
theorem entropy_le_cross_entropy_of_sum_eq_one
    {p q : ι → ℝ} (hp_nn : ∀ i, 0 ≤ p i) (hq_pos : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1) :
    entropy p ≤ -∑ i, p i * Real.log (q i) :=
  entropy_le_cross_entropy_of_support_subset hp_nn (fun i ↦ (hq_pos i).le)
    (fun i hq0 ↦ absurd hq0 (hq_pos i).ne') (by rw [hp_sum, hq_sum])

/-- **Gibbs' inequality** / nonnegativity of the classical relative entropy: `D(p‖q) ≥ 0` for
probability distributions `p`, `q` with `q` strictly positive. -/
theorem relativeEntropy_nonneg {p q : ι → ℝ} (hp_nn : ∀ i, 0 ≤ p i)
    (hq_pos : ∀ i, 0 < q i) (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1) :
    0 ≤ relativeEntropy p q := by
  rw [relativeEntropy_eq_sub]
  have h := entropy_le_cross_entropy_of_sum_eq_one hp_nn hq_pos hp_sum hq_sum
  linarith [entropy_eq_neg_sum_mul_log p]

/-- Nonnegativity of the classical relative entropy under a support condition (absolute
continuity): `D(p‖q) ≥ 0` when `supp p ⊆ supp q` (encoded as `q i = 0 → p i = 0`) and `p`, `q`
have equal total mass. -/
theorem relativeEntropy_nonneg_of_support_subset {p q : ι → ℝ} (hp_nn : ∀ i, 0 ≤ p i)
    (hq_nn : ∀ i, 0 ≤ q i) (hsupp : ∀ i, q i = 0 → p i = 0) (hpq_sum : ∑ i, p i = ∑ i, q i) :
    0 ≤ relativeEntropy p q := by
  rw [relativeEntropy_eq_sub]
  have h := entropy_le_cross_entropy_of_support_subset hp_nn hq_nn hsupp hpq_sum
  linarith [entropy_eq_neg_sum_mul_log p]

/-- **Sub-normalized Gibbs' inequality**: the classical relative entropy `D(p‖q)` is nonnegative
even when the reference `q` carries *at most* the total mass of `p` (`∑ q ≤ ∑ p`), keeping the
nonnegativity `p ≥ 0`, `q ≥ 0` and the absolute-continuity (support) condition `q i = 0 → p i = 0`.
This generalizes `Real.relativeEntropy_nonneg_of_support_subset` (which needs *equal* total mass) to
a *sub-probability* reference: through the shared kernel `entropy_le_cross_entropy_of_sum_le`, the
per-term Gibbs bound `p i * log (q i / p i) ≤ q i - p i` sums to
`-D(p‖q) ≤ ∑ (q i - p i) = ∑ q - ∑ p ≤ 0`, so `D(p‖q) ≥ 0`. Used to deduce `H(Y | X) ≥ 0` from the
relative-entropy expression of the conditional entropy (Nielsen & Chuang, Exercise 11.7), whose
reference distribution `q(x, y) = p(x, y)² / p_X(x)` is only sub-normalized (`∑ q ≤ 1`). -/
theorem relativeEntropy_nonneg_of_sum_le {p q : ι → ℝ} (hp_nn : ∀ i, 0 ≤ p i)
    (hq_nn : ∀ i, 0 ≤ q i) (hsupp : ∀ i, q i = 0 → p i = 0) (hqp_sum : ∑ i, q i ≤ ∑ i, p i) :
    0 ≤ relativeEntropy p q := by
  rw [relativeEntropy_eq_sub]
  have h := entropy_le_cross_entropy_of_sum_le hp_nn hq_nn hsupp hqp_sum
  linarith [entropy_eq_neg_sum_mul_log p]

/-- **Equality condition for Gibbs' inequality** (Nielsen–Chuang Theorem 11.1): for
`p, q : ι → ℝ` with `p ≥ 0`, `q ≥ 0`, equal total mass `∑ p = ∑ q`, and the absolute-continuity
(support) condition `q x = 0 → p x = 0`, the classical relative entropy vanishes if and only if
the distributions are equal, `D(p‖q) = 0 ↔ p = q`.

Together with `Real.relativeEntropy_nonneg_of_support_subset` (the `≥ 0` half at the same
generality) this is the faithful real-valued rendering of N&C Theorem 11.1: "the relative entropy
is non-negative, with equality if and only if `p = q`". The support hypothesis is precisely the
domain on which the real-valued `relativeEntropy` (using the junk value `log 0 = 0`) coincides
with N&C's `H(p‖q)`; where `supp p ⊄ supp q`, N&C set `−p log 0 ≡ +∞` (p. 504), so there
`H(p‖q) = +∞ > 0` with `p ≠ q` — consistent with the theorem but outside the finite real-valued
encoding. The strictly-positive-`q` case is the specialization `hsupp := fun i hq0 ↦ …`.

**Proof.** The support-aware pointwise Gibbs bound `p x * log (q x / p x) ≤ q x - p x` sums to
`-D(p‖q) ≤ ∑ (q x - p x) = 0`. When `D(p‖q) = 0` both sums equal `0`, so by
`Finset.sum_eq_sum_iff_of_le` the bound is an equality termwise; at each `x` either `q x = 0`
(then `p x = 0 = q x` by the support hypothesis) or `q x > 0`, where the strict companion
`Real.mul_log_div_lt_sub_of_ne` forces `p x = q x`. The converse is `Real.relativeEntropy_self`. -/
theorem relativeEntropy_eq_zero_iff {p q : ι → ℝ} (hp_nn : ∀ i, 0 ≤ p i) (hq_nn : ∀ i, 0 ≤ q i)
    (hsupp : ∀ i, q i = 0 → p i = 0) (hpq_sum : ∑ i, p i = ∑ i, q i) :
    relativeEntropy p q = 0 ↔ p = q := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- Support-aware pointwise Gibbs bound; summed it is `-D(p‖q) ≤ 0`, so `D = 0` forces equality.
    have hle : ∀ i ∈ Finset.univ, p i * Real.log (q i / p i) ≤ q i - p i := by
      intro i _
      rcases eq_or_lt_of_le (hq_nn i) with hq0 | hq0
      · simp [← hq0, hsupp i hq0.symm]
      · exact mul_log_div_le_sub_of_nonneg (hp_nn i) hq0
    have hsum_g : ∑ i, p i * Real.log (q i / p i) = 0 := by
      -- Split `p x log (q x / p x) = p x log (q x) - p x log (p x)`, using `p x = 0 → term = 0`
      -- and, on `p x > 0`, that `q x ≠ 0` (else `p x = 0` by `hsupp`).
      have hsplit : ∑ i, p i * Real.log (q i / p i)
          = ∑ i, p i * Real.log (q i) - ∑ i, p i * Real.log (p i) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rcases eq_or_lt_of_le (hp_nn i) with hp0 | hp0
        · simp [← hp0]
        · rw [Real.log_div (fun hq0 ↦ hp0.ne' (hsupp i hq0)) hp0.ne', mul_sub]
      rw [hsplit]
      linarith [relativeEntropy_eq_sub p q, h]
    have hsum_qp : ∑ i, (q i - p i) = 0 := by
      rw [Finset.sum_sub_distrib, hpq_sum, sub_self]
    have hpt := (Finset.sum_eq_sum_iff_of_le hle).mp (hsum_g.trans hsum_qp.symm)
    funext i
    rcases eq_or_lt_of_le (hq_nn i) with hq0 | hq0
    · rw [hsupp i hq0.symm]; exact hq0
    · by_contra hne
      exact absurd (hpt i (Finset.mem_univ i))
        (ne_of_lt (mul_log_div_lt_sub_of_ne (hp_nn i) hq0 hne))
  · rintro rfl
    exact relativeEntropy_self p

/-- **Strict positivity of the relative entropy for distinct distributions**: the "with equality
if and only if `p = q`" clause of Nielsen–Chuang Theorem 11.1 in its sharp contrapositive form —
`D(p‖q) > 0` whenever `p ≠ q`, for `p ≥ 0`, `q ≥ 0` with equal total mass `∑ p = ∑ q` and
`supp p ⊆ supp q` (`q x = 0 → p x = 0`). Combines
`Real.relativeEntropy_nonneg_of_support_subset` with `Real.relativeEntropy_eq_zero_iff`. -/
theorem relativeEntropy_pos_of_ne {p q : ι → ℝ} (hp_nn : ∀ i, 0 ≤ p i) (hq_nn : ∀ i, 0 ≤ q i)
    (hsupp : ∀ i, q i = 0 → p i = 0) (hpq_sum : ∑ i, p i = ∑ i, q i) (hpq : p ≠ q) :
    0 < relativeEntropy p q := by
  refine lt_of_le_of_ne
    (relativeEntropy_nonneg_of_support_subset hp_nn hq_nn hsupp hpq_sum) fun h ↦ ?_
  exact hpq ((relativeEntropy_eq_zero_iff hp_nn hq_nn hsupp hpq_sum).mp h.symm)

/-- **Doubly-stochastic Klein-classical bound**: for probability distributions `p : ι → ℝ` and
`q : κ → ℝ`, and a doubly-stochastic matrix `W : ι → κ → ℝ` (entries nonneg, both row sums and
column sums equal to 1), the bound `∑ᵢ pᵢ * ∑ⱼ Wᵢⱼ * log qⱼ ≤ -entropy p` holds.

**Proof.** Inner Jensen on `Real.log` (concave) gives `∑ⱼ Wᵢⱼ log qⱼ ≤ log rᵢ` where
`rᵢ := ∑ⱼ Wᵢⱼ qⱼ`. The `rᵢ` form a probability distribution (sum to 1 via `W`'s row-sum-1
and `q`'s sum-to-1). Outer classical Gibbs (`entropy_le_cross_entropy_of_sum_eq_one`) on
`(p, r)` gives `entropy p ≤ -∑ᵢ pᵢ log rᵢ`, i.e., `∑ᵢ pᵢ log rᵢ ≤ -entropy p`. Combine.

The classical input to operator Klein's inequality (Nielsen–Chuang Theorem 11.7) via spectral
decomposition: take `Wᵢⱼ := ‖⟨fⱼ, eᵢ⟩‖²` where `eᵢ, fⱼ` are orthonormal eigenbases — `W` is
doubly-stochastic by Parseval. -/
theorem sum_mul_sum_mul_log_le_neg_entropy_of_doubly_stochastic
    {κ : Type*} [Fintype κ]
    {p : ι → ℝ} {q : κ → ℝ} {W : ι → κ → ℝ}
    (hp_nn : ∀ i, 0 ≤ p i) (hq_pos : ∀ j, 0 < q j)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ j, q j = 1)
    (hW_nn : ∀ i j, 0 ≤ W i j)
    (hW_row_sum : ∀ i, ∑ j, W i j = 1)
    (hW_col_sum : ∀ j, ∑ i, W i j = 1) :
    ∑ i, p i * ∑ j, W i j * Real.log (q j) ≤ -entropy p := by
  -- Bridge distribution `rᵢ := ∑ⱼ Wᵢⱼ qⱼ`: inner Jensen on `log` (concave) bounds
  -- `∑ⱼ Wᵢⱼ log qⱼ ≤ log rᵢ`; multiplying by `pᵢ ≥ 0` and summing gives the LHS bound by
  -- `∑ᵢ pᵢ log rᵢ`, which classical Gibbs (`entropy_le_cross_entropy_of_sum_eq_one`) then
  -- bounds by `-entropy p`. `r` is a probability distribution: positive via
  -- `Finset.sum_pos_iff_of_nonneg` on row sum 1, sums to 1 via `sum_comm` + column sum.
  refine (Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left ?_ (hp_nn i)).trans
    (le_neg.mp <| entropy_le_cross_entropy_of_sum_eq_one
      (q := fun i ↦ ∑ j, W i j * q j) hp_nn (fun i ↦ ?_) hp_sum ?_)
  · simpa [smul_eq_mul] using strictConcaveOn_log_Ioi.concaveOn.le_map_sum
      (t := Finset.univ) (w := W i) (p := q)
      (fun j _ ↦ hW_nn i j) (hW_row_sum i) (fun j _ ↦ hq_pos j)
  · refine Finset.sum_pos' (fun j _ ↦ mul_nonneg (hW_nn i j) (hq_pos j).le) ?_
    obtain ⟨j, hj, hj_pos⟩ := (Finset.sum_pos_iff_of_nonneg fun j _ ↦ hW_nn i j).mp
      (hW_row_sum i ▸ one_pos)
    exact ⟨j, hj, mul_pos hj_pos (hq_pos j)⟩
  · simp_rw [Finset.sum_comm (f := fun i j ↦ W i j * q j), ← Finset.sum_mul]
    simp [hW_col_sum, hq_sum]

/-- The set of nonneg real-valued functions on `ι`, on which `entropy` is concave. -/
def entropyDomain (ι : Type*) : Set (ι → ℝ) := Set.univ.pi fun _ ↦ Set.Ici (0 : ℝ)

omit [Fintype ι] in
theorem convex_entropyDomain : Convex ℝ (entropyDomain ι) :=
  convex_pi fun _ _ ↦ convex_Ici 0

/-- **Concavity of Shannon entropy** on the convex set of nonneg-valued functions. Each
summand `p ↦ negMulLog (p i)` is concave via `concaveOn_negMulLog` composed with the
linear projection `p ↦ p i`; then `ConcaveOn.sum` lifts to the Finset-sum. -/
theorem entropy_concave : ConcaveOn ℝ (entropyDomain ι) entropy := by
  refine ConcaveOn.sum convex_entropyDomain fun i _ ↦ ?_
  refine (concaveOn_negMulLog.comp_linearMap
    (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)).subset ?_ convex_entropyDomain
  intro p hp
  exact hp i (Set.mem_univ _)

/-! ### Continuity of `negMulLog` — the analytic kernel of Fannes' inequality

The single-variable estimates behind Nielsen–Chuang Theorem 11.6 (eq. 11.47): `negMulLog`
is its own modulus of continuity on scales `≤ 1/2`, and is monotone up to its maximum at
`e⁻¹`. Stated for `Real.negMulLog` directly so they compose with the spectral development. -/

/-- For `δ ∈ [0, 1/2]`, `η(1 - δ) ≤ η(δ)` where `η = Real.negMulLog`. This is the endpoint
estimate in Fannes' continuity bound (Nielsen–Chuang eq. 11.47): the difference
`φ δ := η δ - η (1 - δ)` is concave on `[0, 1/2]` (its derivative `-log δ - log (1 - δ) - 2`
is strictly decreasing there) and vanishes at both endpoints, hence is nonnegative. -/
theorem negMulLog_one_sub_le {δ : ℝ} (h0 : 0 ≤ δ) (h : δ ≤ 1 / 2) :
    Real.negMulLog (1 - δ) ≤ Real.negMulLog δ := by
  set φ : ℝ → ℝ := fun t => Real.negMulLog t - Real.negMulLog (1 - t) with hφ
  have hcont : ContinuousOn φ (Set.Icc 0 (1 / 2 : ℝ)) :=
    (Real.continuous_negMulLog.sub
      (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id))).continuousOn
  -- `deriv φ t = -log t - log (1 - t) - 2` on the open interval, via the chain rule.
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 2),
      deriv φ t = -Real.log t - Real.log (1 - t) - 2 := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have ht1ne : (1 : ℝ) - t ≠ 0 := by have : t < 1 := by linarith
                                       linarith
    have d1 : HasDerivAt Real.negMulLog (-Real.log t - 1) t :=
      Real.hasDerivAt_negMulLog (ne_of_gt ht0)
    have d2 : HasDerivAt (fun s => Real.negMulLog (1 - s)) ((-Real.log (1 - t) - 1) * (-1)) t :=
      (Real.hasDerivAt_negMulLog ht1ne).comp t ((hasDerivAt_id t).const_sub 1)
    have hφd : HasDerivAt φ (-Real.log t - Real.log (1 - t) - 2) t := by
      rw [hφ]; convert d1.sub d2 using 1; ring
    exact hφd.deriv
  -- `deriv φ` is strictly antitone on the interior, so `φ` is concave.
  have hanti : StrictAntiOn (deriv φ) (interior (Set.Icc 0 (1 / 2 : ℝ))) := by
    rw [interior_Icc]
    intro a ha b hb hab
    rw [hderiv a ha, hderiv b hb]
    obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb
    have hprod : a * (1 - a) < b * (1 - b) := by nlinarith
    have hlog : Real.log (a * (1 - a)) < Real.log (b * (1 - b)) :=
      Real.log_lt_log (mul_pos ha0 (by linarith)) hprod
    rw [Real.log_mul (ne_of_gt ha0) (by linarith),
      Real.log_mul (ne_of_gt hb0) (by linarith)] at hlog
    linarith
  have hconc : ConcaveOn ℝ (Set.Icc 0 (1 / 2 : ℝ)) φ :=
    (StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc _ _) hcont hanti).concaveOn
  -- `φ` is nonnegative on `[0, 1/2]` since it is concave with `φ 0 = φ (1/2) = 0`.
  have key := hconc.min_le_of_mem_Icc (x := 0) (y := 1 / 2) (z := δ)
    (by norm_num) (by norm_num) ⟨h0, h⟩
  have h0' : φ 0 = 0 := by rw [hφ]; simp
  have h12 : φ (1 / 2 : ℝ) = 0 := by rw [hφ]; norm_num
  rw [h0', h12] at key; simp only [min_self] at key; rw [hφ] at key; simp only at key
  linarith [key]

/-- The increment `t ↦ negMulLog t - negMulLog (t + δ)` is monotone (nondecreasing) on
`[0, ∞)` for any `δ ≥ 0`: its derivative `log (t + δ) - log t` is nonnegative. Equivalently,
by concavity of `negMulLog` the increment `negMulLog (t + δ) - negMulLog t` shrinks as `t`
grows. Both directions of `Real.abs_negMulLog_sub_le` reduce to this monotonicity. -/
theorem monotoneOn_negMulLog_sub_add {δ : ℝ} (hδ : 0 ≤ δ) :
    MonotoneOn (fun t => Real.negMulLog t - Real.negMulLog (t + δ)) (Set.Ici (0 : ℝ)) := by
  have hgderiv : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s => Real.negMulLog s - Real.negMulLog (s + δ))
        (Real.log (t + δ) - Real.log t) t := by
    intro t ht
    have ht'ne : t + δ ≠ 0 := ne_of_gt (by positivity)
    have d1 : HasDerivAt Real.negMulLog (-Real.log t - 1) t :=
      Real.hasDerivAt_negMulLog (ne_of_gt ht)
    have d2 : HasDerivAt (fun s => Real.negMulLog (s + δ)) (-Real.log (t + δ) - 1) t := by
      have := (Real.hasDerivAt_negMulLog ht'ne).comp t ((hasDerivAt_id t).add_const δ)
      simpa [Function.comp_def] using this
    convert d1.sub d2 using 1; ring
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · exact (Real.continuous_negMulLog.sub
      (Real.continuous_negMulLog.comp (continuous_id.add continuous_const))).continuousOn
  · rw [interior_Ici]
    exact fun t ht => (hgderiv t ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t ht
    rw [(hgderiv t ht).deriv]
    have : Real.log t ≤ Real.log (t + δ) := Real.log_le_log ht (by linarith)
    linarith

/-- Single-increment form of Fannes' continuity bound: for a base point `y ≥ 0` and a step
`δ ∈ [0, 1/2]` with `y + δ ≤ 1`, `|negMulLog (y + δ) - negMulLog y| ≤ negMulLog δ`. The upper
bound is subadditivity of `negMulLog` (increment monotonicity evaluated at `0 ≤ y`); the lower
bound is the same monotonicity up to `y ≤ 1 - δ` combined with `negMulLog_one_sub_le`. -/
theorem abs_negMulLog_add_sub_le {y δ : ℝ} (hy : 0 ≤ y) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2)
    (hyδ : y + δ ≤ 1) :
    |Real.negMulLog (y + δ) - Real.negMulLog y| ≤ Real.negMulLog δ := by
  set g : ℝ → ℝ := fun t => Real.negMulLog t - Real.negMulLog (t + δ) with hg
  have hmono := monotoneOn_negMulLog_sub_add hδ
  have hgy : Real.negMulLog (y + δ) - Real.negMulLog y = -(g y) := by rw [hg]; ring
  rw [hgy, abs_neg, abs_le]
  refine ⟨?_, ?_⟩
  · have hstep : g 0 ≤ g y := hmono Set.self_mem_Ici (Set.mem_Ici.mpr hy) hy
    have hg0 : g 0 = -Real.negMulLog δ := by rw [hg]; simp
    rw [hg0] at hstep; linarith
  · have h1δ : (0 : ℝ) ≤ 1 - δ := by linarith
    have hstep : g y ≤ g (1 - δ) :=
      hmono (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr h1δ) (by linarith)
    have hg1 : g (1 - δ) = Real.negMulLog (1 - δ) := by rw [hg]; simp
    rw [hg1] at hstep
    linarith [negMulLog_one_sub_le hδ hδ2]

/-- **Continuity kernel of Fannes' inequality** (Nielsen–Chuang Theorem 11.6, eq. 11.47): for
`x, y ∈ [0, 1]` with `|x - y| ≤ 1/2`,
`|negMulLog x - negMulLog y| ≤ negMulLog |x - y|`.
So `η = Real.negMulLog` serves as its own modulus of continuity on scales `≤ 1/2`. Applied to
paired sorted eigenvalues `x = rᵢ`, `y = sᵢ ∈ [0, 1]` of density operators, this is the
per-eigenvalue estimate summed in the proof of Fannes' inequality. -/
theorem abs_negMulLog_sub_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (hxy : |x - y| ≤ 1 / 2) :
    |Real.negMulLog x - Real.negMulLog y| ≤ Real.negMulLog |x - y| := by
  rcases le_total y x with hyx | hxy'
  · have hδ0 : 0 ≤ x - y := by linarith
    have habs : |x - y| = x - y := abs_of_nonneg hδ0
    rw [habs]
    have key := abs_negMulLog_add_sub_le (y := y) (δ := x - y) hy0 hδ0 (habs ▸ hxy) (by linarith)
    have hx_eq : y + (x - y) = x := by ring
    rwa [hx_eq] at key
  · have hδ0 : 0 ≤ y - x := by linarith
    have habs : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_nonneg hδ0
    rw [habs, abs_sub_comm]
    have key := abs_negMulLog_add_sub_le (y := x) (δ := y - x) hx0 hδ0 (habs ▸ hxy) (by linarith)
    have hy_eq : x + (y - x) = y := by ring
    rwa [hy_eq] at key

/-- `Real.negMulLog` is strictly increasing on `[0, e⁻¹]`, i.e. on the interval up to its
maximum: there `deriv negMulLog x = -log x - 1 > 0`. Used to lift Fannes' bound from the
summed eigenvalue-difference `Δ` to the trace distance `T ≥ Δ` when `T ≤ e⁻¹`
(monotonicity of `η` on `[0, e⁻¹]`, Nielsen–Chuang eq. 11.49). -/
theorem strictMonoOn_negMulLog_Icc :
    StrictMonoOn Real.negMulLog (Set.Icc 0 (Real.exp (-1))) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) Real.continuous_negMulLog.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  obtain ⟨hx0, hx1⟩ := hx
  rw [Real.deriv_negMulLog (ne_of_gt hx0)]
  have : Real.log x < -1 := by
    have := Real.log_lt_log hx0 hx1
    rwa [Real.log_exp] at this
  linarith

/-- `Real.negMulLog` attains its maximum value `e⁻¹` at `x = e⁻¹`, so `negMulLog x ≤ e⁻¹` for all
`x ≥ 0`. (The hypothesis `0 ≤ x` is essential: `negMulLog` uses `Real.log |x|`, so for `x < 0` the
value `-x * log x` is unbounded above.) This is the constant appearing in the weaker unconditional
form of Fannes' inequality (Nielsen–Chuang eq. (11.45)). The proof reduces to the tangent-line
bound `log t ≤ t - 1` (`Real.log_le_sub_one_of_pos`) applied at `t = 1 / (x * e)`, which gives
`-log x ≤ 1 / (x * e)`; multiplying by `x` yields `-x log x ≤ e⁻¹`. -/
theorem negMulLog_le_exp_neg_one {x : ℝ} (hx : 0 ≤ x) : Real.negMulLog x ≤ Real.exp (-1) := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · rw [Real.negMulLog_zero]; exact (Real.exp_pos _).le
  · rw [Real.negMulLog]
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hxe : (0 : ℝ) < x * Real.exp 1 := by positivity
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (x * Real.exp 1) by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hxe), Real.log_one, zero_sub,
      Real.log_mul (ne_of_gt hx) (ne_of_gt he), Real.log_exp] at h
    rw [Real.exp_neg]
    have hstep : -Real.log x ≤ 1 / (x * Real.exp 1) := by linarith
    calc -x * Real.log x = x * (-Real.log x) := by ring
      _ ≤ x * (1 / (x * Real.exp 1)) := mul_le_mul_of_nonneg_left hstep (le_of_lt hx)
      _ = (Real.exp 1)⁻¹ := by field_simp

/-- Shannon entropy of the symmetric two-point distribution `((1 + t)/2, (1 - t)/2)` is at most
that of `(p, 1 - p)` whenever `|2p - 1| ≤ t ≤ 1` and `p ∈ [0, 1]`. Both sides are binary entropies
(`entropy_fin_two_eq_binEntropy`), and `binEntropy` is antitone on `[1/2, 1]`
(`binEntropy_strictAntiOn`) and symmetric (`binEntropy_one_sub`), so the claim reduces to
`max p (1 - p) ≤ (1 + t)/2`, i.e. `|2p - 1| ≤ t`. -/
theorem entropy_pair_le {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ht1 : t ≤ 1) (h : |2 * p - 1| ≤ t) :
    entropy ![(1 + t) / 2, (1 - t) / 2] ≤ entropy ![p, 1 - p] := by
  have ht0 : 0 ≤ t := le_trans (abs_nonneg _) h
  rw [entropy_fin_two_eq_binEntropy p, show (1 - t) / 2 = 1 - (1 + t) / 2 by ring,
    entropy_fin_two_eq_binEntropy]
  have hmem : (1 + t) / 2 ∈ Set.Icc (2⁻¹ : ℝ) 1 := ⟨by linarith, by linarith⟩
  rcases le_total p (2⁻¹ : ℝ) with hp | hp
  · rw [← binEntropy_one_sub p]
    refine binEntropy_strictAntiOn.antitoneOn ⟨by linarith, by linarith⟩ hmem ?_
    have := (abs_le.mp h).1; linarith
  · refine binEntropy_strictAntiOn.antitoneOn ⟨hp, hp1⟩ hmem ?_
    have := (abs_le.mp h).2; linarith

/-- Strict version of `entropy_pair_le`: for `|2p - 1| < t ≤ 1` and `p ∈ [0, 1]`, the Shannon
entropy of `((1 + t)/2, (1 - t)/2)` is strictly below that of `(p, 1 - p)`. -/
theorem entropy_pair_lt {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ht1 : t ≤ 1) (h : |2 * p - 1| < t) :
    entropy ![(1 + t) / 2, (1 - t) / 2] < entropy ![p, 1 - p] := by
  have ht0 : 0 ≤ t := le_trans (abs_nonneg _) h.le
  rw [entropy_fin_two_eq_binEntropy p, show (1 - t) / 2 = 1 - (1 + t) / 2 by ring,
    entropy_fin_two_eq_binEntropy]
  have hmem : (1 + t) / 2 ∈ Set.Icc (2⁻¹ : ℝ) 1 := ⟨by linarith, by linarith⟩
  rcases le_total p (2⁻¹ : ℝ) with hp | hp
  · rw [← binEntropy_one_sub p]
    refine binEntropy_strictAntiOn ⟨by linarith, by linarith⟩ hmem ?_
    have := (abs_lt.mp h).1; linarith
  · refine binEntropy_strictAntiOn ⟨hp, hp1⟩ hmem ?_
    have := (abs_lt.mp h).2; linarith

end Real
