/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Field

/-!
# Collision probability and collision entropy

For a finite type `ι` and a function `p : ι → ℝ` (interpreted as a probability mass function when
`p i ∈ [0, 1]` and `∑ i, p i = 1`), the **collision probability** and **collision entropy**
(Rényi entropy of order 2) are

`Real.collisionProb p := ∑ i, (p i) ^ 2`,
`Real.collisionEntropy p := -Real.logb 2 (collisionProb p)`.

The collision probability is `Pr[X = X'] = ∑ₓ p(x)²`, the probability that two independent draws
from `p` collide; the collision entropy `Hc(p) = -log₂ (∑ₓ p(x)²)` measures its randomness in bits.
Base `2` (bits) is used — as in Nielsen & Chuang §12.6 — since the applications compare `Hc` to the
number of output bits `m = log₂ |B|` of a hash function.

The function is defined on raw `ι → ℝ` input, mirroring the `Real.entropy` convention of accepting
any real input and providing distribution-hypothesis-driven API lemmas separately.

## Main definitions

- `Real.collisionProb : (ι → ℝ) → ℝ`
- `Real.collisionEntropy : (ι → ℝ) → ℝ`

## Main results

- `Real.collisionProb_nonneg`: `0 ≤ collisionProb p` (a sum of squares), unconditionally.
- `Real.collisionProb_le_one`: `collisionProb p ≤ 1` for a probability distribution.
- `Real.collisionProb_pos`: `0 < collisionProb p` for a probability distribution (some atom is
  nonzero, and its square lower-bounds the sum).
- `Real.inv_card_le_collisionProb`: `(card ι)⁻¹ ≤ collisionProb p` — the uniform distribution
  minimizes the collision probability (Cauchy–Schwarz, `sq_sum_le_card_mul_sum_sq`).
- `Real.collisionProb_uniform`: the uniform distribution has collision probability `(card ι)⁻¹`.
- `Real.collisionEntropy_uniform`: the uniform distribution attains collision entropy
  `log₂ (card ι)`.
- `Real.collisionEntropy_nonneg`: `0 ≤ collisionEntropy p` for a probability distribution.
- `Real.collisionEntropy_le_logb_card`: `collisionEntropy p ≤ log₂ (card ι)`, with equality for the
  uniform distribution (`collisionEntropy_uniform`); the collision-entropy analogue of
  `Real.entropy_le_log_card`. It is the `Hc(X) ≤ log₂ |X|` half of the pair with
  `Real.entropy_le_log_card` (`H(X) ≤ log |X|`).
- `Real.log_collisionProb_inv_le_entropy`: `log (collisionProb p)⁻¹ ≤ entropy p`, i.e. Shannon
  entropy dominates collision entropy `Hc(X) ≤ H(X)` (in nats). This is the `H ≥ Hc` first
  inequality of Nielsen & Chuang Theorem 12.16, in its unconditional per-outcome form.
- `Real.collisionEntropy_le_entropy_div_log_two`: the base-`2` restatement
  `collisionEntropy p ≤ entropy p / log 2` (both sides in bits).

`H(X) ≥ Hc(X)` is an instance of the monotonicity of Rényi entropy in its order (`H = H₁ ≥ H₂ =
Hc`); it is proved here by Gibbs' inequality against a tilted reference (see
`log_collisionProb_inv_le_entropy`).
-/

@[expose] public section

namespace Real

variable {ι : Type*} [Fintype ι]

/-- The **collision probability** of `p : ι → ℝ`: `∑ i, (p i) ^ 2`. For a probability mass function
this is `Pr[X = X'] = ∑ₓ p(x)²`, the probability that two independent draws collide. -/
noncomputable def collisionProb (p : ι → ℝ) : ℝ := ∑ i, p i ^ 2

theorem collisionProb_eq (p : ι → ℝ) : collisionProb p = ∑ i, p i ^ 2 := rfl

/-- The collision probability is nonnegative (a sum of squares), for any input. -/
theorem collisionProb_nonneg (p : ι → ℝ) : 0 ≤ collisionProb p :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- For a probability distribution (`0 ≤ p i`, `∑ p = 1`) the collision probability is at most `1`:
each `p i ≤ 1`, so `∑ p i ² ≤ ∑ p i = 1`. -/
theorem collisionProb_le_one {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    collisionProb p ≤ 1 := by
  have hle1 : ∀ i, p i ≤ 1 := fun i ↦
    (Finset.single_le_sum (fun j _ ↦ h0 j) (Finset.mem_univ i)).trans hsum.le
  rw [collisionProb_eq, ← hsum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [sq]
  exact mul_le_of_le_one_right (h0 i) (hle1 i)

/-- The collision probability of a probability distribution is strictly positive: the total mass
`1 ≠ 0` forces some atom `p k ≠ 0`, and `p k ² > 0` lower-bounds the sum of nonnegative squares. -/
theorem collisionProb_pos {p : ι → ℝ} (hsum : ∑ i, p i = 1) : 0 < collisionProb p := by
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  rw [collisionProb_eq]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun i _ ↦ sq_nonneg (p i)) (Finset.mem_univ k))
  positivity

-- A probability distribution's index type is nonempty (its mass is `1 ≠ 0`), so its cardinality
-- is positive. Shared by `inv_card_le_collisionProb` and `collisionEntropy_le_logb_card`.
private theorem card_pos_of_sum_eq_one {p : ι → ℝ} (hsum : ∑ i, p i = 1) :
    (0 : ℝ) < Fintype.card ι := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum; norm_num at hsum
  · exact_mod_cast Fintype.card_pos

/-- **The uniform distribution minimizes the collision probability**: `(card ι)⁻¹ ≤ collisionProb p`
for any probability distribution. This is Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`):
`1 = (∑ p)² ≤ |ι| · ∑ p²`. It gives the collision-entropy bound `Hc(X) ≤ log₂ |X|`
(`collisionEntropy_le_logb_card`). -/
theorem inv_card_le_collisionProb {p : ι → ℝ} (hsum : ∑ i, p i = 1) :
    (Fintype.card ι : ℝ)⁻¹ ≤ collisionProb p := by
  have hcard : (0 : ℝ) < Fintype.card ι := card_pos_of_sum_eq_one hsum
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := p)
  rw [Finset.card_univ, hsum, one_pow] at hcs
  -- `hcs : 1 ≤ ↑(card ι) * ∑ i, p i ^ 2`; divide by `card ι > 0`.
  rw [collisionProb_eq, inv_le_iff_one_le_mul₀ hcard, mul_comm]
  exact hcs

/-- The uniform distribution `i ↦ (card ι)⁻¹` has collision probability `(card ι)⁻¹`. -/
theorem collisionProb_uniform :
    collisionProb (fun _ : ι ↦ (Fintype.card ι : ℝ)⁻¹) = (Fintype.card ι : ℝ)⁻¹ := by
  rw [collisionProb_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rcases eq_or_ne (Fintype.card ι : ℝ) 0 with h | h
  · rw [h]; simp
  · rw [sq, ← mul_assoc, mul_inv_cancel₀ h, one_mul]

/-- The **collision entropy** (Rényi entropy of order 2) of `p : ι → ℝ`, in bits:
`Hc(p) = -log₂ (∑ᵢ (p i)²)`. -/
noncomputable def collisionEntropy (p : ι → ℝ) : ℝ := -Real.logb 2 (collisionProb p)

theorem collisionEntropy_eq (p : ι → ℝ) :
    collisionEntropy p = -Real.logb 2 (collisionProb p) := rfl

/-- The uniform distribution `i ↦ (card ι)⁻¹` attains collision entropy `log₂ (card ι)`. -/
theorem collisionEntropy_uniform :
    collisionEntropy (fun _ : ι ↦ (Fintype.card ι : ℝ)⁻¹) = Real.logb 2 (Fintype.card ι) := by
  rw [collisionEntropy_eq, collisionProb_uniform, Real.logb_inv, neg_neg]

/-- The collision entropy of a probability distribution is nonnegative: the collision probability
lies in `(0, 1]`, so `log₂ ≤ 0`. -/
theorem collisionEntropy_nonneg {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    0 ≤ collisionEntropy p := by
  rw [collisionEntropy_eq, neg_nonneg]
  exact Real.logb_nonpos (by norm_num) (collisionProb_nonneg p) (collisionProb_le_one h0 hsum)

/-- **Collision entropy is at most `log₂ (card ι)`** (attained by the uniform distribution, see
`collisionEntropy_uniform`): the collision-entropy analogue of `Real.entropy_le_log_card`. Proof:
`(card ι)⁻¹ ≤ collisionProb p` (`inv_card_le_collisionProb`) and monotonicity of `log₂`. -/
theorem collisionEntropy_le_logb_card {p : ι → ℝ} (hsum : ∑ i, p i = 1) :
    collisionEntropy p ≤ Real.logb 2 (Fintype.card ι) := by
  have hcard : (0 : ℝ) < Fintype.card ι := card_pos_of_sum_eq_one hsum
  rw [collisionEntropy_eq, neg_le, ← Real.logb_inv]
  exact Real.logb_le_logb_of_le (by norm_num) (inv_pos.mpr hcard) (inv_card_le_collisionProb hsum)

/-- **Shannon entropy dominates collision entropy** (natural-log form): for a probability
distribution `p`, `log (collisionProb p)⁻¹ ≤ entropy p`, i.e. `Hc(X) ≤ H(X)` in nats. This is the
`H ≥ Hc` half of Nielsen & Chuang Theorem 12.16's first inequality (in its unconditional,
per-outcome form); it is the Rényi-order monotonicity `H₁ ≥ H₂`.

Proof: Gibbs' inequality (`entropy_le_cross_entropy_of_support_subset`) against the *tilted*
reference `q i := (p i)² / collisionProb p`, itself a probability distribution since
`∑ᵢ (p i)² = collisionProb p`. Its cross-entropy `-∑ᵢ p i · log (q i)` evaluates to
`2 · entropy p + log (collisionProb p)`, so Gibbs reads `entropy p ≤ 2 · entropy p +
log (collisionProb p)`, i.e. `-log (collisionProb p) = log (collisionProb p)⁻¹ ≤ entropy p`. -/
theorem log_collisionProb_inv_le_entropy {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    Real.log (collisionProb p)⁻¹ ≤ entropy p := by
  have hPc_pos : 0 < collisionProb p := collisionProb_pos hsum
  have hPc_ne : collisionProb p ≠ 0 := hPc_pos.ne'
  -- The tilted reference `q i = (p i)² / collisionProb p` is a probability distribution.
  have hq_nn : ∀ i, 0 ≤ p i ^ 2 / collisionProb p := fun i ↦ div_nonneg (sq_nonneg _) hPc_pos.le
  have hq_sum : ∑ i, p i ^ 2 / collisionProb p = 1 := by
    rw [← Finset.sum_div, ← collisionProb_eq, div_self hPc_ne]
  have hsupp : ∀ i, p i ^ 2 / collisionProb p = 0 → p i = 0 := fun i hqi ↦ by
    have hp2 : p i ^ 2 = 0 := (div_eq_zero_iff.mp hqi).resolve_right hPc_ne
    exact pow_eq_zero_iff (by norm_num) |>.mp hp2
  have hgibbs := entropy_le_cross_entropy_of_support_subset h0 hq_nn hsupp (hsum.trans hq_sum.symm)
  -- The cross-entropy against `q` evaluates to `2 · entropy p + log (collisionProb p)`.
  have hcross : -∑ i, p i * Real.log (p i ^ 2 / collisionProb p)
      = 2 * entropy p + Real.log (collisionProb p) := by
    have hterm : ∀ i, p i * Real.log (p i ^ 2 / collisionProb p)
        = 2 * (p i * Real.log (p i)) - p i * Real.log (collisionProb p) := fun i ↦ by
      rcases eq_or_lt_of_le (h0 i) with h | h
      · simp [← h]
      · rw [Real.log_div (by positivity) hPc_ne, Real.log_pow]
        push_cast; ring
    calc -∑ i, p i * Real.log (p i ^ 2 / collisionProb p)
        = -∑ i, (2 * (p i * Real.log (p i)) - p i * Real.log (collisionProb p)) := by
          rw [Finset.sum_congr rfl (fun i _ ↦ hterm i)]
      _ = 2 * (-∑ i, p i * Real.log (p i)) + (∑ i, p i) * Real.log (collisionProb p) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]; ring
      _ = 2 * entropy p + Real.log (collisionProb p) := by
          rw [hsum, entropy_eq_neg_sum_mul_log]; ring
  rw [hcross] at hgibbs
  rw [Real.log_inv]
  linarith

/-- **Shannon entropy dominates collision entropy**, base-`2` (bits) form:
`collisionEntropy p ≤ entropy p / log 2` for a probability distribution `p`. The right side is the
Shannon entropy expressed in bits; this is the base-`2` restatement of
`log_collisionProb_inv_le_entropy`, dividing that natural-log bound by `log 2 > 0`. It is the
`Hc(X) ≤ H(X)` first inequality of Nielsen & Chuang Theorem 12.16 (unconditional form). -/
theorem collisionEntropy_le_entropy_div_log_two {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    collisionEntropy p ≤ entropy p / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hrw : collisionEntropy p = Real.log (collisionProb p)⁻¹ / Real.log 2 := by
    rw [collisionEntropy_eq, ← Real.log_div_log, Real.log_inv, neg_div]
  rw [hrw]
  gcongr
  exact log_collisionProb_inv_le_entropy h0 hsum

end Real
