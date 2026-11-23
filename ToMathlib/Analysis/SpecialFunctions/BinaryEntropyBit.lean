/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The binary entropy function measured in bits

Mathlib's `Real.binEntropy` measures the Shannon entropy of a Bernoulli random variable in *nats*,
using the natural logarithm; its maximum value is therefore `Real.log 2`. In much of the
information-theory literature (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
being one example) entropy is measured in *bits*, using the base-`2` logarithm, so that a fair coin
has entropy exactly `1`.

This file records that base-`2` variant, `Real.binEntropyBit`, and its relationship to
`Real.binEntropy` (they differ by the positive scalar `Real.log 2`), then transports the maximum
of `Real.binEntropy` to obtain the clean statement that `Real.binEntropyBit` attains its greatest
value, `1`, exactly at `p = 1 / 2`.

## Main declarations

* `Real.binEntropyBit`: the binary entropy function measured in bits,
  `binEntropyBit p := -(p * logb 2 p) - (1 - p) * logb 2 (1 - p)`.

## Main results

* `Real.binEntropyBit_eq_binEntropy_div_log_two`: `binEntropyBit p = binEntropy p / log 2`.
* `Real.binEntropyBit_eq_neg_mul_logb`: the definition written out with the base-`2` logarithm,
  `binEntropyBit p = -(p * logb 2 p) - (1 - p) * logb 2 (1 - p)`.
* `Real.binEntropyBit_two_inv`: `binEntropyBit (1 / 2) = 1` (a fair coin carries one bit).
* `Real.binEntropyBit_nonneg`: `0 ≤ binEntropyBit p` for `0 ≤ p ≤ 1`.
* `Real.binEntropyBit_le_one`: `binEntropyBit p ≤ 1` for every real `p`.
* `Real.binEntropyBit_eq_one_iff`: `binEntropyBit p = 1 ↔ p = 1 / 2`, so the maximum is attained
  only at `p = 1 / 2`.
* `Real.isGreatest_range_binEntropyBit`: `1` is the greatest value of `binEntropyBit`, packaging
  the attainment (`binEntropyBit_two_inv`) and the bound (`binEntropyBit_le_one`) together.
* `Real.strictConcaveOn_binEntropyBit`: `binEntropyBit` is strictly concave on `[0, 1]`, so the
  concavity inequality is an equality only in the trivial cases.
* `Real.concaveOn_binEntropyBit`: `binEntropyBit` is concave on `[0, 1]` (inequality (11.11) of
  Nielsen & Chuang, Exercise 11.4), the non-strict corollary.

Like `Real.binEntropy`, the function is defined and the bounds hold for all real `p` (not only on
`[0, 1]`), thanks to `Real.log x = Real.log |x|`. The concavity results, following
`Real.strictConcave_binEntropy`, are stated on `[0, 1]`.
-/

open Set

namespace Real

public section

variable {p : ℝ}

/-- The **binary entropy function measured in bits**: the Shannon entropy of a Bernoulli random
variable with success probability `p`, using the base-`2` logarithm, `binEntropyBit p :=
-p * logb 2 p - (1 - p) * logb 2 (1 - p)`. It is the version of `Real.binEntropy` in which a fair
coin carries exactly one bit of entropy. -/
@[pp_nodot] noncomputable def binEntropyBit (p : ℝ) : ℝ :=
  -(p * logb 2 p) - (1 - p) * logb 2 (1 - p)

/-- The bit-valued and nat-valued binary entropies differ by the positive scalar `log 2`:
`binEntropyBit p = binEntropy p / log 2`. This is the change-of-base identity `logb 2 x =
log x / log 2` applied to both terms. -/
theorem binEntropyBit_eq_binEntropy_div_log_two (p : ℝ) :
    binEntropyBit p = binEntropy p / log 2 := by
  simp only [binEntropyBit, binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog_eq_neg, logb]
  ring

/-- The binary entropy in bits, written out with the base-`2` logarithm:
`binEntropyBit p = -(p * logb 2 p) - (1 - p) * logb 2 (1 - p)`. This is the base-`2` analogue of
`binEntropy_eq_negMulLog_add_negMulLog_one_sub`, and a restatement of the definition. -/
theorem binEntropyBit_eq_neg_mul_logb (p : ℝ) :
    binEntropyBit p = -(p * logb 2 p) - (1 - p) * logb 2 (1 - p) := by
  -- the definitional equation lemma, NOT `rfl`: an exported theorem may not unfold the unexposed
  -- def body by kernel reduction under the module system.
  simp only [binEntropyBit]

@[simp] lemma binEntropyBit_zero : binEntropyBit 0 = 0 := by
  simp [binEntropyBit_eq_binEntropy_div_log_two]

@[simp] lemma binEntropyBit_one : binEntropyBit 1 = 0 := by
  simp [binEntropyBit_eq_binEntropy_div_log_two]

/-- A fair coin (`p = 1 / 2`) carries exactly one bit of entropy: `binEntropyBit (1 / 2) = 1`. This
is the maximum value; see `Real.binEntropyBit_le_one` and `Real.binEntropyBit_eq_one_iff`. -/
@[simp] lemma binEntropyBit_two_inv : binEntropyBit 2⁻¹ = 1 := by
  rw [binEntropyBit_eq_binEntropy_div_log_two, binEntropy_two_inv,
    div_self (log_pos (by norm_num)).ne']

/-- The binary entropy in bits is **nonnegative** on the unit interval: `0 ≤ binEntropyBit p` for
`0 ≤ p ≤ 1`. The lower-bound companion to `Real.binEntropyBit_le_one`, obtained from
`Real.binEntropy_nonneg` since `binEntropyBit p = binEntropy p / log 2` with `log 2 ≥ 0`. -/
lemma binEntropyBit_nonneg (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ binEntropyBit p := by
  rw [binEntropyBit_eq_binEntropy_div_log_two]
  exact div_nonneg (binEntropy_nonneg h0 h1) (log_nonneg (by norm_num))

/-- The binary entropy in bits never exceeds `1`: `binEntropyBit p ≤ 1` for every real `p`. Together
with `Real.binEntropyBit_two_inv` this says `1` is the maximum value of the binary entropy. -/
lemma binEntropyBit_le_one : binEntropyBit p ≤ 1 := by
  rw [binEntropyBit_eq_binEntropy_div_log_two, div_le_one (log_pos (by norm_num))]
  exact binEntropy_le_log_two

/-- The binary entropy in bits attains its maximum value `1` **exactly** at `p = 1 / 2`:
`binEntropyBit p = 1 ↔ p = 1 / 2`. This is the full content of Nielsen & Chuang, Exercise 11.3. -/
theorem binEntropyBit_eq_one_iff : binEntropyBit p = 1 ↔ p = 2⁻¹ := by
  rw [binEntropyBit_eq_binEntropy_div_log_two, div_eq_one_iff_eq (log_pos (by norm_num)).ne']
  exact binEntropy_eq_log_two

/-- **The binary entropy function, measured in bits, attains its maximum value of one.** `1` is the
greatest value taken by `binEntropyBit`: it is attained (at `p = 1 / 2`, by
`Real.binEntropyBit_two_inv`) and it is an upper bound (`Real.binEntropyBit_le_one`). -/
theorem isGreatest_range_binEntropyBit : IsGreatest (range binEntropyBit) 1 :=
  ⟨⟨2⁻¹, binEntropyBit_two_inv⟩, by rintro x ⟨p, rfl⟩; exact binEntropyBit_le_one⟩

/-! ### Concavity of the binary entropy -/

/-- **The binary entropy in bits is strictly concave** on `[0, 1]`: for `x ≠ y` in `[0, 1]` and
weights `0 < a`, `0 < b` with `a + b = 1`, one has
`a • binEntropyBit x + b • binEntropyBit y < binEntropyBit (a • x + b • y)`. Equivalently, the
concavity inequality is an equality only in the trivial cases `x = y`, `a = 0`, or `b = 0` — the
precise content of Nielsen & Chuang, Exercise 11.4. Strict concavity is transported from that of
the nat-valued `Real.binEntropy` (`Real.strictConcave_binEntropy`) by scaling with the positive
constant `(log 2)⁻¹`, since `binEntropyBit p = (log 2)⁻¹ • binEntropy p`. -/
theorem strictConcaveOn_binEntropyBit : StrictConcaveOn ℝ (Icc 0 1) binEntropyBit := by
  have h : StrictConcaveOn ℝ (Icc 0 1) (fun p => (log 2)⁻¹ • binEntropy p) :=
    ⟨strictConcave_binEntropy.1, fun x hx y hy hxy a b ha hb hab => by
      have hlt := strictConcave_binEntropy.2 hx hy hxy ha hb hab
      calc a • (log 2)⁻¹ • binEntropy x + b • (log 2)⁻¹ • binEntropy y
          = (log 2)⁻¹ • (a • binEntropy x + b • binEntropy y) := by
            simp only [smul_eq_mul]; ring
        _ < (log 2)⁻¹ • binEntropy (a • x + b • y) :=
            smul_lt_smul_of_pos_left hlt (inv_pos.2 (log_pos (by norm_num)))⟩
  refine h.congr fun p _ => ?_
  change (log 2)⁻¹ • binEntropy p = binEntropyBit p
  rw [smul_eq_mul, binEntropyBit_eq_binEntropy_div_log_two]; ring

/-- **The binary entropy in bits is concave** on `[0, 1]`: for `x, y ∈ [0, 1]` and weights
`0 ≤ a`, `0 ≤ b` with `a + b = 1`, one has
`a • binEntropyBit x + b • binEntropyBit y ≤ binEntropyBit (a • x + b • y)` — inequality (11.11) of
Nielsen & Chuang, Exercise 11.4. It is the non-strict corollary of
`Real.strictConcaveOn_binEntropyBit`. -/
theorem concaveOn_binEntropyBit : ConcaveOn ℝ (Icc 0 1) binEntropyBit :=
  strictConcaveOn_binEntropyBit.concaveOn

end

end Real
