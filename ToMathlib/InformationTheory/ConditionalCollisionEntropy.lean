/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.CollisionEntropy
public import ToMathlib.Analysis.SpecialFunctions.JointEntropy

/-!
# Conditional collision entropy and the privacy-amplification tail bound

For a finite joint distribution `p : ι × κ → ℝ` of a pair of random variables `(X, U)` (a
probability mass function when `p ≥ 0` and `∑ p = 1`), this file develops the **conditional
collision entropy** `Hc(X | U = u)` — the collision entropy (Rényi entropy of order 2) of the
conditional distribution of `X` given the *specific* value `U = u` — and proves the tail bound
underlying privacy amplification and information reconciliation.

Following the `Real.marginalFst`/`Real.marginalSnd` convention of
`ToMathlib.Analysis.SpecialFunctions.JointEntropy`, `X` is the first coordinate `ι` and `U` the
second coordinate `κ`, so `marginalFst p = p_X` and `marginalSnd p = p_U`.

## Main definitions

- `Real.condDistribGivenSnd p u`: the conditional distribution `x ↦ p(x, u) / p_U(u)` of `X`
  given `U = u`.
- `Real.condCollisionProb p u`: `Pc(X | U = u) = ∑ₓ p(x | u)²`.
- `Real.condCollisionEntropy p u`: `Hc(X | U = u) = -log₂ (∑ₓ p(x | u)²)`.

## Main results

- `Real.marginalSnd_sq_mul_condCollisionProb`: the weighting identity
  `p_U(u)² · Pc(X | U = u) = ∑ₓ p(x, u)²` (valid even where `p_U(u) = 0`, both sides then `0`).
- `Real.sum_marginalSnd_sq_mul_condCollisionProb_le`: `∑ᵤ p_U(u)² · Pc(X | U = u) ≤ Pc(X)`, i.e.
  the joint collision probability is dominated by the marginal collision probability
  (`Finset.sum_sq_le_sq_sum_of_nonneg`).
- `Real.condEntropy_eq_sum_marginalSnd_mul_entropy`: the **chain rule** for the Shannon conditional
  entropy, `H(X | U) = ∑ᵤ p_U(u) · H(X | U = u)` (with `H(X | U = u)` the Shannon entropy of
  `condDistribGivenSnd p u`).
- `Real.log_inv_le_condEntropy_of_condCollisionProb_le`: a uniform bound `Pc(X | U = u) ≤ c` on the
  conditional collision probability lower-bounds the Shannon conditional entropy,
  `log c⁻¹ ≤ H(X | U)` — the ensemble-independent skeleton of SIC/2-design accessible-information
  bounds.
- `Real.prob_condCollisionEntropy_ge` — **Nielsen & Chuang, Theorem 12.17**: for a security
  parameter `s > 0`, with probability at least `1 - 2⁻ˢ` (measured by `p_U`) the value `U = u`
  satisfies `Hc(X | U = u) ≥ Hc(X) - 2·log₂|U| - 2s`. The proof combines the marginal-domination
  bound above with a Cauchy–Schwarz / Markov argument (`sq_sum_le_card_mul_sum_sq`) applied to the
  "bad" set `{u : Hc(X | U = u) < Hc(X) - 2·log₂|U| - 2s}`, translated between collision entropy
  and collision probability through strict monotonicity of `log₂`.

The exponent `-2·log₂|U|` matches Nielsen & Chuang; the Cauchy–Schwarz argument in fact yields the
sharper `-log₂|U|`, so the stated bound holds with room to spare (the slack `2⁻ˢ / √|U|`).
-/

@[expose] public section

namespace Real

variable {ι κ : Type*} [Fintype ι]

/-! ### The conditional distribution `X | U = u` and its collision quantities -/

/-- The **conditional distribution** of `X` given `U = u`: `x ↦ p(x, u) / p_U(u)`, where
`p_U(u) = Real.marginalSnd p u`. When `p_U(u) = 0` this is the zero function. -/
noncomputable def condDistribGivenSnd (p : ι × κ → ℝ) (u : κ) : ι → ℝ :=
  fun x ↦ p (x, u) / marginalSnd p u

theorem condDistribGivenSnd_apply (p : ι × κ → ℝ) (u : κ) (x : ι) :
    condDistribGivenSnd p u x = p (x, u) / marginalSnd p u := rfl

/-- The conditional distribution is nonnegative when `p` is. -/
theorem condDistribGivenSnd_nonneg {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (u : κ) (x : ι) :
    0 ≤ condDistribGivenSnd p u x :=
  div_nonneg (hp _) (marginalSnd_nonneg hp u)

/-- Where the marginal `p_U(u)` is nonzero, the conditional distribution is a genuine probability
distribution: `∑ₓ p(x | u) = 1`. -/
theorem sum_condDistribGivenSnd {p : ι × κ → ℝ} {u : κ} (hu : marginalSnd p u ≠ 0) :
    ∑ x, condDistribGivenSnd p u x = 1 := by
  simp only [condDistribGivenSnd]
  rw [← Finset.sum_div, ← marginalSnd_apply, div_self hu]

/-- The **conditional collision probability** `Pc(X | U = u) = ∑ₓ p(x | u)²`. -/
noncomputable def condCollisionProb (p : ι × κ → ℝ) (u : κ) : ℝ :=
  collisionProb (condDistribGivenSnd p u)

/-- The **conditional collision entropy** `Hc(X | U = u) = -log₂ (∑ₓ p(x | u)²)`, the collision
entropy of the conditional distribution of `X` given `U = u`. -/
noncomputable def condCollisionEntropy (p : ι × κ → ℝ) (u : κ) : ℝ :=
  collisionEntropy (condDistribGivenSnd p u)

theorem condCollisionEntropy_eq (p : ι × κ → ℝ) (u : κ) :
    condCollisionEntropy p u = -Real.logb 2 (condCollisionProb p u) := by
  rw [condCollisionEntropy, collisionEntropy_eq, condCollisionProb]

/-! ### Marginal domination of the conditional collision probability -/

/-- **Weighting identity**: `p_U(u)² · Pc(X | U = u) = ∑ₓ p(x, u)²`. Valid unconditionally on the
support (`p_U(u) ≠ 0`, where it is the definition cleared of denominators) and off it (`p_U(u) = 0`
forces every `p(x, u) = 0`, so both sides vanish). -/
theorem marginalSnd_sq_mul_condCollisionProb {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (u : κ) :
    marginalSnd p u ^ 2 * condCollisionProb p u = ∑ x, p (x, u) ^ 2 := by
  rcases eq_or_ne (marginalSnd p u) 0 with h | h
  · -- `p_U(u) = 0`: the whole fibre is zero.
    have hz : ∀ x, p (x, u) = 0 := by
      intro x
      have hsum0 : ∑ x, p (x, u) = 0 := by rw [← marginalSnd_apply]; exact h
      exact (Finset.sum_eq_zero_iff_of_nonneg fun x _ ↦ hp (x, u)).1 hsum0 x (Finset.mem_univ x)
    simp [h, hz]
  · -- `p_U(u) ≠ 0`: clear denominators.
    rw [condCollisionProb, collisionProb_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [condDistribGivenSnd_apply, div_pow, mul_comm, div_mul_cancel₀ _ (pow_ne_zero 2 h)]

variable [Fintype κ]

/-- **Marginal collision domination**: `∑ᵤ p_U(u)² · Pc(X | U = u) ≤ Pc(X)`. The left-hand side is
the joint collision probability `∑ₓ,ᵤ p(x, u)²`, and for each `x`,
`∑ᵤ p(x, u)² ≤ (∑ᵤ p(x, u))² = p_X(x)²` by `Finset.sum_sq_le_sq_sum_of_nonneg`. -/
theorem sum_marginalSnd_sq_mul_condCollisionProb_le {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    ∑ u, marginalSnd p u ^ 2 * condCollisionProb p u ≤ collisionProb (marginalFst p) := by
  calc ∑ u, marginalSnd p u ^ 2 * condCollisionProb p u
      = ∑ u, ∑ x, p (x, u) ^ 2 :=
        Finset.sum_congr rfl fun u _ ↦ marginalSnd_sq_mul_condCollisionProb hp u
    _ = ∑ x, ∑ u, p (x, u) ^ 2 := Finset.sum_comm
    _ ≤ ∑ x, (∑ u, p (x, u)) ^ 2 :=
        Finset.sum_le_sum fun x _ ↦ Finset.sum_sq_le_sq_sum_of_nonneg fun u _ ↦ hp (x, u)
    _ = collisionProb (marginalFst p) := by
        simp only [collisionProb_eq, marginalFst_apply]

/-! ### Chain rule: conditional entropy as an average of per-value entropies -/

/-- **Chain rule for the Shannon conditional entropy.** `H(X | U)` is the `p_U`-weighted average of
the Shannon entropies of the per-value conditional distributions `X | U = u`:

`H(X | U) = ∑ᵤ p_U(u) · H(X | U = u)`,

where `H(X | U = u) = Real.entropy (condDistribGivenSnd p u)`. This is the classical chain rule
`H(X, U) = H(U) + H(X | U)` read through `condEntropy p = H(X, U) − H(U)`; unlike the collision-
entropy tail bound below it involves no positivity of the conditioning, only `p ≥ 0`.

The zero-marginal values `p_U(u) = 0` are handled gracefully: the whole fibre `p(·, u)` then
vanishes (nonnegativity), and `negMulLog 0 = 0` makes both the fibre's contribution to `H(X, U)`
and the weighted term `0 · H(X | U = u)` vanish. On the support the per-value identity is
`negMulLog`'s scaling law `negMulLog (p_U(u) · p(x | u)) = p(x | u) · negMulLog (p_U(u))
+ p_U(u) · negMulLog (p(x | u))` summed over `x`, using `∑ₓ p(x | u) = 1`. -/
theorem condEntropy_eq_sum_marginalSnd_mul_entropy {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    condEntropy p = ∑ u, marginalSnd p u * entropy (condDistribGivenSnd p u) := by
  rw [condEntropy_eq, entropy_eq p, entropy_eq (marginalSnd p), Fintype.sum_prod_type,
    Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rcases eq_or_ne (marginalSnd p u) 0 with hu | hu
  · -- `p_U(u) = 0`: the whole fibre `p(·, u)` vanishes.
    have hz : ∀ x, p (x, u) = 0 := by
      intro x
      have hsum0 : ∑ x, p (x, u) = 0 := by rw [← marginalSnd_apply]; exact hu
      exact (Finset.sum_eq_zero_iff_of_nonneg fun x _ ↦ hp (x, u)).1 hsum0 x (Finset.mem_univ x)
    simp [hu, hz]
  · -- `p_U(u) ≠ 0`: reconstruct `p(x, u) = p_U(u) · p(x | u)` and apply `negMulLog_mul`.
    have hpe : ∀ x, p (x, u) = marginalSnd p u * condDistribGivenSnd p u x := by
      intro x
      rw [condDistribGivenSnd_apply, mul_comm, div_mul_cancel₀ _ hu]
    calc (∑ x, (p (x, u)).negMulLog) - (marginalSnd p u).negMulLog
        = (∑ x, (marginalSnd p u * condDistribGivenSnd p u x).negMulLog)
            - (marginalSnd p u).negMulLog := by simp_rw [← hpe]
      _ = (∑ x, (condDistribGivenSnd p u x * (marginalSnd p u).negMulLog
            + marginalSnd p u * (condDistribGivenSnd p u x).negMulLog))
            - (marginalSnd p u).negMulLog := by simp_rw [negMulLog_mul]
      _ = ((∑ x, condDistribGivenSnd p u x) * (marginalSnd p u).negMulLog
            + marginalSnd p u * ∑ x, (condDistribGivenSnd p u x).negMulLog)
            - (marginalSnd p u).negMulLog := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      _ = marginalSnd p u * entropy (condDistribGivenSnd p u) := by
          rw [sum_condDistribGivenSnd hu, one_mul, entropy_eq]; ring

/-- **Uniform conditional-collision bound ⟹ conditional-entropy lower bound.** If every value
`U = u` has conditional collision probability `Pc(X | U = u) ≤ c`, then the Shannon conditional
entropy is at least `log c⁻¹`:

`(∀ u, Pc(X | U = u) ≤ c) → log c⁻¹ ≤ H(X | U)`.

This is the ensemble-independent skeleton behind accessible-information bounds of the SIC / 2-design
kind: combine the chain rule `H(X | U) = ∑ᵤ p_U(u) · H(X | U = u)`
(`condEntropy_eq_sum_marginalSnd_mul_entropy`) with the per-value Shannon ≥ Rényi-2 bound
`log (Pc(X | U = u))⁻¹ ≤ H(X | U = u)` (`log_collisionProb_inv_le_entropy`), monotonicity of `log`,
and `∑ᵤ p_U(u) = 1`. No positivity of `c` is assumed: on the support `Pc(X | U = u) > 0`
(`collisionProb_pos`) already forces `c > 0`, and the off-support values are weighted out by
`p_U(u) = 0`. -/
theorem log_inv_le_condEntropy_of_condCollisionProb_le {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q)
    (hsum : ∑ u, marginalSnd p u = 1) {c : ℝ} (hle : ∀ u, condCollisionProb p u ≤ c) :
    Real.log c⁻¹ ≤ condEntropy p := by
  rw [condEntropy_eq_sum_marginalSnd_mul_entropy hp]
  calc Real.log c⁻¹ = (∑ u, marginalSnd p u) * Real.log c⁻¹ := by rw [hsum, one_mul]
    _ = ∑ u, marginalSnd p u * Real.log c⁻¹ := by rw [Finset.sum_mul]
    _ ≤ ∑ u, marginalSnd p u * entropy (condDistribGivenSnd p u) := by
        refine Finset.sum_le_sum fun u _ ↦ ?_
        rcases eq_or_ne (marginalSnd p u) 0 with hu | hu
        · simp [hu]
        · refine mul_le_mul_of_nonneg_left ?_ (marginalSnd_nonneg hp u)
          have hccpos : 0 < condCollisionProb p u := collisionProb_pos (sum_condDistribGivenSnd hu)
          have h1 := log_collisionProb_inv_le_entropy
            (condDistribGivenSnd_nonneg hp u) (sum_condDistribGivenSnd hu)
          rw [show collisionProb (condDistribGivenSnd p u) = condCollisionProb p u from rfl,
            Real.log_inv] at h1
          have h2 : Real.log (condCollisionProb p u) ≤ Real.log c := log_le_log hccpos (hle u)
          rw [Real.log_inv]
          linarith

/-! ### The privacy-amplification tail bound (Nielsen & Chuang, Theorem 12.17) -/

/-- **Nielsen & Chuang, Theorem 12.17** (privacy amplification / information reconciliation).
Let `X` and `U` be jointly distributed random variables with joint law `p : ι × κ → ℝ`
(`p ≥ 0`, `∑ p = 1`), and let `s > 0` be a security parameter. Then, with probability at least
`1 - 2⁻ˢ` (measured by the marginal `p_U`), the value `U = u` satisfies
`Hc(X | U = u) ≥ Hc(X) - 2·log₂|U| - 2s`, where `Hc(X) = Real.collisionEntropy (marginalFst p)`
and `|U| = Fintype.card κ`.

The event is recorded as a lower bound `1 - 2⁻ˢ ≤ ∑ᵤ p_U(u)` over the `u` at which the inequality
holds. The proof: the "bad" set carries collision-probability weight bounded via
`sum_marginalSnd_sq_mul_condCollisionProb_le` and `sq_sum_le_card_mul_sum_sq`, and collision
entropy converts to collision probability through the strict monotonicity of `log₂`.

Nielsen & Chuang state this for a security parameter `s > 0` (the regime where `1 - 2⁻ˢ ∈ (0, 1)`
is a genuine high-probability guarantee); the inequality in fact holds for every real `s`,
vacuously when `s ≤ 0` since then `1 - 2⁻ˢ ≤ 0 ≤ ∑ᵤ p_U(u)`. -/
theorem prob_condCollisionEntropy_ge (p : ι × κ → ℝ) (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1)
    (s : ℝ) :
    1 - (2 : ℝ) ^ (-s) ≤ ∑ u ∈ Finset.univ.filter
        (fun u ↦ collisionEntropy (marginalFst p) - 2 * Real.logb 2 (Fintype.card κ) - 2 * s
          ≤ condCollisionEntropy p u),
      marginalSnd p u := by
  classical
  -- Abbreviations and positivity facts.
  have hHcX : collisionEntropy (marginalFst p) = -Real.logb 2 (collisionProb (marginalFst p)) :=
    collisionEntropy_eq _
  have hPpos : 0 < collisionProb (marginalFst p) := by
    apply collisionProb_pos; rw [sum_marginalFst]; exact hsum
  set P := collisionProb (marginalFst p) with hPdef
  -- `κ` is nonempty, so `|U| ≥ 1`.
  have hcard0 : Fintype.card κ ≠ 0 := by
    intro h
    rw [Fintype.card_eq_zero_iff] at h
    have hz : (∑ q : ι × κ, p q) = 0 := Finset.sum_eq_zero fun q _ ↦ h.elim q.2
    rw [hsum] at hz; exact one_ne_zero hz
  have hcardR : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Nat.pos_of_ne_zero hcard0
  have hcard1 : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hcard0
  have hbase : (0 : ℝ) < 2 := by norm_num
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (2 * s) := Real.rpow_pos_of_pos hbase _
  set θ := P * (Fintype.card κ : ℝ) ^ 2 * (2 : ℝ) ^ (2 * s) with hθdef
  have hθpos : 0 < θ := by
    rw [hθdef]; exact mul_pos (mul_pos hPpos (pow_pos hcardR 2)) h2pos
  -- The threshold `θ` realises the entropy bound as `-log₂ θ`.
  have hlogθ : Real.logb 2 θ = Real.logb 2 P + 2 * Real.logb 2 (Fintype.card κ) + 2 * s := by
    rw [hθdef, Real.logb_mul (ne_of_gt (mul_pos hPpos (pow_pos hcardR 2))) (ne_of_gt h2pos),
      Real.logb_mul (ne_of_gt hPpos) (ne_of_gt (pow_pos hcardR 2)), Real.logb_pow,
      Real.logb_rpow hbase (by norm_num)]
    push_cast; ring
  have hbound : collisionEntropy (marginalFst p) - 2 * Real.logb 2 (Fintype.card κ) - 2 * s
      = -Real.logb 2 θ := by rw [hHcX, hlogθ]; ring
  -- `2⁻ˢ` squared kills the `2^{2s}` in `θ`.
  have htA : ((2 : ℝ) ^ (-s)) ^ 2 * (2 : ℝ) ^ (2 * s) = 1 := by
    rw [sq, ← Real.rpow_add hbase, ← Real.rpow_add hbase, show -s + -s + 2 * s = 0 by ring,
      Real.rpow_zero]
  have ht_nonneg : 0 ≤ (2 : ℝ) ^ (-s) := le_of_lt (Real.rpow_pos_of_pos hbase _)
  -- The "bad" set and its total `p_U`-mass.
  set bad := Finset.univ.filter (fun u ↦ ¬ (collisionEntropy (marginalFst p)
      - 2 * Real.logb 2 (Fintype.card κ) - 2 * s ≤ condCollisionEntropy p u)) with hbaddef
  set S := ∑ u ∈ bad, marginalSnd p u with hSdef
  set T := ∑ u ∈ bad, marginalSnd p u ^ 2 with hTdef
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun u _ ↦ marginalSnd_nonneg hp u
  -- Step 1+2: `θ · T ≤ Pc(X)`.
  have hθT : θ * T ≤ P := by
    calc θ * T = ∑ u ∈ bad, θ * marginalSnd p u ^ 2 := by rw [hTdef, Finset.mul_sum]
      _ ≤ ∑ u ∈ bad, marginalSnd p u ^ 2 * condCollisionProb p u := by
          refine Finset.sum_le_sum fun u hu ↦ ?_
          rw [hbaddef, Finset.mem_filter] at hu
          have hbadu : condCollisionEntropy p u
              < collisionEntropy (marginalFst p) - 2 * Real.logb 2 (Fintype.card κ) - 2 * s :=
            not_le.1 hu.2
          rcases eq_or_lt_of_le (marginalSnd_nonneg hp u) with hzero | hpos
          · rw [← hzero]; simp
          · -- `p_U(u) > 0`: the entropy bound forces `θ ≤ Pc(X | U = u)`.
            have hcpos : 0 < condCollisionProb p u :=
              collisionProb_pos (sum_condDistribGivenSnd hpos.ne')
            have hlt : Real.logb 2 θ < Real.logb 2 (condCollisionProb p u) := by
              have h1 : condCollisionEntropy p u < -Real.logb 2 θ := by rwa [hbound] at hbadu
              rw [condCollisionEntropy_eq] at h1
              linarith
            have hθc : θ ≤ condCollisionProb p u :=
              le_of_lt <| (Real.strictMonoOn_logb (by norm_num)).lt_iff_lt hθpos hcpos |>.1 hlt
            calc θ * marginalSnd p u ^ 2
                ≤ condCollisionProb p u * marginalSnd p u ^ 2 :=
                  mul_le_mul_of_nonneg_right hθc (sq_nonneg _)
              _ = marginalSnd p u ^ 2 * condCollisionProb p u := mul_comm _ _
      _ ≤ ∑ u, marginalSnd p u ^ 2 * condCollisionProb p u :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun u _ _ ↦ mul_nonneg (sq_nonneg _) (collisionProb_nonneg _))
      _ ≤ P := sum_marginalSnd_sq_mul_condCollisionProb_le hp
  -- Step 3: Cauchy–Schwarz `S² ≤ |bad| · T`, and `|bad| ≤ |U|`.
  have hCS : S ^ 2 ≤ (bad.card : ℝ) * T := by rw [hSdef, hTdef]; exact sq_sum_le_card_mul_sum_sq
  -- Step 4: `S² ≤ (2⁻ˢ)²`.
  have hkey : θ * (S ^ 2) ≤ θ * ((2 : ℝ) ^ (-s)) ^ 2 := by
    have hstep : θ * ((bad.card : ℝ) * T) ≤ θ * ((2 : ℝ) ^ (-s)) ^ 2 := by
      have e2 : θ * ((2 : ℝ) ^ (-s)) ^ 2 = P * (Fintype.card κ : ℝ) ^ 2 := by
        rw [hθdef]
        calc P * (Fintype.card κ : ℝ) ^ 2 * (2 : ℝ) ^ (2 * s) * ((2 : ℝ) ^ (-s)) ^ 2
            = P * (Fintype.card κ : ℝ) ^ 2 * (((2 : ℝ) ^ (-s)) ^ 2 * (2 : ℝ) ^ (2 * s)) := by ring
          _ = P * (Fintype.card κ : ℝ) ^ 2 := by rw [htA, mul_one]
      rw [e2]
      calc θ * ((bad.card : ℝ) * T) = (bad.card : ℝ) * (θ * T) := by ring
        _ ≤ (bad.card : ℝ) * P :=
            mul_le_mul_of_nonneg_left hθT (by positivity)
        _ ≤ (Fintype.card κ : ℝ) * P := by
            refine mul_le_mul_of_nonneg_right ?_ hPpos.le
            calc (bad.card : ℝ) ≤ (Finset.univ.card : ℝ) := by
                  exact_mod_cast Finset.card_filter_le _ _
              _ = (Fintype.card κ : ℝ) := by rw [Finset.card_univ]
        _ = P * (Fintype.card κ : ℝ) := mul_comm _ _
        _ ≤ P * (Fintype.card κ : ℝ) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ hPpos.le
            nlinarith [hcard1, hcardR]
    exact (mul_le_mul_of_nonneg_left hCS hθpos.le).trans hstep
  have hSsq : S ^ 2 ≤ ((2 : ℝ) ^ (-s)) ^ 2 := le_of_mul_le_mul_left hkey hθpos
  have hS_le : S ≤ (2 : ℝ) ^ (-s) := by
    have := Real.sqrt_le_sqrt hSsq
    rwa [Real.sqrt_sq hS_nonneg, Real.sqrt_sq ht_nonneg] at this
  -- Step 5: convert the bad-set mass bound into the good-set probability bound.
  have hsplit : (∑ u ∈ Finset.univ.filter (fun u ↦ collisionEntropy (marginalFst p)
        - 2 * Real.logb 2 (Fintype.card κ) - 2 * s ≤ condCollisionEntropy p u), marginalSnd p u)
      + S = 1 := by
    rw [hSdef, hbaddef, Finset.sum_filter_add_sum_filter_not Finset.univ _ (marginalSnd p),
      sum_marginalSnd, hsum]
  linarith

end Real
