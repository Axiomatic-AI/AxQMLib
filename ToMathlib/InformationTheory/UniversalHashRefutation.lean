/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.UniversalHashEntropy

/-!
# Refutation of the literal constant in Nielsen & Chuang's Theorem 12.16

Nielsen & Chuang's privacy-amplification theorem (§12.6, Theorem 12.16) states the entropy chain
`H(G(X)|G) ≥ Hc(G(X)|G) ≥ m − 2^{m−Hc(X)}` for the output `G(X)` of a `2`-universal hash family to
`{0,1}^m`, with `G` uniform. The first inequality and the (corrected) form of the second are
established in `ToMathlib/InformationTheory/UniversalHashEntropy.lean`; the honest second bound is
`Hc(G(X)|G) ≥ m − log₂(1 + 2^{m−Hc(X)})`. This file proves that **Nielsen & Chuang's literal second
inequality, with its constant `2^{m−Hc(X)}`, is false**.

The obstruction is the elementary gap `log₂(1 + z) > z` for `0 < z < 1` (equivalently `2^z < 1 + z`,
the strict convexity of `2^·` below the chord): the textbook's linear constant `2^{m−Hc(X)}`
over-states the true `log₂(1 + 2^{m−Hc(X)})`, dropping the `1/ln 2` in `log₂(1+z) ≤ z/ln 2`.
Writing `z = 2^{m−Hc(X)} = |β|·Pc(X)`, whenever `0 < z < 1` (i.e. `m < Hc(X)`, the regime of
interest for key extraction) there is a universal family whose conditional collision entropy falls
strictly below `m − 2^{m−Hc(X)}`.

## The counterexample

The **all-functions family** `h = (id : (α → β) → α → β)` — index set `γ = α → β`, so a uniform `G`
is a uniformly random function — is exactly `2`-universal (`id_isUniversalFamily`): for distinct
`x ≠ x'`, exactly `|β|^{|α|−1}` of the `|β|^{|α|}` functions satisfy `g x = g x'`
(`card_filter_apply_eq_pow`), a collision fraction of exactly `1/|β|`. Its average collision
probability has the closed form `avgCollisionProb id p = 1/|β| + (1 − 1/|β|)·Pc(X)`
(`avgCollisionProb_id`), so the leftover-hash bound `≤ 1/|β| + Pc(X)` is essentially tight.

Taking `α = Fin 16`, `β = Fin 8` (so `m = log₂ 8 = 3`) and `X` uniform (`Pc(X) = 1/16`, `Hc(X) = 4`,
`z = 8·(1/16) = 1/2 ∈ (0,1)`), the average collision probability is `1/8 + (7/8)·(1/16) = 23/128`,
hence
`Hc(G(X)|G) = −log₂(23/128) = 2.4757… < 5/2 = 3 − 1/2 = m − 2^{m−Hc(X)}`
(`avgCollisionEntropy_id_uniform_lt_literalBound`). The strict inequality reduces to `23/128 >
2^{−5/2}`, i.e. `529 > 512` after squaring. The headline `exists_lt_universalHash_literalBound`
packages this as: there is a genuinely `2`-universal family and input distribution violating Nielsen
& Chuang's literal bound.

## Main results

* `card_filter_apply_eq_pow`: `#{g : α → β | g x = g x'} = |β|^{|α|−1}` for `x ≠ x'` — the count
  driving universality and the closed form.
* `id_isUniversalFamily`: the all-functions family is `2`-universal.
* `avgCollisionProb_id`: `avgCollisionProb id p = 1/|β| + (1 − 1/|β|)·collisionProb p`.
* `avgCollisionEntropy_id_uniform_lt_literalBound`: the concrete violation on `Fin 16 → Fin 8`.
* `exists_lt_universalHash_literalBound`: **the refutation** — a `2`-universal family and input with
  `Hc(G(X)|G) < log₂|β| − |β|·Pc(X)`, so Nielsen & Chuang's literal second inequality is false.
-/

@[expose] public section

namespace Real

variable {α β : Type*}

/-- Restricting a function `g : α → β` that agrees at two distinct points `x ≠ x'` (`g x = g x'`) to
the complement of `x'` is a bijection onto *all* functions `{a // a ≠ x'} → β`: the value at `x'` is
forced to equal the value at `x` — which lies in the complement, since `x ≠ x'` — so it carries no
free information. Used to count the functions agreeing at `x, x'`. -/
private def funAgreePairEquiv [DecidableEq α] {x x' : α} (hxx : x ≠ x') :
    {g : α → β // g x = g x'} ≃ ({a : α // a ≠ x'} → β) where
  toFun g a := g.1 a.1
  invFun r := ⟨fun a => if h : a = x' then r ⟨x, hxx⟩ else r ⟨a, h⟩, by
    dsimp only
    rw [dite_eq_right hxx, dite_eq_left rfl]⟩
  left_inv g := by
    apply Subtype.ext
    funext a
    dsimp only
    by_cases h : a = x'
    · rw [dite_eq_left h, h]; exact g.2
    · rw [dite_eq_right h]
  right_inv r := by
    funext a
    dsimp only
    rw [dite_eq_right a.2]

/-- **The number of functions `α → β` that agree at two distinct points** `x ≠ x'` is
`|β|^{|α|−1}`. The value at `x'` is determined (it must equal the value at `x`), leaving the
`|α|−1` remaining coordinates free; formally, restriction to the complement of `x'` is a bijection
(`funAgreePairEquiv`) onto `{a // a ≠ x'} → β`, of cardinality `|β|^{|α|−1}`. -/
theorem card_filter_apply_eq_pow [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {x x' : α} (hxx : x ≠ x') :
    (Finset.univ.filter (fun g : α → β => g x = g x')).card
      = Fintype.card β ^ (Fintype.card α - 1) := by
  have hcompl : Fintype.card {a : α // a ≠ x'} = Fintype.card α - 1 := by
    simp [Fintype.card_subtype_compl]
  rw [← Fintype.card_subtype, Fintype.card_congr (funAgreePairEquiv hxx), Fintype.card_fun, hcompl]

/-- **The all-functions family `id : (α → β) → α → β` is `2`-universal** (for `β` nonempty): with
`G` a uniformly random function `α → β`, distinct inputs `x ≠ x'` collide with probability exactly
`1/|β|`, meeting the universality bound with equality. Proof: `card_filter_apply_eq_pow` gives
`|β|^{|α|−1}` colliding functions out of `|β|^{|α|}` (`Fintype.card_fun`), a ratio of `1/|β|`. -/
theorem id_isUniversalFamily [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Nonempty β] :
    IsUniversalFamily (id : (α → β) → α → β) := by
  intro x x' hxx
  have hn : 1 ≤ Fintype.card α := Fintype.card_pos_iff.mpr ⟨x⟩
  have hfil : (Finset.univ.filter (fun g : (α → β) => id g x = id g x')).card
      = Fintype.card β ^ (Fintype.card α - 1) := card_filter_apply_eq_pow hxx
  rw [hfil, Fintype.card_fun]
  -- `|β|^{|α|−1} / |β|^{|α|} = 1/|β|`, so the collision fraction equals `1/|β|`.
  push_cast
  have hCpos : (0 : ℝ) < (Fintype.card β : ℝ) ^ (Fintype.card α - 1) := by positivity
  have hpow : (Fintype.card β : ℝ) ^ Fintype.card α
      = (Fintype.card β : ℝ) ^ (Fintype.card α - 1) * (Fintype.card β : ℝ) := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  apply le_of_eq
  rw [hpow, ← div_div, div_self hCpos.ne', one_div]

/-- **Closed form for the average collision probability of the all-functions family.** For the
family `id : (α → β) → α → β` and any input probability distribution `p`,
`avgCollisionProb id p = 1/|β| + (1 − 1/|β|)·Pc(X)`, where `Pc(X) = collisionProb p`.

In particular the leftover-hash bound `avgCollisionProb ≤ 1/|β| + Pc(X)` is essentially tight for
this family: the slack is exactly `Pc(X)/|β|`. Proof: expand each hashed collision probability over
ordered pairs (`collisionProb_law_eq_sum_pairs`) and average the indicator `[g x' = g x]` over `g`
to the collision frequency `#{g | g x' = g x}/|γ|`, which is `1` on the diagonal `x = x'` and
`|β|^{|α|−1}/|β|^{|α|} = 1/|β|` off it (`card_filter_apply_eq_pow`, `Fintype.card_fun`). -/
theorem avgCollisionProb_id [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Nonempty α] [Nonempty β] {p : α → ℝ} (hsum : ∑ x, p x = 1) :
    avgCollisionProb (id : (α → β) → α → β) p
      = (Fintype.card β : ℝ)⁻¹ + (1 - (Fintype.card β : ℝ)⁻¹) * collisionProb p := by
  have hβR : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty β›
  have hn : 1 ≤ Fintype.card α := Fintype.card_pos_iff.mpr ‹Nonempty α›
  set C : ℝ := (Fintype.card β : ℝ) ^ (Fintype.card α - 1) with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hGR : (Fintype.card (α → β) : ℝ) = C * Fintype.card β := by
    rw [Fintype.card_fun]; push_cast; rw [hC, ← pow_succ, Nat.sub_add_cancel hn]
  -- Numerator: `∑_g Pc(law p (id g)) = C + (|γ| − C)·Pc`.
  have hnum : (∑ g : α → β, collisionProb (law p (id g)))
      = C + ((Fintype.card (α → β) : ℝ) - C) * collisionProb p := by
    -- Expand each push-forward collision probability over ordered pairs, then swap `g` inward.
    have reorder : (∑ g : α → β, collisionProb (law p (id g)))
        = ∑ x, ∑ x', ∑ g : α → β, if g x' = g x then p x * p x' else 0 := by
      simp_rw [id_eq, collisionProb_law_eq_sum_pairs]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    rw [reorder]
    -- Average the indicator over `g` to the collision count.
    have hcount : ∀ x x' : α, (∑ g : α → β, if g x' = g x then p x * p x' else 0)
        = (if x' = x then (Fintype.card (α → β) : ℝ) else C) * (p x * p x') := by
      intro x x'
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 1
      by_cases hxx : x' = x
      · subst hxx
        rw [ite_eq_left rfl, Finset.filter_true_of_mem (fun g _ => rfl), Finset.card_univ]
      · rw [ite_eq_right hxx, hC]
        exact_mod_cast card_filter_apply_eq_pow hxx
    simp_rw [hcount]
    -- Split each coefficient into the constant `C` part and the diagonal excess `|γ| − C`.
    have hsplit : ∀ x x' : α,
        (if x' = x then (Fintype.card (α → β) : ℝ) else C) * (p x * p x')
          = C * (p x * p x')
            + (if x' = x then ((Fintype.card (α → β) : ℝ) - C) else 0) * (p x * p x') := by
      intro x x'
      by_cases hxx : x' = x
      · rw [ite_eq_left hxx, ite_eq_left hxx]; ring
      · rw [ite_eq_right hxx, ite_eq_right hxx, zero_mul, add_zero]
    simp_rw [hsplit, Finset.sum_add_distrib]
    -- The constant part sums to `C`; the diagonal excess to `(|γ| − C)·Pc`.
    have hAsum : (∑ x, ∑ x', C * (p x * p x')) = C := by
      simp only [← Finset.mul_sum, hsum, mul_one]
    have hBsum : (∑ x, ∑ x',
        (if x' = x then ((Fintype.card (α → β) : ℝ) - C) else 0) * (p x * p x'))
          = ((Fintype.card (α → β) : ℝ) - C) * collisionProb p := by
      rw [collisionProb_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp_rw [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ x
        (fun x' => ((Fintype.card (α → β) : ℝ) - C) * (p x * p x')), ite_eq_left (Finset.mem_univ
            x)]
      ring
    rw [hAsum, hBsum]
  rw [avgCollisionProb_eq, hnum, hGR]
  field_simp

/-- **The concrete counterexample.** On `α = Fin 16`, `β = Fin 8` with `X` uniform, the
all-functions family's conditional collision entropy is `Hc(G(X)|G) = −log₂(23/128) = 2.475… < 5/2`,
strictly below N&C's literal bound `m − 2^{m−Hc(X)} = log₂ 8 − 8·(1/16) = 3 − 1/2 = 5/2`.

Here `m = log₂ 8 = 3` output bits, `Pc(X) = 1/16` so `Hc(X) = 4`, and the average collision
probability is `avgCollisionProb id X = 1/8 + (7/8)·(1/16) = 23/128` (`avgCollisionProb_id`,
`collisionProb_uniform`). The strict inequality reduces to `log₂(23/16) > 1/2`, i.e. `23/16 > √2`,
i.e. `529 > 512`. -/
theorem avgCollisionEntropy_id_uniform_lt_literalBound :
    avgCollisionEntropy (id : (Fin 16 → Fin 8) → Fin 16 → Fin 8)
        (fun _ => (Fintype.card (Fin 16) : ℝ)⁻¹)
      < Real.logb 2 (Fintype.card (Fin 8))
        - Fintype.card (Fin 8)
          * collisionProb (fun _ : Fin 16 => (Fintype.card (Fin 16) : ℝ)⁻¹) := by
  have hcard16 : Fintype.card (Fin 16) = 16 := Fintype.card_fin 16
  have hcard8 : Fintype.card (Fin 8) = 8 := Fintype.card_fin 8
  have hsum : ∑ _x : Fin 16, (Fintype.card (Fin 16) : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, hcard16]; norm_num
  have hPc : collisionProb (fun _ : Fin 16 => (Fintype.card (Fin 16) : ℝ)⁻¹)
      = (Fintype.card (Fin 16) : ℝ)⁻¹ := collisionProb_uniform
  have hAvg : avgCollisionProb (id : (Fin 16 → Fin 8) → Fin 16 → Fin 8)
      (fun _ => (Fintype.card (Fin 16) : ℝ)⁻¹) = 23 / 128 := by
    rw [avgCollisionProb_id hsum, hPc, hcard8, hcard16]; norm_num
  rw [avgCollisionEntropy_eq, hAvg, hPc, hcard8, hcard16]
  -- Goal: `−log₂(23/128) < log₂ 8 − 8·(1/16)`.
  have h816 : (8 : ℝ) * (16 : ℝ)⁻¹ = 1 / 2 := by norm_num
  -- `log₂ 8 + log₂(23/128) = log₂(23/16)`, so it suffices that `log₂(23/16) > 1/2`.
  have hmul : Real.logb 2 8 + Real.logb 2 (23 / 128) = Real.logb 2 (23 / 16) := by
    rw [← Real.logb_mul (by norm_num) (by norm_num),
      show (8 : ℝ) * (23 / 128) = 23 / 16 by norm_num]
  have hhalf : Real.logb 2 (2 ^ (1 / 2 : ℝ)) = 1 / 2 := by
    rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by positivity)]
  have hkey : (1 : ℝ) / 2 < Real.logb 2 (23 / 16) := by
    rw [← hhalf]
    apply Real.logb_lt_logb (by norm_num) (by positivity)
    rw [← Real.sqrt_eq_rpow, Real.sqrt_lt' (by norm_num)]
    norm_num
  push_cast
  linarith [hmul, hkey, h816]

/-- **Refutation of the literal constant in Nielsen & Chuang's Theorem 12.16.** There is a genuinely
`2`-universal hash family `h` and input distribution `p` whose conditional collision entropy falls
strictly below the textbook's literal second bound `m − 2^{m−Hc(X)}` — written here
`log₂|β| − |β|·Pc(X)`, using `2^{m−Hc(X)} = |β|·Pc(X)`. Hence N&C's *second* inequality,
with the constant `2^{m−Hc(X)}`, is **false** as stated; the correct lower bound is the `log₂(1+·)`
form `Real.avgCollisionEntropy_ge`.

Witnessed by the all-functions family on `Fin 16 → Fin 8` with `X` uniform
(`id_isUniversalFamily`, `avgCollisionEntropy_id_uniform_lt_literalBound`). -/
theorem exists_lt_universalHash_literalBound :
    ∃ (h : (Fin 16 → Fin 8) → Fin 16 → Fin 8) (p : Fin 16 → ℝ),
      IsUniversalFamily h ∧ (∀ x, 0 ≤ p x) ∧ (∑ x, p x = 1) ∧
        avgCollisionEntropy h p
          < Real.logb 2 (Fintype.card (Fin 8)) - Fintype.card (Fin 8) * collisionProb p :=
  ⟨id, fun _ => (Fintype.card (Fin 16) : ℝ)⁻¹, id_isUniversalFamily, fun _ => by positivity,
    by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num,
    avgCollisionEntropy_id_uniform_lt_literalBound⟩

end Real
