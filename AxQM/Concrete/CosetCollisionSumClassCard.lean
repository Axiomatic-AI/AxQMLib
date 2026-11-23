/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SubgroupMaximalSum
import AxQM.Concrete.SubgroupMaximalRatioSum
import AxQM.Concrete.SubgroupNilpotentMaximalNormal

/-!
# Concrete: the affinity collision sum at N&C's sample count, conditional on one class count

*(Supporting `AxQM/NC/Ch5/Problem5_5.lean`, N&C Problem 5.5 — the non-Abelian hidden
subgroup problem.)* This file performs the **final threading** of the Ettinger–Høyer–Knill
piece (ii) counting tail: it feeds the assembled maximal-subgroup ratio bound
`sum_maximal_ratio_pow_le_of_classCard_sq` (`SubgroupMaximalRatioSum.lean`) into the collision-sum
reduction `sum_cosetAffinity_pow_collision_maximal_le_of_sq` (`SubgroupMaximalSum.lean`), producing
a bound on the whole affinity collision sum `∑_{K'≠K} A(K,K')^{2s}` at N&C's linear sample exponent
(`2·|G|² ≤ 2^s`, i.e. `s = 2 log₂|G| + 1`, `m = 2s = 4 log₂|G| + 2`) that is **unconditional except
for the single group-theoretic count** of the `K`-conjugacy classes of non-normal maximal subgroups.

## What is proved

The collision reduction pins the collision sum on the maximal-subgroup sum:
`∑_{K'≠K} A(K,K')^{2s} ≤ 1/|G| + 4·∑_{M⋖K}(|M|/|K|)^s`, valid under the *mild generation
hypothesis* `∀ J, ∑_{M⋖J}(|M|/|J|)^s ≤ 1/2`. The bound `sum_maximal_ratio_pow_le_of_classCard_sq`
supplies BOTH: applied at each `J` it gives `∑_{M⋖J}(|M|/|J|)^s ≤ 3/(2|G|) ≤ 1/2` (for `|G| ≥ 3`),
discharging the mild hypothesis, and at `K` itself it bounds the residual maximal sum by `3/(2|G|)`.
Composing,

`∑_{K'≠K} A(K,K')^{2s} ≤ 1/|G| + 4·(3/(2|G|)) = 7/|G|`

— an **`O(1/|G|)` collision bound at N&C's linear sample count**
(`sum_cosetAffinity_pow_collision_classCard_le_of_sq`), conditional ONLY on the
Liebeck–Pyber–Shalev-strength count `∀ J, 3·#{J-conj classes of non-normal maximals} ≤ |J|²`. This
is the sharpest form of the EHK piece (ii) reduction: the *entire* remaining counting tail — the
output of the ~ten-file maximal-subgroup development — is now carried by that one `∀`-quantified
hypothesis, and the physics-layer form `cosetDensityState_pi_sum_affinity_collision_classCard_le`
(statement of Problem 5.5) lifts this to the `State`-level pairwise-affinity sum the
identification clause consumes.

The constant `7/|G|` is `O(1/|G|)` but not the sharp `1/|G|`; reaching N&C's exact target
probability `1 − 1/|G|` at the exact constant `m = 4 log₂|G| + 2` needs a further sharpening of the
collision reduction's factors together with a per-state (not merely summed) discrimination bound.
The linear *order* in `log|G|` — the substantive Ettinger–Høyer–Knill content — is exactly what this
bound establishes.
-/

namespace AxQM.Concrete

open Finset

variable {G : Type*} [Group G]

open Classical in
/-- **The affinity collision sum is `≤ 7/|G|` at N&C's sample count, conditional only on the
non-normal maximal class count** (Ettinger–Høyer–Knill piece ii, final threading). For a finite
group `G`, a subgroup `K ≤ G`, and N&C's sample exponent `2·|G|² ≤ 2^s` (i.e. `s = 2 log₂|G| + 1`,
`m = 2s = 4 log₂|G| + 2`), *given* the single Liebeck–Pyber–Shalev-strength count that every
subgroup `J ≤ G` has

`3 · #{J-conjugacy classes of non-normal maximal subgroups of J} ≤ |J|²`,

the whole affinity collision sum over the candidate hidden subgroups obeys

`∑_{K' ≠ K} A(K, K')^{2s} = ∑_{K' ≠ K} (|K∩K'|/√(|K||K'|))^{2s} ≤ 7/|G|`.

This is the **final threading** of the Ettinger–Høyer–Knill piece (ii) counting tail. The collision
reduction `sum_cosetAffinity_pow_collision_maximal_le_of_sq` bounds the sum by
`1/|G| + 4·∑_{M⋖K}(|M|/|K|)^s` under the *mild generation hypothesis*
`∀ J, ∑_{M⋖J}(|M|/|J|)^s ≤ 1/2`, and the maximal-subgroup bound
`sum_maximal_ratio_pow_le_of_classCard_sq` supplies both parts: applied at each `J` it gives
`∑_{M⋖J}(|M|/|J|)^s ≤ 3/(2|G|)`, which is `≤ 1/2` once `|G| ≥ 3` (`hG`), discharging the mild
hypothesis, and at `K` it bounds the residual maximal sum by `3/(2|G|)`;
`1/|G| + 4·(3/(2|G|)) = 7/|G|`.

So the *entire* remaining counting tail of the EHK identification bound is now carried by the single
`∀`-quantified count `hcount` — the `K`-conjugacy-class count of non-normal maximal subgroups, the
one residual with no group quotient to count through. The constant `7/|G|` is `O(1/|G|)`, the linear
sample count being the substantive content; the sharp `1/|G|` needs a further sharpening of the
collision factors (see the module docstring). -/
theorem sum_cosetAffinity_pow_collision_classCard_le_of_sq [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) {s : ℕ} (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hcount : ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2) :
    ∑ K' ∈ Finset.univ.erase K, cosetAffinity K K' ^ (2 * s) ≤ 7 / (Nat.card G : ℝ) := by
  have hG3 : (3 : ℝ) ≤ Nat.card G := by exact_mod_cast hG
  have hGpos : (0 : ℝ) < Nat.card G := by linarith
  have hG0 : (Nat.card G : ℝ) ≠ 0 := hGpos.ne'
  -- The mild generation hypothesis `∀ J, ∑_{M⋖J}(|M|/|J|)^s ≤ 1/2`, from the bound at each `J`
  -- (the bound `3/(2|G|)` is `≤ 1/2` because `|G| ≥ 3`).
  have hmild : ∀ J : Subgroup G,
      ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ J),
        ((Nat.card ↥M : ℝ) / Nat.card ↥J) ^ s ≤ 1 / 2 := by
    intro J
    refine (sum_maximal_ratio_pow_le_of_classCard_sq J hs (hcount J)).trans ?_
    rw [div_le_iff₀ (by linarith)]
    linarith
  -- The collision reduction, and the residual maximal bound at `K`.
  refine (sum_cosetAffinity_pow_collision_maximal_le_of_sq K hs hmild).trans ?_
  have hmax := sum_maximal_ratio_pow_le_of_classCard_sq K hs (hcount K)
  rw [show (7 : ℝ) / (Nat.card G : ℝ)
      = (Nat.card G : ℝ)⁻¹ + 4 * (3 / (2 * (Nat.card G : ℝ))) by field_simp; ring]
  linarith

open Classical in
/-- **The affinity collision sum is `≤ 1/(2|G|)` at a linear sample count** — the sharp `O(1/|G|)`
constant, at a modestly larger (still linear) exponent than N&C's exact `2s`. For a finite group
`G`, a subgroup `K ≤ G`, and the base sample exponent `2·|G|² ≤ 2^s`, *given* the single
Liebeck–Pyber–Shalev-strength class count that every subgroup `J ≤ G` has
`3 · #{J-conjugacy classes of non-normal maximal subgroups of J} ≤ |J|²`, the affinity collision sum
at the exponent `2·(s+4)` obeys

`∑_{K' ≠ K} A(K, K')^{2(s+4)} ≤ 1/(2|G|)`.

This sharpens `sum_cosetAffinity_pow_collision_classCard_le_of_sq` (`≤ 7/|G|` at exponent `2s`) to
the **sharp `1/(2|G|)`** by an *exponent-raising* argument: every *near* term already carries the
universal per-copy separation `A(K, K') ≤ 1/√2` (`cosetAffinity_le_of_ne`, `K' ≠ K`), so raising the
exponent from `2s` to `2s + 8` multiplies each term — hence the whole sum — by
`(1/√2)^8 = 1/16`; `(7/|G|)·(1/16) = 7/(16|G|) ≤ 1/(2|G|)`. The cost is `+8` in the exponent
(`+4` in the sample-count half-exponent), i.e. `m = 2(s+4) = 4 log₂|G| + 10` in place of N&C's exact
`m = 2s = 4 log₂|G| + 2` — still a **linear** `O(log|G|)` count. The `1/(2|G|)` bound is exactly
what drives the pretty-good identification deficit `2·∑ A` to N&C's exact `1/|G|`, so the
identification success probability reaches `≥ 1 − 1/|G|` (see
`AxQM.cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_commGroup`). -/
theorem sum_cosetAffinity_pow_collision_classCard_le_inv_of_sq [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) {s : ℕ} (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hcount : ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2) :
    ∑ K' ∈ Finset.univ.erase K, cosetAffinity K K' ^ (2 * (s + 4))
      ≤ 1 / (2 * (Nat.card G : ℝ)) := by
  have hG3 : (3 : ℝ) ≤ Nat.card G := by exact_mod_cast hG
  have hGpos : (0 : ℝ) < Nat.card G := by linarith
  -- `(1/√2)^8 = 1/16`: the factor a `+8` exponent bump buys, since `(1/√2)^2 = 1/2`.
  have hhalf8 : ((1 : ℝ) / Real.sqrt 2) ^ 8 = 1 / 16 := by
    have h2 : ((1 : ℝ) / Real.sqrt 2) ^ 2 = 1 / 2 := by
      rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc ((1 : ℝ) / Real.sqrt 2) ^ 8 = (((1 : ℝ) / Real.sqrt 2) ^ 2) ^ 4 := by rw [← pow_mul]
      _ = (1 / 2) ^ 4 := by rw [h2]
      _ = 1 / 16 := by norm_num
  -- Per-term: raising the exponent from `2s` to `2(s+4) = 2s+8` costs a factor `1/16`, because each
  -- coset affinity `A(K,K') ≤ 1/√2` (distinct subgroups).
  have hterm : ∀ K' ∈ Finset.univ.erase K,
      cosetAffinity K K' ^ (2 * (s + 4)) ≤ cosetAffinity K K' ^ (2 * s) * (1 / 16) := by
    intro K' hK'
    have hne : K ≠ K' := (Finset.ne_of_mem_erase hK').symm
    have hle : cosetAffinity K K' ≤ 1 / Real.sqrt 2 := cosetAffinity_le_of_ne K K' hne
    have hnn : 0 ≤ cosetAffinity K K' := cosetAffinity_nonneg K K'
    have h8 : cosetAffinity K K' ^ 8 ≤ 1 / 16 := hhalf8 ▸ pow_le_pow_left₀ hnn hle 8
    calc cosetAffinity K K' ^ (2 * (s + 4))
        = cosetAffinity K K' ^ (2 * s) * cosetAffinity K K' ^ 8 := by
          rw [show 2 * (s + 4) = 2 * s + 8 from by ring, pow_add]
      _ ≤ cosetAffinity K K' ^ (2 * s) * (1 / 16) :=
          mul_le_mul_of_nonneg_left h8 (pow_nonneg hnn _)
  calc ∑ K' ∈ Finset.univ.erase K, cosetAffinity K K' ^ (2 * (s + 4))
      ≤ ∑ K' ∈ Finset.univ.erase K, cosetAffinity K K' ^ (2 * s) * (1 / 16) :=
        Finset.sum_le_sum hterm
    _ = (∑ K' ∈ Finset.univ.erase K, cosetAffinity K K' ^ (2 * s)) * (1 / 16) := by
        rw [← Finset.sum_mul]
    _ ≤ (7 / (Nat.card G : ℝ)) * (1 / 16) := by
        gcongr
        exact sum_cosetAffinity_pow_collision_classCard_le_of_sq K hG hs hcount
    _ ≤ 1 / (2 * (Nat.card G : ℝ)) := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hGpos]

open Classical in
/-- **The Problem 5.5 non-normal-maximal class-count hypothesis holds vacuously for a nilpotent
group.** For a **nilpotent** finite group `G`, every subgroup `J ≤ G` satisfies the
Liebeck–Pyber–Shalev-strength count that gates the piece-(ii) collision tail,

`3 · #{J-conjugacy classes of non-normal maximal subgroups of J} ≤ |J|²`,

**vacuously**: a nilpotent group — and every subgroup of one — has *no* non-normal maximal subgroups
(`normal_subgroupOf_of_covBy_of_isNilpotent`: under the normalizer condition every maximal subgroup
is normal), so the filtered set is empty and the count is `0 ≤ |J|²`. This is the single shared
discharge of the class-count hypothesis `hcount` for every nilpotent-`G` identification headline
(`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_nilpotent` and its variants), replacing
the previously-inlined `Finset.filter_eq_empty_iff` argument at each site. -/
theorem classCard_hyp_of_isNilpotent [Group.IsNilpotent G] [Fintype (Subgroup G)] :
    ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2 := by
  intro J
  have hempty : (Finset.univ.filter
        (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro M - ⟨hcov, hnn⟩
    exact hnn (normal_subgroupOf_of_covBy_of_isNilpotent hcov)
  rw [hempty, Finset.image_empty, Finset.card_empty, Nat.mul_zero]
  exact Nat.zero_le _

end AxQM.Concrete
