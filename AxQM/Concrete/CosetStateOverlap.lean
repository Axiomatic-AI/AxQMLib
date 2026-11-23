/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CosetState

/-!
# Concrete: the Hilbert–Schmidt overlap of coset density matrices

This file computes the **overlap** `tr(σ_K σ_{K'})` of the coset density matrices of two subgroups
`K, K' ≤ G` of a finite group `G`, where `σ_K = cosetDensity K` (entries `σ_K i j = |G|⁻¹ · [iK =
jK]`, see `AxQM.Concrete.CosetState`). The result is the clean, computable quantity

`tr(σ_K σ_{K'}) = |K ∩ K'| / |G|`   (`cosetDensity_trace_mul`),

whose diagonal specialisation `K = K'` is the **purity**

`tr(σ_K²) = |K| / |G|`   (`cosetDensity_trace_mul_self`).

Comparing the two gives the **near-orthogonality bound** for *distinct* subgroups `K ≠ K'`:

`2 · tr(σ_K σ_{K'})² ≤ tr(σ_K²) · tr(σ_{K'}²)`   (`cosetDensity_trace_mul_sq_le`),

i.e. the normalized overlap `tr(σ_K σ_{K'}) / √(tr σ_K² · tr σ_{K'}²) = |K∩K'|/√(|K||K'|) ≤ 1/√2`.
Its purely group-theoretic core is `2·|K∩K'|² ≤ |K|·|K'|` (`two_mul_card_inf_sq_le`), from the
pigeonhole fact that a proper subgroup has at most half its overgroup's order
(`two_mul_card_le_of_lt`).

These are the quantitative heart of Nielsen & Chuang, Problem 5.5 (the non-Abelian hidden subgroup
problem): they say precisely *how nearly orthogonal* the single-copy reduced states `σ_K` are for
different candidate hidden subgroups. Since `σ_K = (|K|/|G|) Π_K` is `|K|/|G|` times the
rank-`|G/K|` projector `Π_K = ∑_C |C⟩⟨C|` onto the coset-symmetric subspace, `σ_K` is the maximally
mixed state on that subspace, and `tr(σ_K²) = |K|/|G| = 1/|G/K|` is exactly the reciprocal of its
rank — the "flatness" that makes the states distinguishable. The cross term
`tr(σ_K σ_{K'}) = |K∩K'|/|G|` is the overlap that the distinguishing-measurement /
union-bound argument controls; its multiplicativity under tensor powers (`(|K∩K'|/|G|)^m`) is what
forces the states apart once `m = 4 log|G| + 2` copies are taken.

## Proof

The computation is an elementary finite-group count. Writing `c = |G|⁻¹`,

`tr(σ_K σ_{K'}) = ∑_{i,j} σ_K i j · σ_{K'} j i = c² · #{(i, j) : i⁻¹j ∈ K ∧ i⁻¹j ∈ K'}`,

using `iK = jK ↔ i⁻¹j ∈ K` (`QuotientGroup.eq`) for both factors. The pair condition is
`i⁻¹j ∈ K ⊓ K'`, and for each fixed `i` the left-translation bijection `j ↦ i·h` (`Equiv.mulLeft`)
identifies `{j : i⁻¹j ∈ K ⊓ K'}` with `K ⊓ K'`, so the inner count is `|K ⊓ K'|` for every `i`.
Hence the total count is `|G| · |K ⊓ K'|` and `tr(σ_K σ_{K'}) = c² · |G| · |K ⊓ K'| = |K∩K'| / |G|`.
-/

namespace AxQM.Concrete

open Matrix
open scoped ComplexOrder

variable {G : Type*} [Group G] [Fintype G]

/-- **The Hilbert–Schmidt overlap of two coset density matrices**:
`tr(σ_K σ_{K'}) = |K ∩ K'| / |G|` for subgroups `K, K' ≤ G` of a finite group `G`. This is the core
quantitative fact behind Nielsen & Chuang, Problem 5.5 — it measures how nearly orthogonal the
single-copy reduced states of two candidate hidden subgroups are, and its `K = K'` case is the
purity `tr(σ_K²) = |K|/|G|` (`cosetDensity_trace_mul_self`).

The proof expands the trace as `∑_{i,j} σ_K i j · σ_{K'} j i`, recognises each entry pair as
`|G|⁻² · [i⁻¹j ∈ K ⊓ K']` (via `QuotientGroup.eq`), and counts: for each `i` the left-translation
bijection `j ↦ i·h` identifies `{j : i⁻¹j ∈ K ⊓ K'}` with `K ⊓ K'`, giving `|K ⊓ K'|` per row and
`|G| · |K ⊓ K'|` in total. -/
theorem cosetDensity_trace_mul (K K' : Subgroup G)
    [DecidablePred (· ∈ K)] [DecidablePred (· ∈ K')] :
    (cosetDensity K * cosetDensity K').trace
      = ((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G : ℂ) := by
  classical
  -- Each summand of `tr(σ_K σ_{K'}) = ∑_i ∑_j σ_K i j · σ_{K'} j i` collapses to the indicator of
  -- `i⁻¹j ∈ K ⊓ K'`, scaled by `|G|⁻²`.
  have hterm : ∀ i j : G, cosetDensity K i j * cosetDensity K' j i
      = if i⁻¹ * j ∈ K ⊓ K' then ((Fintype.card G : ℝ)⁻¹ : ℂ) ^ 2 else 0 := by
    intro i j
    have hK' : (j⁻¹ * i ∈ K') ↔ (i⁻¹ * j ∈ K') := by
      rw [show j⁻¹ * i = (i⁻¹ * j)⁻¹ from by group]; exact Subgroup.inv_mem_iff K'
    simp only [cosetDensity_apply, QuotientGroup.eq, hK', Subgroup.mem_inf]
    by_cases h1 : i⁻¹ * j ∈ K <;> by_cases h2 : i⁻¹ * j ∈ K' <;> simp [h1, h2, pow_two]
  -- The inner sum over `j` counts a full left coset of `K ⊓ K'`: `|K ⊓ K'|` nonzero terms.
  have hrow : ∀ i : G,
      (∑ j : G, if i⁻¹ * j ∈ K ⊓ K' then ((Fintype.card G : ℝ)⁻¹ : ℂ) ^ 2 else 0)
        = (Nat.card ↥(K ⊓ K') : ℂ) * ((Fintype.card G : ℝ)⁻¹ : ℂ) ^ 2 := by
    intro i
    rw [← Equiv.sum_comp (Equiv.mulLeft i)
      (fun j => if i⁻¹ * j ∈ K ⊓ K' then ((Fintype.card G : ℝ)⁻¹ : ℂ) ^ 2 else 0)]
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
    have hsplit : ∀ h : G,
        (if h ∈ K ⊓ K' then ((Fintype.card G : ℝ)⁻¹ : ℂ) ^ 2 else 0)
          = (if h ∈ K ⊓ K' then (1 : ℂ) else 0) * ((Fintype.card G : ℝ)⁻¹ : ℂ) ^ 2 := by
      intro h; split_ifs <;> simp
    rw [Finset.sum_congr rfl fun h _ => hsplit h, ← Finset.sum_mul, Finset.sum_boole,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- Assemble: `|G|` rows, each contributing `|K ⊓ K'| · |G|⁻²`.
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, hterm]
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  push_cast
  field_simp

/-- **The purity of the coset density matrix**: `tr(σ_K²) = tr(σ_K σ_K) = |K| / |G|`, the diagonal
(`K = K'`) case of the overlap `cosetDensity_trace_mul` (using `K ⊓ K = K`). Stated with `σ_K · σ_K`
(rather than `σ_K ^ 2`) so it needs only `[Fintype G]` and matches the operator-square
`ρ.op * ρ.op` appearing in `State.purity`. Since `σ_K = (|K|/|G|) Π_K` is `|K|/|G|` times a
rank-`|G/K|` projector, it is the maximally mixed state on the coset-symmetric subspace and its
purity `|K|/|G| = 1/|G/K|` is the reciprocal of that subspace's dimension. -/
theorem cosetDensity_trace_mul_self (K : Subgroup G) [DecidablePred (· ∈ K)] :
    (cosetDensity K * cosetDensity K).trace = ((Nat.card ↥K : ℝ) / Fintype.card G : ℂ) := by
  rw [cosetDensity_trace_mul K K, inf_idem]

/-- **The coset density matrix is a scalar multiple of a projector**: `σ_K · σ_K = (|K|/|G|) · σ_K`.
Since `σ_K = (|K|/|G|) Π_K` with `Π_K = ∑_C |C⟩⟨C|` an orthogonal projector (`Π_K² = Π_K`), squaring
multiplies the scalar exactly once: `σ_K² = (|K|/|G|)² Π_K = (|K|/|G|) σ_K`; equivalently
`(|G|/|K|) σ_K` is idempotent. Entrywise `(σ_K²) i j = ∑_k |G|⁻²·[iK=kK][kK=jK]` collapses — when
`iK = jK` there are exactly `|K|` values of `k` in that shared coset, and none otherwise — to
`|K|·|G|⁻²·[iK=jK] = (|K|/|G|)·σ_K i j`.

This is the identity that makes the operator square root `√σ_K = √(|G|/|K|)·σ_K` a *scalar multiple*
of `σ_K` (`AxQM.cosetDensityState_op_cfc_sqrt`), so the fidelity-metric distinguishability
of the reduced states — the quantum **affinity** `tr(√σ_K √σ_{K'}) = |K∩K'|/√(|K||K'|)` — is
computable in closed form, exactly as the Hilbert–Schmidt overlap `tr(σ_K σ_{K'})` is. -/
theorem cosetDensity_mul_self (K : Subgroup G) [DecidablePred (· ∈ K)] :
    cosetDensity K * cosetDensity K
      = ((Nat.card ↥K : ℝ) / Fintype.card G : ℂ) • cosetDensity K := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, cosetDensity_apply]
  by_cases hij : (↑i : G ⧸ K) = (↑j : G ⧸ K)
  · rw [ite_eq_left hij]
    -- On the shared coset each summand is `[iK=kK]·|G|⁻²`; there are `|K|` contributing `k`.
    have hL : ∀ k : G,
        (if (↑i : G ⧸ K) = ↑k then ((Fintype.card G : ℝ)⁻¹ : ℂ) else 0)
            * (if (↑k : G ⧸ K) = ↑j then ((Fintype.card G : ℝ)⁻¹ : ℂ) else 0)
          = if (↑i : G ⧸ K) = ↑k then ((Fintype.card G : ℝ)⁻¹ : ℂ) ^ 2 else 0 := by
      intro k
      by_cases h1 : (↑i : G ⧸ K) = ↑k
      · rw [ite_eq_left h1, ite_eq_left (h1.symm.trans hij), ite_eq_left h1, ← pow_two]
      · rw [ite_eq_right h1, ite_eq_right h1, zero_mul]
    rw [Finset.sum_congr rfl fun k _ => hL k]
    have hcount : (∑ k : G, if (↑i : G ⧸ K) = ↑k then ((Fintype.card G : ℝ)⁻¹ : ℂ) ^ 2 else 0)
        = (Nat.card ↥K : ℂ) * ((Fintype.card G : ℝ)⁻¹ : ℂ) ^ 2 := by
      simp only [QuotientGroup.eq]
      rw [← Equiv.sum_comp (Equiv.mulLeft i)
        (fun k => if i⁻¹ * k ∈ K then ((Fintype.card G : ℝ)⁻¹ : ℂ) ^ 2 else 0)]
      simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
      rw [Finset.sum_congr rfl fun h _ =>
        (by split_ifs <;> simp :
          (if h ∈ K then ((Fintype.card G : ℝ)⁻¹ : ℂ) ^ 2 else 0)
            = (if h ∈ K then (1 : ℂ) else 0) * ((Fintype.card G : ℝ)⁻¹ : ℂ) ^ 2),
        ← Finset.sum_mul, Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcount]
    have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    push_cast
    field_simp
  · rw [ite_eq_right hij, mul_zero]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : (↑i : G ⧸ K) = ↑k
    · rw [ite_eq_left h1, ite_eq_right (fun h => hij (h1.trans h)), mul_zero]
    · rw [ite_eq_right h1, zero_mul]

/-- **A proper subgroup has at most half the order of its overgroup** (the pigeonhole step of the
near-orthogonality bound). For finite subgroups `H ≤ L` of a group `G` with `H ≠ L`, Lagrange's
theorem gives `|H| ∣ |L|` and strictness gives `|H| < |L|`, so — being a proper divisor — `|H|` is
at most `|L| / 2`, i.e. `2·|H| ≤ |L|`. -/
theorem two_mul_card_le_of_lt {G : Type*} [Group G] [Finite G] (H L : Subgroup G)
    (hle : H ≤ L) (hne : H ≠ L) : 2 * Nat.card ↥H ≤ Nat.card ↥L := by
  have hdvd : Nat.card ↥H ∣ Nat.card ↥L := Subgroup.card_dvd_of_le hle
  have hss : (H : Set G) ⊂ (L : Set G) := SetLike.coe_ssubset_coe.mpr (lt_of_le_of_ne hle hne)
  have hlt : Nat.card ↥H < Nat.card ↥L := Set.Finite.card_lt_card (L : Set G).toFinite hss
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hlt ⊢
  have hk2 : 2 ≤ k := by
    by_contra h
    rw [not_le] at h
    interval_cases k <;> omega
  calc 2 * Nat.card ↥H = Nat.card ↥H * 2 := by ring
    _ ≤ Nat.card ↥H * k := Nat.mul_le_mul (le_refl _) hk2

/-- **Distinct hidden subgroups have near-orthogonal coset density matrices** (the single-copy count
behind Nielsen & Chuang, Problem 5.5). For two *distinct* subgroups `K ≠ K'` of a finite group `G`,
the order of their intersection is small enough that

`2 · |K ∩ K'|² ≤ |K| · |K'|`.

Equivalently the normalized Hilbert–Schmidt overlap `|K ∩ K'| / √(|K|·|K'|) ≤ 1/√2` — the two
reduced states meet at a "mutual angle" of at least `45°`. This is the elementary finite-group fact
underlying the physical claim that *"the pure-state outcomes corresponding to different possible
hidden subgroups are nearly orthogonal"*: `K ∩ K'` must be a **proper** subgroup of at least one of
`K, K'` (were it equal to both, `K = K ∩ K' = K'`), so by `two_mul_card_le_of_lt` its order is at
most half of that one's; multiplying by the trivial bound `|K ∩ K'| ≤` the other order gives the
result. Its trace form is `cosetDensity_trace_mul_sq_le`, and it tensorizes to the exponential
near-orthogonality `(|K ∩ K'|/√(|K||K'|))^m ≤ 2^{-m/2}` that forces the `m`-copy states apart. -/
theorem two_mul_card_inf_sq_le {G : Type*} [Group G] [Finite G] (K K' : Subgroup G) (hne : K ≠ K') :
    2 * Nat.card ↥(K ⊓ K') ^ 2 ≤ Nat.card ↥K * Nat.card ↥K' := by
  -- `K ⊓ K'` is a proper subgroup of `K` or of `K'`; otherwise it equals both, forcing `K = K'`.
  have key : K ⊓ K' ≠ K ∨ K ⊓ K' ≠ K' := by
    by_contra h
    rw [not_or, not_ne_iff, not_ne_iff] at h
    exact hne (h.1.symm.trans h.2)
  have hb : 0 < Nat.card ↥K := Nat.card_pos
  have hb' : 0 < Nat.card ↥K' := Nat.card_pos
  have hdb : Nat.card ↥(K ⊓ K') ∣ Nat.card ↥K := Subgroup.card_dvd_of_le inf_le_left
  have hdb' : Nat.card ↥(K ⊓ K') ∣ Nat.card ↥K' := Subgroup.card_dvd_of_le inf_le_right
  rcases key with hK | hK'
  · -- `K ⊓ K' ⊊ K`: halve on the `K` factor, bound `|K ∩ K'| ≤ |K'|` on the other.
    have h2d : 2 * Nat.card ↥(K ⊓ K') ≤ Nat.card ↥K := two_mul_card_le_of_lt _ _ inf_le_left hK
    have hd' : Nat.card ↥(K ⊓ K') ≤ Nat.card ↥K' := Nat.le_of_dvd hb' hdb'
    calc 2 * Nat.card ↥(K ⊓ K') ^ 2
        = (2 * Nat.card ↥(K ⊓ K')) * Nat.card ↥(K ⊓ K') := by ring
      _ ≤ Nat.card ↥K * Nat.card ↥K' := Nat.mul_le_mul h2d hd'
  · -- `K ⊓ K' ⊊ K'`: symmetric.
    have h2d : 2 * Nat.card ↥(K ⊓ K') ≤ Nat.card ↥K' := two_mul_card_le_of_lt _ _ inf_le_right hK'
    have hd : Nat.card ↥(K ⊓ K') ≤ Nat.card ↥K := Nat.le_of_dvd hb hdb
    calc 2 * Nat.card ↥(K ⊓ K') ^ 2
        = Nat.card ↥(K ⊓ K') * (2 * Nat.card ↥(K ⊓ K')) := by ring
      _ ≤ Nat.card ↥K * Nat.card ↥K' := Nat.mul_le_mul hd h2d

/-- **The trace form of near-orthogonality**: for distinct subgroups `K ≠ K'` the squared
Hilbert–Schmidt overlap of the coset density matrices is at most half the product of their purities,

`2 · tr(σ_K σ_{K'})² ≤ tr(σ_K²) · tr(σ_{K'}²)`.

This is `two_mul_card_inf_sq_le` transported through the trace evaluations `cosetDensity_trace_mul`
(`tr(σ_K σ_{K'}) = |K ∩ K'|/|G|`) and `cosetDensity_trace_mul_self` (`tr(σ_K²) = |K|/|G|`): the
factor `|G|⁻²` common to all three terms cancels, leaving the finite-group count. It states, at the
matrix level, that the single-copy reduced states of two distinct candidate hidden subgroups have a
mutual overlap bounded away from their self-overlaps — the quantitative near-orthogonality N&C
Problem 5.5 amplifies to `2^{-m/2}` by taking `m` copies. -/
theorem cosetDensity_trace_mul_sq_le (K K' : Subgroup G)
    [DecidablePred (· ∈ K)] [DecidablePred (· ∈ K')] (hne : K ≠ K') :
    2 * (cosetDensity K * cosetDensity K').trace ^ 2
      ≤ (cosetDensity K * cosetDensity K).trace * (cosetDensity K' * cosetDensity K').trace := by
  have hpoly : 2 * (Nat.card ↥(K ⊓ K') : ℝ) ^ 2 ≤ (Nat.card ↥K : ℝ) * (Nat.card ↥K' : ℝ) := by
    exact_mod_cast two_mul_card_inf_sq_le K K' hne
  have hreal : 2 * ((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G) ^ 2
      ≤ ((Nat.card ↥K : ℝ) / Fintype.card G) * ((Nat.card ↥K' : ℝ) / Fintype.card G) := by
    rw [show 2 * ((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G) ^ 2
          = (2 * (Nat.card ↥(K ⊓ K') : ℝ) ^ 2) / (Fintype.card G : ℝ) ^ 2 from by ring,
        show ((Nat.card ↥K : ℝ) / Fintype.card G) * ((Nat.card ↥K' : ℝ) / Fintype.card G)
          = ((Nat.card ↥K : ℝ) * (Nat.card ↥K' : ℝ)) / (Fintype.card G : ℝ) ^ 2 from by ring,
        div_le_div_iff_of_pos_right (by positivity)]
    exact hpoly
  rw [cosetDensity_trace_mul, cosetDensity_trace_mul_self, cosetDensity_trace_mul_self]
  exact_mod_cast hreal

end AxQM.Concrete
