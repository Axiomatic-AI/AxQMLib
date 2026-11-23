/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CosetStateOverlap
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Concrete: tensor powers of the coset-density overlap

This file promotes the single-copy Hilbert–Schmidt overlap of coset density matrices
(`AxQM.Concrete.CosetStateOverlap`) to the **`m`-copy tensor powers** that carry the quantitative
content of Nielsen & Chuang, Problem 5.5 (the non-Abelian hidden subgroup problem).

## The key observation: `σ_K^{⊗m}` is again a coset density matrix

For a finite index type `ι` (think `ι = Fin m`), the `m`-fold tensor power `σ_K^{⊗ι}` of the coset
density matrix `σ_K = cosetDensity K` (on `ℂ[G]`) is *itself* a coset density matrix — that of the
**product subgroup** `K^ι = ∏_{i} K` of the direct-power group `G^ι = (ι → G)`. Indeed the coset
condition factors coordinatewise,

`(g_i)_i · K^ι = (h_i)_i · K^ι ↔ ∀ i, g_i K = h_i K`,

so the entry of `cosetDensity (K^ι)` at `((g_i)_i, (h_i)_i)` is
`|G^ι|⁻¹ ∏_i [g_i K = h_i K] = ∏_i (|G|⁻¹ [g_i K = h_i K])`, exactly the Kronecker-power entry of
`σ_K`. We therefore never build any Kronecker machinery: the `m`-copy quantities are read off from
the single-copy `cosetDensity_trace_mul` applied to the product subgroups `K^ι, K'^ι ≤ G^ι`.

This is the mathematically clean route to the reduced state `σ_K^{⊗m}` of the `m`-copy HSP query
state (5.80): the `m`-copy query register is the single-copy register for the group `G^ι` and the
coordinatewise query function, so its reduced state is `cosetDensity (K^ι)` by the single-copy
reduced-state theorem — no `m`-fold tensor of states is needed.

## What is proved

Writing `Kᵖ = Subgroup.pi Set.univ (fun _ => K)` for the product subgroup (`= K^ι`):

* `cosetDensity_pi_trace_mul` — **tensor-power multiplicativity of the overlap**:
  `tr(σ_{Kᵖ} σ_{K'ᵖ}) = tr(σ_K σ_{K'})^{|ι|}`, i.e. `(|K∩K'|/|G|)^m`.
* `cosetDensity_pi_trace_mul_self` — its diagonal `tr(σ_{Kᵖ}²) = tr(σ_K²)^{|ι|} = (|K|/|G|)^m`.
* `cosetDensity_pi_trace_mul_sq_le` — **exponential near-orthogonality**: for distinct subgroups
  `K ≠ K'`, `2^{|ι|} · tr(σ_{Kᵖ} σ_{K'ᵖ})² ≤ tr(σ_{Kᵖ}²) · tr(σ_{K'ᵖ}²)`, i.e. the normalized
  overlap `(|K∩K'|/√(|K||K'|))^m ≤ 2^{-m/2}`.

The two supporting group-theoretic facts are `subgroupPi_const_inf` (intersection distributes over
the product, `Kᵖ ⊓ K'ᵖ = (K ⊓ K')ᵖ`) and `natCard_subgroupPi_const` (the product subgroup has order
`|K|^{|ι|}`).
-/

namespace AxQM.Concrete

open Matrix
open scoped ComplexOrder

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [Group G] [Fintype G]

/-- Membership in a **constant product subgroup** `∏_i H ≤ (ι → G)` is decidable: `f ∈ ∏_i H` is the
finite conjunction `∀ i, f i ∈ H` of the decidable memberships `f i ∈ H`. This lets the coset
density matrix `cosetDensity (∏_i H)` be formed from `[DecidablePred (· ∈ H)]` alone. -/
instance decidablePredMemPiConst (H : Subgroup G) [DecidablePred (· ∈ H)] :
    DecidablePred (· ∈ Subgroup.pi (Set.univ : Set ι) fun _ => H) := fun f =>
  decidable_of_iff (∀ i, f i ∈ H) (by simp [Subgroup.mem_pi])

omit [Fintype ι] [DecidableEq ι] [Fintype G] in
/-- **Intersection distributes over constant product subgroups**:
`(∏_i K) ⊓ (∏_i K') = ∏_i (K ⊓ K')` in `(ι → G)`. Membership on both sides is `∀ i, f i ∈ K ∧ f i ∈
K'` after distributing the two universal quantifiers (`forall_and`). This is the group-theoretic
input that turns the intersection appearing in `cosetDensity_trace_mul` for the product subgroups
into a product of single-copy intersections. -/
theorem subgroupPi_const_inf (K K' : Subgroup G) :
    (Subgroup.pi (Set.univ : Set ι) fun _ => K) ⊓ (Subgroup.pi (Set.univ : Set ι) fun _ => K')
      = Subgroup.pi (Set.univ : Set ι) fun _ => K ⊓ K' := by
  ext f
  simp only [Subgroup.mem_inf, Subgroup.mem_pi, Set.mem_univ, forall_true_left, forall_and]

omit [DecidableEq ι] [Fintype G] in
/-- **The order of a constant product subgroup**: `|∏_i H| = |H|^{|ι|}` for `H ≤ G` and a finite
index type `ι`. The subtype `↥(∏_i H)` of functions `f : ι → G` with `∀ i, f i ∈ H` is equivalent to
`ι → ↥H` (`Equiv.subtypePiEquivPi`), whose cardinality is the constant product `∏_i |H| = |H|^{|ι|}`
(`Nat.card_pi`). This is the `m`-copy scaling `|K^{⊗m}| = |K|^m` behind the tensor-power overlap. -/
theorem natCard_subgroupPi_const (H : Subgroup G) :
    Nat.card ↥(Subgroup.pi (Set.univ : Set ι) fun _ => H) = Nat.card ↥H ^ Fintype.card ι := by
  rw [Nat.card_congr ((Equiv.subtypeEquivRight fun f => by simp [Subgroup.mem_pi]).trans
        (Equiv.subtypePiEquivPi (p := fun (_ : ι) x => x ∈ H))),
      Nat.card_pi, Finset.prod_const, Finset.card_univ]

/-- **Tensor-power multiplicativity of the coset-density overlap**: the Hilbert–Schmidt overlap of
the `|ι|`-fold tensor powers `σ_K^{⊗ι} = cosetDensity (K^ι)` (`K^ι = ∏_i K` the product subgroup of
`G^ι = (ι → G)`) is the `|ι|`-th power of the single-copy overlap,

`tr(σ_{Kᵖ} σ_{K'ᵖ}) = tr(σ_K σ_{K'})^{|ι|}`   ( `= (|K ∩ K'|/|G|)^{|ι|}` ).

This is the multiplicativity of Hilbert–Schmidt overlap under tensor products, obtained without any
Kronecker machinery: `cosetDensity_trace_mul` gives both sides as
`|K^ι ∩ K'^ι| / |G^ι|` and `(|K ∩ K'|/|G|)^{|ι|}`, which agree because intersection distributes over
the product (`subgroupPi_const_inf`), `|K^ι ∩ K'^ι| = |K ∩ K'|^{|ι|}` (`natCard_subgroupPi_const`),
and `|G^ι| = |G|^{|ι|}` (`Fintype.card_fun`). It is the mechanism that forces the reduced states of
distinct candidate hidden subgroups apart as the number `m = |ι|` of coset samples grows. -/
theorem cosetDensity_pi_trace_mul (K K' : Subgroup G)
    [DecidablePred (· ∈ K)] [DecidablePred (· ∈ K')] :
    (cosetDensity (Subgroup.pi (Set.univ : Set ι) fun _ => K)
        * cosetDensity (Subgroup.pi (Set.univ : Set ι) fun _ => K')).trace
      = (cosetDensity K * cosetDensity K').trace ^ Fintype.card ι := by
  rw [cosetDensity_trace_mul, cosetDensity_trace_mul, subgroupPi_const_inf,
    natCard_subgroupPi_const, Fintype.card_fun]
  push_cast
  rw [div_pow]

/-- **Tensor-power multiplicativity of the purity**: the diagonal (`K' = K`) case of
`cosetDensity_pi_trace_mul`,

`tr(σ_{Kᵖ}²) = tr(σ_K²)^{|ι|}`   ( `= (|K|/|G|)^{|ι|}` ),

the purity of the `|ι|`-fold tensor power `σ_K^{⊗ι}` of the coset density matrix. -/
theorem cosetDensity_pi_trace_mul_self (K : Subgroup G) [DecidablePred (· ∈ K)] :
    (cosetDensity (Subgroup.pi (Set.univ : Set ι) fun _ => K)
        * cosetDensity (Subgroup.pi (Set.univ : Set ι) fun _ => K)).trace
      = (cosetDensity K * cosetDensity K).trace ^ Fintype.card ι :=
  cosetDensity_pi_trace_mul K K

/-- **Exponential near-orthogonality of the tensor-power reduced states** (the quantitative heart of
Nielsen & Chuang, Problem 5.5). For *distinct* subgroups `K ≠ K'` of a finite group `G` and
`m = |ι|` copies, the squared Hilbert–Schmidt overlap of the tensor powers is suppressed by `2^{-m}`
relative
to the product of the purities,

`2^{|ι|} · tr(σ_{Kᵖ} σ_{K'ᵖ})² ≤ tr(σ_{Kᵖ}²) · tr(σ_{K'ᵖ}²)`,

equivalently the normalized overlap `tr(σ_{Kᵖ} σ_{K'ᵖ}) / √(tr σ_{Kᵖ}² · tr σ_{K'ᵖ}²) =
(|K∩K'|/√(|K||K'|))^m ≤ (1/√2)^m = 2^{-m/2}`. This is the single-copy bound
`cosetDensity_trace_mul_sq_le` (`2·tr(σ_K σ_{K'})² ≤ tr(σ_K²)·tr(σ_{K'}²)`, i.e. `2·|K∩K'|² ≤
|K|·|K'|`) raised to the `m`-th power through the tensor-power multiplicativity
`cosetDensity_pi_trace_mul`: with the three overlaps replaced by their `m`-th powers, the inequality
is `(2·tr(σ_K σ_{K'})²)^m ≤ (tr(σ_K²)·tr(σ_{K'}²))^m`, monotone in the single-copy bound. It is what
makes `m = 4 log|G| + 2` samples enough to drive the pairwise overlap below `2^{-2}/|G|²`, the
quantitative statement that "the pure-state outcomes for different possible hidden subgroups are
nearly orthogonal". -/
theorem cosetDensity_pi_trace_mul_sq_le (K K' : Subgroup G)
    [DecidablePred (· ∈ K)] [DecidablePred (· ∈ K')] (hne : K ≠ K') :
    2 ^ Fintype.card ι
        * (cosetDensity (Subgroup.pi (Set.univ : Set ι) fun _ => K)
            * cosetDensity (Subgroup.pi (Set.univ : Set ι) fun _ => K')).trace ^ 2
      ≤ (cosetDensity (Subgroup.pi (Set.univ : Set ι) fun _ => K)
            * cosetDensity (Subgroup.pi (Set.univ : Set ι) fun _ => K)).trace
        * (cosetDensity (Subgroup.pi (Set.univ : Set ι) fun _ => K')
            * cosetDensity (Subgroup.pi (Set.univ : Set ι) fun _ => K')).trace := by
  rw [cosetDensity_pi_trace_mul K K', cosetDensity_pi_trace_mul K K,
    cosetDensity_pi_trace_mul K' K', cosetDensity_trace_mul, cosetDensity_trace_mul_self,
    cosetDensity_trace_mul_self]
  -- the single-copy group-theoretic core, cast to `ℝ`
  have hpoly : 2 * (Nat.card ↥(K ⊓ K') : ℝ) ^ 2 ≤ (Nat.card ↥K : ℝ) * (Nat.card ↥K' : ℝ) := by
    exact_mod_cast two_mul_card_inf_sq_le K K' hne
  -- the single-copy trace bound, divided through by `|G|²`
  have hkey : 2 * ((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G) ^ 2
      ≤ ((Nat.card ↥K : ℝ) / Fintype.card G) * ((Nat.card ↥K' : ℝ) / Fintype.card G) := by
    rw [show 2 * ((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G) ^ 2
          = (2 * (Nat.card ↥(K ⊓ K') : ℝ) ^ 2) / (Fintype.card G : ℝ) ^ 2 from by ring,
        show ((Nat.card ↥K : ℝ) / Fintype.card G) * ((Nat.card ↥K' : ℝ) / Fintype.card G)
          = ((Nat.card ↥K : ℝ) * (Nat.card ↥K' : ℝ)) / (Fintype.card G : ℝ) ^ 2 from by ring,
        div_le_div_iff_of_pos_right (by positivity)]
    exact hpoly
  -- raise the single-copy bound to the `m`-th power
  have hreal : (2 : ℝ) ^ Fintype.card ι
        * (((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G) ^ Fintype.card ι) ^ 2
      ≤ ((Nat.card ↥K : ℝ) / Fintype.card G) ^ Fintype.card ι
        * ((Nat.card ↥K' : ℝ) / Fintype.card G) ^ Fintype.card ι := by
    calc (2 : ℝ) ^ Fintype.card ι
            * (((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G) ^ Fintype.card ι) ^ 2
        = (2 * ((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G) ^ 2) ^ Fintype.card ι := by
          rw [mul_pow, pow_right_comm]
      _ ≤ (((Nat.card ↥K : ℝ) / Fintype.card G) * ((Nat.card ↥K' : ℝ) / Fintype.card G))
            ^ Fintype.card ι := pow_le_pow_left₀ (by positivity) hkey _
      _ = ((Nat.card ↥K : ℝ) / Fintype.card G) ^ Fintype.card ι
            * ((Nat.card ↥K' : ℝ) / Fintype.card G) ^ Fintype.card ι := mul_pow _ _ _
  exact_mod_cast hreal

omit [Fintype ι] [DecidableEq ι] [Fintype G] in
/-- **Coset equality in a constant product subgroup factors coordinatewise.** Two functions
`g₁, g₂ : ι → G` lie in the same left coset of the product subgroup `K^ι = ∏_i K ≤ (ι → G)` iff they
lie in the same left coset of `K` in every coordinate:

`(g₁ : (ι → G) ⧸ K^ι) = g₂ ↔ ∀ i, (g₁ i : G ⧸ K) = g₂ i`.

The coset condition `g₁⁻¹ g₂ ∈ K^ι` is (`Subgroup.mem_pi`) the coordinatewise conjunction
`∀ i, (g₁ i)⁻¹ (g₂ i) ∈ K`, each conjunct being the single-coordinate coset condition
(`QuotientGroup.eq`). This is the group-theoretic fact behind the `m`-copy reduced-state lift of
Nielsen & Chuang, Problem 5.5: a query function `f` constant and distinct on the cosets of `K` gives
a coordinatewise query `g ↦ (f (g i))_i` that is constant and distinct on the cosets of `K^ι`, so
the `m`-copy query state is the single-copy query state for the group `G^ι`. -/
theorem quotient_mk_pi_const_eq_iff (K : Subgroup G) (g₁ g₂ : ι → G) :
    (↑g₁ : (ι → G) ⧸ Subgroup.pi (Set.univ : Set ι) fun _ => K) = ↑g₂
      ↔ ∀ i, (↑(g₁ i) : G ⧸ K) = ↑(g₂ i) := by
  simp only [QuotientGroup.eq, Subgroup.mem_pi, Set.mem_univ, forall_true_left, Pi.mul_apply,
    Pi.inv_apply]

end AxQM.Concrete
