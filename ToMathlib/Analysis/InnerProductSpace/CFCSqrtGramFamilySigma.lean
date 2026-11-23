/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFCSqrtGramFamily

/-!
# The message-grouped form of the pretty-good-measurement error estimate

In Nielsen & Chuang's random-coding proof of the Holevo–Schumacher–Westmoreland theorem
(Theorem 12.8, achievability), the pretty-good decoder acts on the whole codebook at once: its Gram
operator is built from the **global** family of typical codeword eigenvectors, indexed by the pair
`c = (M, κ)` of a message `M` and a conditional-typical eigenindex `κ ∈ T_M`.  The codeword-family
error bound `InnerProductSpace.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le` (N&C eq. (12.94))
therefore fires at this global index and bounds the total decoding deficit

`2·∑_c λ_c (1 − α_c)`,   `α_c = re⟪e_c, √Γ e_c⟫`,   `Γ = V⋆·V`,   `V = synthesisMap ψ`,

by three right-hand frame sums over the global family.

To feed each of those sums into the *per-message* physical trace identities of the achievability
proof (`3·tr(σ_M(1−P))`, `∑_{M'≠M} tr(P σ_M P P_{M'})`, `tr(σ_M(1−P_M))`, N&C eqs. (12.95),
(12.79)), the global sums must be **grouped by the message** `M`, and the double sum
`∑_c ∑_{c'} λ_c |⟪ψ_c, ψ_{c'}⟫|²` split — for each block `M` — into the **same-message diagonal**
`M' = M` (matched by the same-message spur bound) plus the **cross-message** off-diagonal `M' ≠ M`
(matched by the confusion bound).

## What this file provides

* `InnerProductSpace.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le_sigma` — the codeword-family
  error bound `two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le` restated over a **sigma index**
  `Σ a, γ a`
  (the block index `a` being the message `M`, and `γ a` the block's eigenindex set `T_M`), with its
  right-hand side regrouped by the block `a`: the eigenvalue mass and the diagonal `‖ψ_c‖²` weight
  collect per block, and the frame double sum splits into the same-block part
  `∑_{κ,κ' in block a} λ |⟪ψ_{a,κ}, ψ_{a,κ'}⟫|²` and the off-block part
  `∑_{a'≠a} ∑_{κ in a, κ' in a'} λ |⟪ψ_{a,κ}, ψ_{a',κ'}⟫|²`.

  The left-hand side is unchanged (the total deficit `2·∑_c λ_c (1 − α_c)` over the sigma index;
  regroup it as `∑_a ∑_κ` with `Fintype.sum_sigma` at the point of use).

## Proof

Purely the block-grouping of the flat bound `two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le`.  Each
of its three right-hand sums is turned into a sum over the block index by `Fintype.sum_sigma`; the
`2·` and `−3·` scalars distribute into the block sum (`Finset.mul_sum`) and the three block sums
recombine into one (`Finset.sum_sub_distrib`, `Finset.sum_add_distrib`).  Inside a block, the inner
factor `∑_{c'} λ_{a,κ} |⟪ψ_{a,κ}, ψ_{c'}⟫|²` is likewise `Fintype.sum_sigma`'d and its outer block
sum split off the diagonal term with `Finset.add_sum_erase`; a `Finset.sum_comm` moves the block
sum outside the eigenindex sum, and `ring` reassembles the block term.

The flat codeword-family bound it regroups is in
`ToMathlib.Analysis.InnerProductSpace.CFCSqrtGramFamily`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  Theorem 12.8, Box 12.5, eqs. (12.94), (12.95), (12.79).
-/

@[expose] public section

open scoped InnerProductSpace

open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {γ : ι → Type*} [∀ a, Fintype (γ a)]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
  [CompleteSpace G]

/-- **The message-grouped codeword-family form of the pretty-good-measurement error estimate**
(Nielsen & Chuang, Box 12.5, eqs. (12.94)→(12.95), block-grouped by message).  For a family
`ψ : (Σ a, γ a) → G` over a sigma index — the block index `a` being Nielsen & Chuang's message `M`
and `γ a` the block's conditional-typical eigenindex set `T_M` — with synthesis operator
`V = synthesisMap ψ`, Gram operator `Γ = V⋆·V`, and nonnegative real weights `λ : (Σ a, γ a) → ℝ`,

`2·∑_c λ_c (1 − re⟪e_c, √Γ e_c⟫)`
`  ≤  ∑_a [ (2·∑_κ λ_{a,κ} − 3·∑_κ λ_{a,κ}‖ψ_{a,κ}‖² + ∑_κ λ_{a,κ} ∑_{κ'} |⟪ψ_{a,κ}, ψ_{a,κ'}⟫|²)`
`           + ∑_{a'≠a} ∑_κ λ_{a,κ} ∑_{κ'} |⟪ψ_{a,κ}, ψ_{a',κ'}⟫|² ]`,

where `c = (a, κ)` ranges over the sigma index, `e_c` are the standard basis vectors of
`EuclideanSpace ℂ (Σ a, γ a)`, `√Γ = cfc Real.sqrt Γ`, and `α_c = re⟪e_c, √Γ e_c⟫` is Nielsen &
Chuang's diagonal decoding overlap `α_{(M,K),(M,K)}` (Box 12.5, `Γ^{1/2} = [α]`).

This is `two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le` at the sigma-indexed family, with the three
right-hand frame sums grouped by the block `a`.  The bracketed per-block term separates the
**same-message** part (the diagonal `a' = a`, whose three sums are bounded by the same-message spur
bound at codeword `σ_M`) from the **cross-message** part (`a' ≠ a`, whose off-diagonal frame double
sum is bounded, per pair `(M, M')`, by the confusion bound).  The left-hand side is the total
decoding deficit `2·∑_c λ_c(1 − α_c)`; regroup it as `∑_a ∑_κ` with `Fintype.sum_sigma` where the
per-message left-hand side is wanted. -/
theorem two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le_sigma
    (ψ : (Σ a, γ a) → G) (lam : (Σ a, γ a) → ℝ) (hlam : ∀ p, 0 ≤ lam p) :
    2 * ∑ p, lam p * (1 - RCLike.re (inner ℂ (EuclideanSpace.basisFun (Σ a, γ a) ℂ p)
        ((cfc Real.sqrt ((adjoint (synthesisMap ψ)).comp (synthesisMap ψ)))
          (EuclideanSpace.basisFun (Σ a, γ a) ℂ p))))
      ≤ ∑ a, ((2 * ∑ κ : γ a, lam ⟨a, κ⟩
          - 3 * ∑ κ : γ a, lam ⟨a, κ⟩ * ‖ψ ⟨a, κ⟩‖ ^ 2
          + ∑ κ : γ a, lam ⟨a, κ⟩ * ∑ κ' : γ a, ‖inner ℂ (ψ ⟨a, κ⟩) (ψ ⟨a, κ'⟩)‖ ^ 2)
        + ∑ a' ∈ Finset.univ.erase a, ∑ κ : γ a, lam ⟨a, κ⟩
            * ∑ κ' : γ a', ‖inner ℂ (ψ ⟨a, κ⟩) (ψ ⟨a', κ'⟩)‖ ^ 2) := by
  refine (two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le ψ lam hlam).trans (le_of_eq ?_)
  -- Group each of the three right-hand sums of the flat bound by the block index `a`.
  rw [Fintype.sum_sigma (fun p => lam p), Fintype.sum_sigma (fun p => lam p * ‖ψ p‖ ^ 2),
    Fintype.sum_sigma (fun p => ∑ q, lam p * ‖inner ℂ (ψ p) (ψ q)‖ ^ 2),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  -- Split the block's frame double sum into its same-block diagonal and off-block parts.
  have hthird : (∑ κ : γ a, ∑ q, lam ⟨a, κ⟩ * ‖inner ℂ (ψ ⟨a, κ⟩) (ψ q)‖ ^ 2)
      = (∑ κ : γ a, lam ⟨a, κ⟩ * ∑ κ' : γ a, ‖inner ℂ (ψ ⟨a, κ⟩) (ψ ⟨a, κ'⟩)‖ ^ 2)
        + ∑ a' ∈ Finset.univ.erase a, ∑ κ : γ a, lam ⟨a, κ⟩
            * ∑ κ' : γ a', ‖inner ℂ (ψ ⟨a, κ⟩) (ψ ⟨a', κ'⟩)‖ ^ 2 := by
    have hperκ : ∀ κ : γ a, (∑ q, lam ⟨a, κ⟩ * ‖inner ℂ (ψ ⟨a, κ⟩) (ψ q)‖ ^ 2)
        = lam ⟨a, κ⟩ * ∑ κ' : γ a, ‖inner ℂ (ψ ⟨a, κ⟩) (ψ ⟨a, κ'⟩)‖ ^ 2
          + lam ⟨a, κ⟩ * ∑ a' ∈ Finset.univ.erase a,
              ∑ κ' : γ a', ‖inner ℂ (ψ ⟨a, κ⟩) (ψ ⟨a', κ'⟩)‖ ^ 2 := fun κ => by
      rw [← Finset.mul_sum, Fintype.sum_sigma (fun q => ‖inner ℂ (ψ ⟨a, κ⟩) (ψ q)‖ ^ 2),
        ← Finset.add_sum_erase Finset.univ
          (fun a' => ∑ κ' : γ a', ‖inner ℂ (ψ ⟨a, κ⟩) (ψ ⟨a', κ'⟩)‖ ^ 2) (Finset.mem_univ a),
        mul_add]
    rw [Finset.sum_congr rfl (fun κ _ => hperκ κ), Finset.sum_add_distrib]
    congr 1
    -- Move the off-block sum outside the eigenindex sum.
    rw [Finset.sum_congr rfl fun κ (_ : κ ∈ Finset.univ) =>
      Finset.mul_sum (Finset.univ.erase a)
        (fun a' => ∑ κ' : γ a', ‖inner ℂ (ψ ⟨a, κ⟩) (ψ ⟨a', κ'⟩)‖ ^ 2) (lam ⟨a, κ⟩),
      Finset.sum_comm]
  rw [hthird]; ring

end InnerProductSpace
