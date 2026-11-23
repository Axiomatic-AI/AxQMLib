/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.MutualInformationMap
public import ToMathlib.Analysis.SpecialFunctions.ConditionalEntropyChain
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Subadditivity of the Shannon entropy of a tuple of random variables

Building on the random-variable entropy development (`Real.entropyMap`, `Real.mutualInfoMap` and the
law `Real.law` of a random variable), this file proves the **subadditivity of the Shannon entropy**
in its `n`-variable form: for random variables `X₀, …, X_{n-1}` on a finite probability space, the
joint entropy is at most the sum of the marginal entropies,

`H(X₀, …, X_{n-1}) ≤ ∑ᵢ H(Xᵢ)`  (`Real.entropyMap_pi_le`).

This is the `n`-fold generalization of the two-variable subadditivity `H(X, Y) ≤ H(X) + H(Y)`
(`Real.entropy_le_add_marginal`, Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.3), and is the entropy "single-letterization" step underlying the converse of Shannon's
noisy channel coding theorem (N&C Theorem 12.7): the output entropy `H(Y₁, …, Yₙ)` of `n` channel
uses is bounded by the sum `∑ᵢ H(Yᵢ)` of the per-use output entropies.

## Model

Random variables are modelled as functions `Xᵢ : Ω → α` on a common finite sample space `Ω`
carrying a probability weight `μ : Ω → ℝ`, exactly as in `Real.condEntropyMap` /
`Real.mutualInfoMap` and the chaining rule `Real.condEntropy_law_chain`. The entropy of a
random variable is
`Real.entropyMap μ X = H(X)`, the Shannon entropy of the push-forward law `Real.law μ X`; modelling
through a shared sample space makes the joint entropy `H(X₀, …, X_{n-1})` of an arbitrary tuple free
(just tuple the variables into `fun ω ↦ (fun i ↦ Xᵢ ω)`).

## Main results

* `Real.entropyMap_prod_le` — two-variable subadditivity `H(f, g) ≤ H(f) + H(g)` in the
  random-variable form.
* `Real.mutualInfoMap_nonneg` — non-negativity of the mutual information `H(f : g) ≥ 0` (N&C
  Theorem 11.3, part 5), an immediate corollary.
* `Real.entropyMap_pi_le` — the `n`-variable subadditivity `H(X₀, …, X_{n-1}) ≤ ∑ᵢ H(Xᵢ)`.
* `Real.entropy_le_sum_entropy_proj` — the coordinate subadditivity `H(Y) ≤ ∑ⱼ H(Yⱼ)` of the
  entropy of a distribution on a finite product `Fin n → ι`, the explicit-distribution reading of
  `Real.entropyMap_pi_le` (its coordinate marginals `law μ (·ⱼ)`).

`entropy_le_sum_entropy_proj` is the output-entropy single-letterization ingredient for the converse
of Shannon's noisy channel coding theorem (N&C Theorem 12.7): the mutual information
`H(Xⁿ : Yⁿ) = H(Yⁿ) − H(Yⁿ | Xⁿ)` of `n` memoryless channel uses is bounded by combining the output
bound `H(Yⁿ) ≤ ∑ⱼ H(Yⱼ)` (here) with the noise-entropy factoring
`H(Yⁿ | Xⁿ = xⁿ) = ∑ⱼ H(q(·|xⱼ))` (`Real.entropy_pi_prod`,
`ToMathlib/Analysis/SpecialFunctions/ShannonEntropy.lean`).

## Design

This is pure classical information theory — it quantifies over functions `μ : Ω → ℝ` and
`Xᵢ : Ω → α`, building on the `Real.entropyMap` / `Real.law` developments. Entropy is measured in
*nats* (natural logarithm), as elsewhere in the library; the inequality is base-independent, so
this is a faithful reformulation.

The two-variable step reuses `Real.entropy_le_add_marginal` on the joint law `law μ (fun ω ↦
(f ω, g ω))`, whose first and second marginals are the laws of `f` and `g`
(`Real.marginalFst_law_prod` / `Real.marginalSnd_law_prod`). The `n`-variable step is an induction
that peels off the first coordinate through `Fin.consEquiv` (a relabeling of the value alphabet,
under which the entropy of a law is invariant, `Real.entropy_law_congr_equiv`).
-/

@[expose] public section

namespace Real

variable {Ω : Type*} [Fintype Ω]

/-! ### Basic properties of the law of a random variable -/

/-- The law of a random variable is nonnegative when the weight is: `law μ X x ≥ 0`. -/
theorem law_nonneg {γ : Type*} [DecidableEq γ] {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    (X : Ω → γ) (x : γ) : 0 ≤ law μ X x :=
  Finset.sum_nonneg fun ω _ => by split_ifs; exacts [hμ ω, le_refl 0]

/-- The total mass of the law of a random variable equals the total mass of the weight:
`∑ₓ law μ X x = ∑_ω μ ω`. In particular the law of `X` under a probability weight is again a
probability distribution. -/
theorem sum_law {γ : Type*} [Fintype γ] [DecidableEq γ] (μ : Ω → ℝ) (X : Ω → γ) :
    ∑ x, law μ X x = ∑ ω, μ ω := by
  simp only [law]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp

/-- The entropy of a random variable is the Shannon entropy of its law:
`entropyMap μ f = entropy (law μ f)`. (Both unfold to the entropy of the same push-forward
distribution, so this is definitional.) -/
theorem entropyMap_eq_entropy_law {β : Type*} [Fintype β] [DecidableEq β]
    (μ : Ω → ℝ) (f : Ω → β) : entropyMap μ f = entropy (law μ f) := rfl

/-- The law of the **identity** random variable is the distribution itself: `law μ id = μ`. The
push-forward of `μ` along `id` fixes each point, so `law μ id x = ∑_{ω : ω = x} μ ω = μ x`. -/
theorem law_id [DecidableEq Ω] (μ : Ω → ℝ) : law μ (id : Ω → Ω) = μ := by
  funext x
  rw [law]
  exact Fintype.sum_ite_eq' x μ

/-- **Expectation under a push-forward law** (law of the unconscious statistician):
`∑ₓ (law μ X) x · f x = ∑_ω μ ω · f (X ω)` — the expectation of `f` under the law of `X` is the
`μ`-average of `f ∘ X`. Specializes to `Real.sum_law` at `f = 1`. -/
theorem sum_law_mul {γ : Type*} [Fintype γ] [DecidableEq γ] (μ : Ω → ℝ) (X : Ω → γ) (f : γ → ℝ) :
    ∑ x, law μ X x * f x = ∑ ω, μ ω * f (X ω) := by
  simp only [law, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp_rw [ite_mul, zero_mul]
  exact Fintype.sum_ite_eq (X ω) fun x => μ ω * f x

/-- The first marginal of the joint law of `(X, Y)` is the law of `X`:
`marginalFst (law μ (X, Y)) = law μ X` (the companion of `Real.marginalSnd_law_prod`). -/
theorem marginalFst_law_prod {ζ γ : Type*} [DecidableEq ζ] [Fintype γ] [DecidableEq γ]
    (μ : Ω → ℝ) (X : Ω → ζ) (Y : Ω → γ) :
    marginalFst (law μ (fun ω => (X ω, Y ω))) = law μ X := by
  funext x
  rw [marginalFst_apply]
  simp only [law]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hfac : ∀ y, (if (X ω, Y ω) = (x, y) then μ ω else 0)
      = if Y ω = y then (if X ω = x then μ ω else 0) else 0 := fun y => by
    by_cases hx : X ω = x <;> by_cases hy : Y ω = y <;> simp [Prod.ext_iff, hx, hy]
  rw [Finset.sum_congr rfl fun y _ => hfac y, Finset.sum_ite_eq]
  simp

/-! ### Subadditivity -/

/-- **Two-variable subadditivity** of the Shannon entropy in the random-variable form
(Nielsen & Chuang Theorem 11.3, part 4): for random variables `f`, `g` on a finite probability
space with weight `μ`, `H(f, g) ≤ H(f) + H(g)`. This is `Real.entropy_le_add_marginal` applied to
the joint law `law μ (f, g)`, whose marginals are the laws of `f` and `g`. -/
theorem entropyMap_prod_le {β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    {μ : Ω → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω) (hμ1 : ∑ ω, μ ω = 1) (f : Ω → β) (g : Ω → γ) :
    entropyMap μ (fun ω => (f ω, g ω)) ≤ entropyMap μ f + entropyMap μ g := by
  have hp0 : ∀ q, 0 ≤ law μ (fun ω => (f ω, g ω)) q := fun q => law_nonneg hμ0 _ q
  have hp1 : ∑ q, law μ (fun ω => (f ω, g ω)) q = 1 := by rw [sum_law]; exact hμ1
  have h := entropy_le_add_marginal hp0 hp1
  rw [marginalFst_law_prod, marginalSnd_law_prod] at h
  simpa only [entropyMap_eq_entropy_law] using h

/-- **Non-negativity of the mutual information** (Nielsen & Chuang Theorem 11.3, part 5) in the
random-variable form: `H(f : g) ≥ 0`. Immediate from two-variable subadditivity
(`Real.entropyMap_prod_le`). -/
theorem mutualInfoMap_nonneg {β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    {μ : Ω → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω) (hμ1 : ∑ ω, μ ω = 1) (f : Ω → β) (g : Ω → γ) :
    0 ≤ mutualInfoMap μ f g := by
  rw [mutualInfoMap_eq]
  linarith [entropyMap_prod_le hμ0 hμ1 f g]

/-- **Subadditivity of the Shannon entropy for `n` random variables**: for random variables
`X₀, …, X_{n-1}` on a finite probability space with weight `μ`, the joint entropy is at most the
sum of the individual entropies,

`H(X₀, …, X_{n-1}) ≤ ∑ᵢ H(Xᵢ)`.

This is the `n`-fold generalization of the two-variable subadditivity `Real.entropyMap_prod_le`,
proved by induction on `n`: the inductive step peels off `X₀` through `Fin.consEquiv` (leaving the
joint entropy unchanged, `Real.entropy_law_congr_equiv`) and applies the two-variable bound. It is
the entropy single-letterization underlying the converse of Shannon's noisy channel coding theorem
(N&C Theorem 12.7). -/
theorem entropyMap_pi_le {α : Type*} [Fintype α] [DecidableEq α]
    {μ : Ω → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω) (hμ1 : ∑ ω, μ ω = 1) :
    ∀ {n : ℕ} (X : Fin n → Ω → α),
      entropyMap μ (fun ω => fun i => X i ω) ≤ ∑ i, entropyMap μ (X i) := by
  intro n
  induction n with
  | zero =>
      intro X
      have hconst : (fun ω => fun i : Fin 0 => X i ω) = fun _ : Ω => (default : Fin 0 → α) := by
        funext ω; exact Subsingleton.elim _ _
      have hz : entropyMap μ (fun ω => fun i : Fin 0 => X i ω) = 0 := by
        rw [hconst, entropyMap_const μ hμ1]
      exact le_of_eq (hz.trans (Fin.sum_univ_zero _).symm)
  | succ n ih =>
      intro X
      -- Peel off `X₀`: the tuple `(fun i ↦ Xᵢ)` is `Fin.consEquiv (X₀, (fun i ↦ X_{i+1}))`.
      have hfun : (fun ω => fun i : Fin (n + 1) => X i ω)
          = (fun ω => (Fin.consEquiv (fun _ : Fin (n + 1) => α))
              (X 0 ω, fun i : Fin n => X i.succ ω)) := by
        funext ω; exact (Fin.cons_self_tail _).symm
      have key : entropyMap μ (fun ω => fun i : Fin (n + 1) => X i ω)
          = entropyMap μ (fun ω => (X 0 ω, fun i : Fin n => X i.succ ω)) := by
        rw [entropyMap_eq_entropy_law, entropyMap_eq_entropy_law, hfun]
        exact entropy_law_congr_equiv μ (Fin.consEquiv (fun _ : Fin (n + 1) => α))
          (fun ω => (X 0 ω, fun i : Fin n => X i.succ ω))
      rw [key]
      calc entropyMap μ (fun ω => (X 0 ω, fun i : Fin n => X i.succ ω))
          ≤ entropyMap μ (X 0) + entropyMap μ (fun ω => fun i : Fin n => X i.succ ω) :=
            entropyMap_prod_le hμ0 hμ1 _ _
        _ ≤ entropyMap μ (X 0) + ∑ i : Fin n, entropyMap μ (X i.succ) := by
            have := ih (fun i : Fin n => X i.succ); linarith
        _ = ∑ i : Fin (n + 1), entropyMap μ (X i) :=
            (Fin.sum_univ_succ (fun i => entropyMap μ (X i))).symm

/-! ### Coordinate subadditivity -/

/-- **Coordinate subadditivity of the Shannon entropy** (explicit-distribution form): for a
probability distribution `μ` on a finite product `Fin n → ι`, the entropy is at most the sum of the
entropies of its coordinate marginals `law μ (·ⱼ)`,

`H(Y₀, …, Y_{n-1}) ≤ ∑ⱼ H(Yⱼ)`.

This is the explicit-distribution reading of the random-variable subadditivity
`Real.entropyMap_pi_le`: apply it to the coordinate projections `Yⱼ = (·ⱼ)` on the sample space
`Fin n → ι` weighted by `μ`, whose own joint law is `μ` itself (`law μ id = μ`). It is the
output-entropy single-letterization step in the converse of Shannon's noisy channel coding theorem
(N&C Theorem 12.7): the entropy `H(Y₀, …, Y_{n-1})` of the `n`-use channel output is bounded by the
sum `∑ⱼ H(Yⱼ)` of the per-use output entropies. -/
theorem entropy_le_sum_entropy_proj {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    {μ : (Fin n → ι) → ℝ} (hμ0 : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) :
    entropy μ ≤ ∑ j, entropy (law μ (fun y => y j)) := by
  have key := entropyMap_pi_le hμ0 hμ1 (fun (j : Fin n) (y : Fin n → ι) => y j)
  simp only [entropyMap_eq_entropy_law] at key
  -- The joint law of the coordinate projections is `μ` itself (`law μ id = μ`).
  have hlaw : law μ (fun y : Fin n → ι => fun i => y i) = μ := law_id μ
  rwa [hlaw] at key

end Real
