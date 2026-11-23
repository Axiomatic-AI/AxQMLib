/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.JointEntropy

/-!
# Chaining rule for conditional entropies (Nielsen & Chuang, Theorem 11.4)

Building on `Real.condEntropy` (`ToMathlib/Analysis/SpecialFunctions/JointEntropy.lean`), this file
proves the **chaining rule for conditional entropies**

`H(X₁, …, Xₙ | Y) = ∑ᵢ H(Xᵢ | Y, X₁, …, Xᵢ₋₁)`  (Nielsen & Chuang, *Quantum Computation and
Quantum Information*, Theorem 11.4, eq. (11.27)).

## Model

`Real.condEntropy` is defined on a *joint distribution* `p : ι × κ → ℝ` as `H(X | Y) = H(X, Y) −
H(Y)`. To speak of the many variables `X₁, …, Xₙ, Y` and their prefix marginals we model each as a
random variable on a common finite sample space `Ω` carrying a weight `μ : Ω → ℝ`, and feed the
resulting joint laws to `Real.condEntropy`:

* `Real.law μ X x = ∑_{ω : X ω = x} μ ω` is the **law** (push-forward distribution) of a random
  variable `X : Ω → γ`; it is the probability mass function of `X` when `μ` is a probability weight.
  The joint law of `(X, Y)` is `Real.law μ (fun ω ↦ (X ω, Y ω))`, whose entropy is the joint
  entropy `H(X, Y)`, and `Real.condEntropy` of it is `H(X | Y)`.

Modelling the variables this way makes every marginal appearing in the chaining rule a law of a
*sub-tuple*, so no ad-hoc coordinate projection is needed. The alphabets of `X₁, …, Xₙ` are taken to
be a common finite type `α` (without loss of generality: any finite family of finite alphabets
recodes injectively into a common one, leaving every joint/conditional entropy unchanged), and `Y`
has alphabet `β`. Entropy is measured in nats, as in `Real.entropy`. No normalisation of `μ` is
assumed — the identity is a purely algebraic telescoping that holds for any weight and specialises
to a probability weight. The `n` variables are supplied as an infinite sequence `X : ℕ → Ω → α`, of
which only the first `n` enter the identity; this keeps the prefix `X₀, …, X_{k-1}` free of index
casts.

## Main results

* `Real.condEntropy_law_chain` — the chaining rule (11.27) for a sequence of random variables.

## Implementation notes

The proof telescopes the joint entropies `G k = H(Y, X₀, …, X_{k-1})` of the prefixes. Two
ingredients support it: `Real.entropy_law_congr_equiv` (the entropy of a law is invariant under a
bijective relabeling of the value alphabet — used to reorder the variables inside a tuple) and
`Real.marginalSnd_law_prod` (the second marginal of a joint law is the law of the second variable),
which turns each `Real.condEntropy` into a difference of prefix joint entropies. The `i`-th summand
becomes `G (i+1) − G i`, and `∑ᵢ (G (i+1) − G i) = G n − G 0` is the head conditional entropy.
-/

@[expose] public section

namespace Real

variable {Ω : Type*} [Fintype Ω]

/-! ### The law of a random variable -/

/-- The **law** (push-forward distribution) `law μ X x = ∑_{ω : X ω = x} μ ω` of a random variable
`X : Ω → γ` under the weight `μ : Ω → ℝ`. When `μ` is a probability weight this is the probability
mass function of `X`; the definition makes sense for any real weight. -/
noncomputable def law {γ : Type*} [DecidableEq γ] (μ : Ω → ℝ) (X : Ω → γ) : γ → ℝ :=
  fun x ↦ ∑ ω, if X ω = x then μ ω else 0

/-- The entropy of a law is invariant under a bijective relabeling `e` of the value alphabet:
`H(law μ (e ∘ X)) = H(law μ X)`. Reordering the components of a tuple-valued random variable is such
a relabeling, so its joint entropy is unchanged. -/
theorem entropy_law_congr_equiv {γ γ' : Type*} [Fintype γ] [DecidableEq γ] [Fintype γ']
    [DecidableEq γ'] (μ : Ω → ℝ) (e : γ ≃ γ') (X : Ω → γ) :
    entropy (law μ (fun ω ↦ e (X ω))) = entropy (law μ X) := by
  have hlaw : law μ (fun ω ↦ e (X ω)) = fun x' ↦ law μ X (e.symm x') := by
    funext x'
    simp only [law]
    exact Finset.sum_congr rfl fun ω _ ↦ if_congr e.eq_symm_apply.symm rfl rfl
  rw [hlaw]
  simp only [entropy_eq]
  exact Equiv.sum_comp e.symm fun x ↦ (law μ X x).negMulLog

/-- The second marginal of the joint law of `(X, Y)` is the law of `Y`:
`marginalSnd (law μ (X, Y)) = law μ Y`. Hence `condEntropy (law μ (X, Y)) = H(X, Y) − H(Y)`. -/
theorem marginalSnd_law_prod {ζ γ : Type*} [Fintype ζ] [DecidableEq ζ] [DecidableEq γ]
    (μ : Ω → ℝ) (X : Ω → ζ) (Y : Ω → γ) :
    marginalSnd (law μ (fun ω ↦ (X ω, Y ω))) = law μ Y := by
  funext y
  rw [marginalSnd_apply]
  simp only [law]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  have hfac : ∀ x, (if (X ω, Y ω) = (x, y) then μ ω else 0)
      = if X ω = x then (if Y ω = y then μ ω else 0) else 0 := fun x ↦ by
    by_cases hx : X ω = x <;> by_cases hy : Y ω = y <;> simp [Prod.ext_iff, hx, hy]
  rw [Finset.sum_congr rfl fun x _ ↦ hfac x, Finset.sum_ite_eq]
  simp

/-! ### Reshaping equivalences -/

/-- Peeling the last `X`-component out of the prefix bundle:
`α × (β × (Fin i → α)) ≃ β × (Fin (i+1) → α)`, sending `(x, (y, p))` to `(y, Fin.snoc p x)`. This is
the relabeling that turns the tuple `(Xᵢ, (Y, X₀, …, Xᵢ₋₁))` into `(Y, X₀, …, Xᵢ)`. -/
def prodSnocEquiv (α β : Type*) (i : ℕ) : α × (β × (Fin i → α)) ≃ β × (Fin (i + 1) → α) where
  toFun := fun p ↦ (p.2.1, Fin.snoc (α := fun _ ↦ α) p.2.2 p.1)
  invFun := fun q ↦ (q.2 (Fin.last i), (q.1, Fin.init q.2))
  left_inv := by rintro ⟨x, y, p⟩; simp [Fin.snoc_last, Fin.init_snoc]
  right_inv := by rintro ⟨y, q⟩; simp [Fin.snoc_init_self]

omit [Fintype Ω] in
/-- The first `i+1` random variables assemble, via `Fin.snoc`, from the first `i` and the `i`-th:
`Fin.snoc (fun j : Fin i ↦ X j ω) (X i ω) = fun j : Fin (i+1) ↦ X j ω`. -/
theorem snoc_prefix {α : Type*} (X : ℕ → Ω → α) (i : ℕ) (ω : Ω) :
    Fin.snoc (α := fun _ ↦ α) (fun j : Fin i ↦ X j ω) (X i ω) = fun j : Fin (i + 1) ↦ X j ω := by
  funext j
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · simp [Fin.snoc_last]
  · simp [Fin.snoc_castSucc]

/-- Telescoping of a difference over `Fin m`: `∑ i, (H (i+1) − H i) = H m − H 0`. The `Fin`-indexed
form of `Finset.sum_range_sub`. -/
theorem sum_fin_sub_telescope (H : ℕ → ℝ) (m : ℕ) :
    ∑ i : Fin m, (H (↑i + 1) - H ↑i) = H m - H 0 :=
  (Fin.sum_univ_eq_sum_range (fun i ↦ H (i + 1) - H i) m).trans (Finset.sum_range_sub H m)

/-! ### The chaining rule (Nielsen & Chuang, Theorem 11.4) -/

/-- **Chaining rule for conditional entropies** (Nielsen & Chuang, Theorem 11.4, eq. (11.27)): for
random variables `X₀, X₁, …` (a sequence, of which only the first `n` enter) and `Y` on a finite
sample space `Ω` with weight `μ`, valued in common finite alphabets,
`H(X₀, …, X_{n-1} | Y) = ∑ᵢ H(Xᵢ | Y, X₀, …, Xᵢ₋₁)`. Each entropy is `Real.condEntropy` of the
appropriate joint law; the identity holds for any weight `μ` (no normalisation needed). -/
theorem condEntropy_law_chain {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : Ω → ℝ) (X : ℕ → Ω → α) (Y : Ω → β) (n : ℕ) :
    condEntropy (law μ fun ω ↦ (fun i : Fin n ↦ X i ω, Y ω))
      = ∑ i : Fin n,
          condEntropy (law μ fun ω ↦ (X i ω, (Y ω, fun j : Fin (i : ℕ) ↦ X j ω))) := by
  -- `G k` is the joint entropy `H(Y, X₀, …, X_{k-1})`.
  set G : ℕ → ℝ := fun k ↦ entropy (law μ fun ω ↦ (Y ω, fun j : Fin k ↦ X j ω)) with hG
  -- Each summand telescopes: `H(Xᵢ | Y, X₀, …, Xᵢ₋₁) = G (i+1) − G i`.
  have hterm : ∀ i : Fin n,
      condEntropy (law μ fun ω ↦ (X i ω, (Y ω, fun j : Fin (i : ℕ) ↦ X j ω)))
        = G ((i : ℕ) + 1) - G (i : ℕ) := by
    intro i
    -- The joint entropy `H(Xᵢ, (Y, prefix)) = G (i+1)`, by reordering into `(Y, prefix ⧺ Xᵢ)`.
    have hA : entropy (law μ fun ω ↦ (X i ω, (Y ω, fun j : Fin (i : ℕ) ↦ X j ω)))
        = G ((i : ℕ) + 1) := by
      simp only [hG]
      have hfun :
          (fun ω ↦ prodSnocEquiv α β (i : ℕ) (X i ω, (Y ω, fun j : Fin (i : ℕ) ↦ X j ω)))
            = (fun ω ↦ (Y ω, fun j : Fin ((i : ℕ) + 1) ↦ X j ω)) := by
        funext ω
        change (Y ω, Fin.snoc (α := fun _ ↦ α) (fun j : Fin (i : ℕ) ↦ X j ω) (X i ω))
            = (Y ω, fun j : Fin ((i : ℕ) + 1) ↦ X j ω)
        rw [snoc_prefix]
      rw [← entropy_law_congr_equiv μ (prodSnocEquiv α β (i : ℕ))
        (fun ω ↦ (X i ω, (Y ω, fun j : Fin (i : ℕ) ↦ X j ω))), hfun]
    -- The conditioning-bundle entropy `H(Y, prefix) = G i`, definitionally.
    have hB : entropy (law μ fun ω ↦ (Y ω, fun j : Fin (i : ℕ) ↦ X j ω)) = G (i : ℕ) := by
      simp only [hG]
    rw [condEntropy_eq,
      marginalSnd_law_prod μ (fun ω ↦ X i ω) (fun ω ↦ (Y ω, fun j : Fin (i : ℕ) ↦ X j ω)),
      hA, hB]
  -- The head conditional entropy is `G n − G 0`.
  have hLHS : condEntropy (law μ fun ω ↦ (fun i : Fin n ↦ X i ω, Y ω)) = G n - G 0 := by
    -- `H((X₀,…,X_{n-1}), Y) = G n`, by the product swap.
    have hAn : entropy (law μ fun ω ↦ (fun i : Fin n ↦ X i ω, Y ω)) = G n := by
      simp only [hG]
      exact (entropy_law_congr_equiv μ (Equiv.prodComm (Fin n → α) β)
        (fun ω ↦ (fun i : Fin n ↦ X i ω, Y ω))).symm
    -- `H(Y) = G 0`, by collapsing the empty prefix (`Fin 0 → α` is `Unique`).
    have hA0 : entropy (law μ fun ω : Ω ↦ Y ω) = G 0 := by
      simp only [hG]
      exact entropy_law_congr_equiv μ (Equiv.prodUnique β (Fin 0 → α))
        (fun ω ↦ (Y ω, fun j : Fin 0 ↦ X j ω))
    rw [condEntropy_eq,
      marginalSnd_law_prod μ (fun ω ↦ (fun i : Fin n ↦ X i ω)) (fun ω ↦ Y ω), hAn, hA0]
  rw [hLHS, Finset.sum_congr rfl fun i _ ↦ hterm i, sum_fin_sub_telescope G n]

end Real
