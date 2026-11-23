/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Conditional Shannon entropy of random variables, and a strong-subadditivity counterexample

For a finite sample space `Ω` with a discrete distribution `p : Ω → ℝ` and a *random variable*
`f : Ω → β` into a finite type, the **entropy of the law of `f`** is the Shannon entropy of the
pushed-forward distribution `b ↦ ∑_{ω : f ω = b} p ω`:

`Real.entropyMap p f := Real.entropy (fun b ↦ ∑ ω, if f ω = b then p ω else 0)`.

This is `H(f)` — the Shannon entropy of the random variable `f` — built directly on top of
`Real.entropy` (in nats). The **conditional entropy** of `f` given `g` is then the usual
difference of joint and marginal entropies,

`Real.condEntropyMap p f g := Real.entropyMap p (fun ω ↦ (f ω, g ω)) - Real.entropyMap p g`,

i.e. `H(f | g) = H(f, g) − H(g)`. Modelling the entropies through the shared sample space `Ω`
makes joint entropies of arbitrary tuples of random variables free (just tuple the variables),
which is exactly what the strong-subadditivity discussion below needs.

## Main declarations

* `Real.entropyMap` — `H(f)`, the Shannon entropy of the law of a random variable `f`.
* `Real.entropyMap_of_injective` — if `f` is injective then `H(f) = H(p)` (relabelling the
  outcomes does not change the entropy: the fibres are singletons).
* `Real.entropyMap_const` — `H(f) = 0` for a constant random variable (a point mass has zero
  entropy), given that `p` is a probability distribution.
* `Real.condEntropyMap` — `H(f | g) = H(f, g) − H(g)`.
* `Real.exists_conditional_strong_subadditivity_counterexample` and
  `Real.not_forall_conditional_strong_subadditivity` — an **explicit example** and its packaging
  as a refutation, showing that the classical conditional-entropy inequality
  `H(D | A, B, C) + H(D | B) ≤ H(D | A, B) + H(D | B, C)` can **fail** (Nielsen & Chuang,
  *Quantum Computation and Quantum Information*, Problem 11.4(2)).

## The counterexample (N&C Problem 11.4(2))

Problem 11.4 contrasts two "conditional forms of strong subadditivity". The quantum form,
`S(A, B, C | D) + S(B | D) ≤ S(A, B | D) + S(B, C | D)`, holds — it is strong subadditivity with
the middle system enlarged to `B ⊗ D`. The classical statement obtained by **conditioning `D` on
the other variables**, `H(D | A, B, C) + H(D | B) ≤ H(D | A, B) + H(D | B, C)`, is a *different*
inequality (the conditioning is reversed), and it is **not** always true.

The explicit example proving the failure: take `Ω = Fin 2` a fair bit `x` with the uniform
distribution `p ≡ 1/2`, let `A = C = D = x` (three copies of the bit) and let `B` be trivial
(constant). Then `D` is a common cause of `A` and `C`, so `A` and `C` are conditionally
independent given `D` but perfectly correlated marginally. Computing (all joint entropies are
either `log 2`, from an injective tuple, or `0`, from a constant), `H(D | A, B, C) = 0`,
`H(D | B) = log 2`, `H(D | A, B) = 0`, `H(D | B, C) = 0`, so the left-hand side is `log 2 > 0`
while the right-hand side is `0`: the inequality fails by a full bit.

## Design

This is pure classical information theory: it quantifies over functions `p : Ω → ℝ` and
`f : Ω → β`, building on the `Real.entropy` development. The statement of Problem 11.4 is in
`AxQM/NC/Ch11/Problem11_4.lean`.

The random-variable (`Ω → β`) formulation is chosen deliberately: it makes the joint entropies of
the many different variable-subsets appearing in the strong-subadditivity inequality available
uniformly, without a bespoke marginalisation operator over product distributions.
-/

@[expose] public section

namespace Real

variable {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]

/-- The Shannon entropy (in nats) of the *law* of a random variable `f : Ω → β` under the
distribution `p : Ω → ℝ`: the entropy of the pushforward distribution
`b ↦ ∑_{ω : f ω = b} p ω`. Writing `H(f)` for this quantity, `entropyMap p f = H(f)`. -/
noncomputable def entropyMap (p : Ω → ℝ) (f : Ω → β) : ℝ :=
  entropy (fun b => ∑ ω, if f ω = b then p ω else 0)

/-- Unfolding lemma for `entropyMap`: the entropy of the law of `f` is the Shannon entropy of the
pushforward distribution `b ↦ ∑_{ω : f ω = b} p ω`. -/
theorem entropyMap_eq (p : Ω → ℝ) (f : Ω → β) :
    entropyMap p f = entropy (fun b => ∑ ω, if f ω = b then p ω else 0) := rfl

/-- The entropy of the law of an **injective** random variable equals the entropy of the
underlying distribution: `H(f) = H(p)` when `f` is injective. Relabelling the outcomes by an
injection sends `p ω` to the value at `f ω` and leaves every other outcome at mass `0`
(`negMulLog 0 = 0`), so the entropy is unchanged. -/
theorem entropyMap_of_injective {p : Ω → ℝ} {f : Ω → β} (hf : Function.Injective f) :
    entropyMap p f = entropy p := by
  classical
  rw [entropyMap_eq, entropy_eq, entropy_eq]
  have hq : ∀ ω, (∑ ω', if f ω' = f ω then p ω' else 0) = p ω := by
    intro ω
    rw [Finset.sum_eq_single ω]
    · simp
    · intro ω' _ hne; rw [ite_eq_right (fun h => hne (hf h))]
    · simp
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.image f Finset.univ)) ?vanish]
  · rw [Finset.sum_image (fun x _ y _ h => hf h)]
    exact Finset.sum_congr rfl (fun ω _ => by rw [hq])
  case vanish =>
    intro b _ hb
    have hz : (∑ ω', if f ω' = b then p ω' else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro ω' _
      rw [ite_eq_right]
      intro h
      exact hb (h ▸ Finset.mem_image_of_mem f (Finset.mem_univ ω'))
    rw [hz, negMulLog_zero]

/-- The entropy of the law of a **constant** random variable is `0`: a point mass carries no
information. Requires `p` to be a probability distribution (`∑ ω, p ω = 1`), so that the
pushforward is the point mass at `c`. -/
theorem entropyMap_const (p : Ω → ℝ) (hp : ∑ ω, p ω = 1) (c : β) :
    entropyMap p (fun _ => c) = 0 := by
  rw [entropyMap_eq, entropy_eq]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  rcases eq_or_ne c b with h | h <;> simp [h, hp, negMulLog_one, negMulLog_zero]

/-- The **conditional Shannon entropy** of a random variable `f` given a random variable `g`,
`H(f | g) = H(f, g) − H(g)`, defined through the joint law of the tuple `(f, g)` and the law of
`g`. -/
noncomputable def condEntropyMap {γ : Type*} [Fintype γ] [DecidableEq γ]
    (p : Ω → ℝ) (f : Ω → β) (g : Ω → γ) : ℝ :=
  entropyMap p (fun ω => (f ω, g ω)) - entropyMap p g

/-- Unfolding lemma for `condEntropyMap`: `H(f | g) = H(f, g) − H(g)`, through the joint law of
the tuple `(f, g)` and the law of `g`. -/
theorem condEntropyMap_eq {γ : Type*} [Fintype γ] [DecidableEq γ]
    (p : Ω → ℝ) (f : Ω → β) (g : Ω → γ) :
    condEntropyMap p f g = entropyMap p (fun ω => (f ω, g ω)) - entropyMap p g := rfl

/-- **Explicit counterexample to the classical conditional form of strong subadditivity**
(Nielsen & Chuang, *Quantum Computation and Quantum Information*, Problem 11.4(2)).

There exist a finite probability space and random variables `A, B, C, D` for which

`H(D | A, B, C) + H(D | B) > H(D | A, B) + H(D | B, C)`,

so the inequality `H(D | A, B, C) + H(D | B) ≤ H(D | A, B) + H(D | B, C)` — the classical
analogue obtained by conditioning `D` on the other variables — does **not** always hold. The
witness is the fair bit `Ω = Fin 2` (uniform `p ≡ 1/2`) with `A = C = D` the identity and `B`
trivial: the four conditional entropies are `0`, `log 2`, `0`, `0`, so the gap is `log 2 > 0`. -/
theorem exists_conditional_strong_subadditivity_counterexample :
    ∃ (Ω : Type) (_ : Fintype Ω) (_ : DecidableEq Ω) (p : Ω → ℝ) (A B C D : Ω → Fin 2),
      (∀ ω, 0 ≤ p ω) ∧ (∑ ω, p ω = 1) ∧
      condEntropyMap p D (fun ω => (A ω, B ω, C ω)) + condEntropyMap p D B >
        condEntropyMap p D (fun ω => (A ω, B ω)) + condEntropyMap p D (fun ω => (B ω, C ω)) := by
  refine ⟨Fin 2, inferInstance, inferInstance, fun _ => (2 : ℝ)⁻¹, id, fun _ => 0, id, id,
    fun _ => by norm_num, by rw [Fin.sum_univ_two]; norm_num, ?_⟩
  have hsum : ∑ _ω : Fin 2, (2 : ℝ)⁻¹ = 1 := by rw [Fin.sum_univ_two]; norm_num
  have hEp : entropy (fun _ : Fin 2 => (2 : ℝ)⁻¹) = Real.log 2 := by
    have h := entropy_uniform (ι := Fin 2)
    simpa [Fintype.card_fin] using h
  simp only [condEntropyMap_eq, id_eq]
  rw [entropyMap_of_injective (f := fun ω : Fin 2 => (ω, ω, (0 : Fin 2), ω))
        (fun _ _ h => congrArg Prod.fst h),
      entropyMap_of_injective (f := fun ω : Fin 2 => (ω, (0 : Fin 2), ω))
        (fun _ _ h => congrArg Prod.fst h),
      entropyMap_of_injective (f := fun ω : Fin 2 => (ω, (0 : Fin 2)))
        (fun _ _ h => congrArg Prod.fst h),
      entropyMap_of_injective (f := fun ω : Fin 2 => (ω, ω, (0 : Fin 2)))
        (fun _ _ h => congrArg Prod.fst h),
      entropyMap_of_injective (f := fun ω : Fin 2 => ((0 : Fin 2), ω))
        (fun _ _ h => congrArg Prod.snd h),
      entropyMap_const (fun _ : Fin 2 => (2 : ℝ)⁻¹) hsum (0 : Fin 2), hEp]
  linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]

/-- **The classical conditional form of strong subadditivity is not a theorem** (Nielsen &
Chuang, Problem 11.4(2)): it is *not* the case that for all finite random variables `A, B, C, D`
on a finite probability space,
`H(D | A, B, C) + H(D | B) ≤ H(D | A, B) + H(D | B, C)`.
This is the negation packaging of
`exists_conditional_strong_subadditivity_counterexample`; contrast with the quantum form
`S(A, B, C | D) + S(B | D) ≤ S(A, B | D) + S(B, C | D)`, which *does* hold. -/
theorem not_forall_conditional_strong_subadditivity :
    ¬ ∀ (Ω αA αB αC αD : Type) [Fintype Ω] [DecidableEq Ω] [Fintype αA] [DecidableEq αA]
        [Fintype αB] [DecidableEq αB] [Fintype αC] [DecidableEq αC] [Fintype αD] [DecidableEq αD]
        (p : Ω → ℝ) (A : Ω → αA) (B : Ω → αB) (C : Ω → αC) (D : Ω → αD),
        (∀ ω, 0 ≤ p ω) → ∑ ω, p ω = 1 →
        condEntropyMap p D (fun ω => (A ω, B ω, C ω)) + condEntropyMap p D B ≤
          condEntropyMap p D (fun ω => (A ω, B ω)) + condEntropyMap p D (fun ω => (B ω, C ω)) := by
  intro h
  obtain ⟨Ω, _, _, p, A, B, C, D, hnn, hsum, hgap⟩ :=
    exists_conditional_strong_subadditivity_counterexample
  exact absurd (h Ω (Fin 2) (Fin 2) (Fin 2) (Fin 2) p A B C D hnn hsum) (not_le.mpr hgap)

end Real
