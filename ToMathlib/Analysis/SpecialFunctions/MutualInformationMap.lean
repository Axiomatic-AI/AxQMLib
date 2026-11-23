/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.ConditionalEntropy

/-!
# Mutual information of random variables, and a superadditivity counterexample

For a finite sample space `Ω` with a discrete distribution `p : Ω → ℝ` and two *random variables*
`f : Ω → β`, `g : Ω → γ` into finite types, the **mutual information** of `f` and `g` is

`Real.mutualInfoMap p f g := Real.entropyMap p f + Real.entropyMap p g − Real.entropyMap p (f, g)`,

i.e. `H(f : g) = H(f) + H(g) − H(f, g)`, defined through the laws of `f`, `g`, and the tuple
`(f, g)` (all via `Real.entropyMap`, the entropy of a pushforward law). This is the
random-variable sibling of `Real.mutualInfo` (which acts on a joint distribution on a product
type), built on the same `Ω`-based development as `Real.condEntropyMap`; modelling the entropies
through a shared sample space makes the joint entropy of any tuple of variables free — exactly what
the counterexample below needs.

## Main declarations

* `Real.mutualInfoMap` — `H(f : g)`, the mutual information of two random variables.
* `Real.exists_mutualInfo_not_superadditive_counterexample` and
  `Real.not_forall_mutualInfo_superadditive` — an **explicit example** and its packaging as a
  refutation, showing that the mutual information is **not** always superadditive (Nielsen &
  Chuang, *Quantum Computation and Quantum Information*, Exercise 11.9).

## The counterexample (N&C Exercise 11.9)

For a fair bit `X₁` and `X₂ = Y₁ = Y₂ = X₁`, mutual information fails to be superadditive:
`H(X₁ : Y₁) + H(X₂ : Y₂) ⩽̸ H(X₁, X₂ : Y₁, Y₂)`.

The witness is the fair bit `Ω = Fin 2` (uniform `p ≡ 1/2`) with all four variables the identity,
so `X₂ = Y₁ = Y₂ = X₁ = x`. Every quantity in sight is the entropy of an *injective* function of
the bit `x` (`x`, the pair `(x, x)`, the quadruple `((x, x), (x, x))`), hence equals `H(x) = log 2`
by `Real.entropyMap_of_injective`. Therefore

* `H(X₁ : Y₁) = H(x) + H(x) − H(x, x) = log 2`, and likewise `H(X₂ : Y₂) = log 2`, so the left-hand
  side is `2 log 2`;
* `H(X₁, X₂ : Y₁, Y₂) = H(x, x) + H(x, x) − H((x, x), (x, x)) = log 2` is the right-hand side.

The gap `2 log 2 − log 2 = log 2 > 0` is a full bit: superadditivity fails. (Contrast N&C Exercise
11.8, where mutual information fails to be *sub*additive.)

## Design

This is pure classical information theory — it quantifies over functions `p : Ω → ℝ` and
`f : Ω → β`, building on the `Real.entropyMap` development. The statement of Exercise 11.9 is in
`AxQM/NC/Ch11/Exercise11_9.lean`.

N&C measure entropy in *bits* (base-2 logarithm); the library measures it in *nats* (natural
logarithm). The failure is a strict inequality whose gap is `log b 2 > 0` in any base `b > 1`, so
it is base-independent: a faithful reformulation, not a weakening.
-/

@[expose] public section

namespace Real

variable {Ω β γ : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- The **mutual information** `H(f : g) = H(f) + H(g) − H(f, g)` of two random variables
`f : Ω → β`, `g : Ω → γ` on a common finite sample space with distribution `p : Ω → ℝ`, defined
through the laws of `f`, `g`, and the tuple `(f, g)` (all via `Real.entropyMap`). -/
noncomputable def mutualInfoMap (p : Ω → ℝ) (f : Ω → β) (g : Ω → γ) : ℝ :=
  entropyMap p f + entropyMap p g - entropyMap p (fun ω => (f ω, g ω))

/-- Unfolding lemma for `mutualInfoMap`: `H(f : g) = H(f) + H(g) − H(f, g)`, through the laws of
`f`, `g`, and the joint law of the tuple `(f, g)`. -/
theorem mutualInfoMap_eq (p : Ω → ℝ) (f : Ω → β) (g : Ω → γ) :
    mutualInfoMap p f g = entropyMap p f + entropyMap p g - entropyMap p (fun ω => (f ω, g ω)) :=
  rfl

/-- **Explicit counterexample to superadditivity of the mutual information** (Nielsen & Chuang,
*Quantum Computation and Quantum Information*, Exercise 11.9).

There exist a finite probability space and random variables `X₁, X₂, Y₁, Y₂` realising the
copied-variable configuration `X₂ ≡ Y₁ ≡ Y₂ ≡ X₁` of the exercise, for which

`H(X₁ : Y₁) + H(X₂ : Y₂) > H(X₁, X₂ : Y₁, Y₂)`,

so the inequality `H(X₁ : Y₁) + H(X₂ : Y₂) ≤ H(X₁, X₂ : Y₁, Y₂)` — superadditivity of the mutual
information (N&C eq. (11.35)) — does **not** hold. The witness is the fair bit `Ω = Fin 2` (uniform
`p ≡ 1/2`) with all four variables the identity: each mutual information equals `log 2`, so the
left-hand side is `2 log 2` and the right-hand side is `log 2`, a gap of a full bit. -/
theorem exists_mutualInfo_not_superadditive_counterexample :
    ∃ (Ω : Type) (_ : Fintype Ω) (_ : DecidableEq Ω) (p : Ω → ℝ) (X₁ X₂ Y₁ Y₂ : Ω → Fin 2),
      (∀ ω, 0 ≤ p ω) ∧ (∑ ω, p ω = 1) ∧ X₂ = X₁ ∧ Y₁ = X₁ ∧ Y₂ = X₁ ∧
      mutualInfoMap p X₁ Y₁ + mutualInfoMap p X₂ Y₂ >
        mutualInfoMap p (fun ω => (X₁ ω, X₂ ω)) (fun ω => (Y₁ ω, Y₂ ω)) := by
  refine ⟨Fin 2, inferInstance, inferInstance, fun _ => (2 : ℝ)⁻¹, id, id, id, id,
    fun _ => by norm_num, by rw [Fin.sum_univ_two]; norm_num, rfl, rfl, rfl, ?_⟩
  have hEp : entropy (fun _ : Fin 2 => (2 : ℝ)⁻¹) = Real.log 2 := by
    have h := entropy_uniform (ι := Fin 2)
    simpa [Fintype.card_fin] using h
  -- Every entropy in sight is the entropy of an injective function of the fair bit, hence `log 2`.
  have e_id : entropyMap (fun _ : Fin 2 => (2 : ℝ)⁻¹) (id : Fin 2 → Fin 2) = Real.log 2 := by
    rw [entropyMap_of_injective Function.injective_id]; exact hEp
  have e_dup : entropyMap (fun _ : Fin 2 => (2 : ℝ)⁻¹) (fun ω : Fin 2 => (ω, ω)) = Real.log 2 := by
    rw [entropyMap_of_injective (f := fun ω : Fin 2 => (ω, ω)) (fun _ _ h => congrArg Prod.fst h)]
    exact hEp
  have e_quad : entropyMap (fun _ : Fin 2 => (2 : ℝ)⁻¹)
      (fun ω : Fin 2 => ((ω, ω), (ω, ω))) = Real.log 2 := by
    rw [entropyMap_of_injective (f := fun ω : Fin 2 => ((ω, ω), (ω, ω)))
      (fun _ _ h => congrArg Prod.fst (congrArg Prod.fst h))]
    exact hEp
  simp only [mutualInfoMap_eq, id_eq]
  linarith [e_id, e_dup, e_quad, Real.log_pos (show (1 : ℝ) < 2 by norm_num)]

/-- **Superadditivity of the mutual information is not a theorem** (Nielsen & Chuang, Exercise
11.9): it is *not* the case that for all finite random variables `X₁, X₂, Y₁, Y₂` on a finite
probability space,
`H(X₁ : Y₁) + H(X₂ : Y₂) ≤ H(X₁, X₂ : Y₁, Y₂)`.
This is the negation packaging of
`exists_mutualInfo_not_superadditive_counterexample`. -/
theorem not_forall_mutualInfo_superadditive :
    ¬ ∀ (Ω αX₁ αX₂ αY₁ αY₂ : Type) [Fintype Ω] [DecidableEq Ω]
        [Fintype αX₁] [DecidableEq αX₁] [Fintype αX₂] [DecidableEq αX₂]
        [Fintype αY₁] [DecidableEq αY₁] [Fintype αY₂] [DecidableEq αY₂]
        (p : Ω → ℝ) (X₁ : Ω → αX₁) (X₂ : Ω → αX₂) (Y₁ : Ω → αY₁) (Y₂ : Ω → αY₂),
        (∀ ω, 0 ≤ p ω) → ∑ ω, p ω = 1 →
        mutualInfoMap p X₁ Y₁ + mutualInfoMap p X₂ Y₂ ≤
          mutualInfoMap p (fun ω => (X₁ ω, X₂ ω)) (fun ω => (Y₁ ω, Y₂ ω)) := by
  intro h
  obtain ⟨Ω, _, _, p, X₁, X₂, Y₁, Y₂, hnn, hsum, _, _, _, hgap⟩ :=
    exists_mutualInfo_not_superadditive_counterexample
  exact absurd (h Ω (Fin 2) (Fin 2) (Fin 2) (Fin 2) p X₁ X₂ Y₁ Y₂ hnn hsum) (not_le.mpr hgap)

end Real
