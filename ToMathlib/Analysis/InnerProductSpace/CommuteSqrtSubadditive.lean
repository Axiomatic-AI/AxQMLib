/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFC
public import ToMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Subadditivity of the operator square root on a commuting family

The operator square root is **not** subadditive in general: `√(A + B) ≤ √A + √B` *fails* for
positive operators `A, B` on a Hilbert space (the anticommutator `√A √B + √B √A` need not be
positive, so `(√A + √B)² = A + B + (√A √B + √B √A)` need not dominate `A + B`; a `2 × 2` witness is
two rank-one projections at `45°`). But when the operators **commute** the obstruction vanishes and
the classical scalar subadditivity `√(a + b) ≤ √a + √b` lifts verbatim:

`√(A + B) ≤ √A + √B`   (for `0 ≤ A`, `0 ≤ B`, `Commute A B`),

and, by induction, `√(∑ⱼ Aⱼ) ≤ ∑ⱼ √Aⱼ` for a pairwise-commuting family of positive operators.

The proof is the operator form of the scalar argument. With `R = √A + √B ≥ 0`: `√A, √B` commute
(`IsSelfAdjoint.commute_cfc`), so `R² = A + B + 2•(√A √B)` and `√A √B ≥ 0` (`Commute.mul_nonneg`),
whence `A + B ≤ R²`; operator-monotonicity of the square root (`CFC.sqrt_le_sqrt`) then gives
`√(A + B) ≤ √(R²) = R` (`ContinuousLinearMap.cfc_real_sqrt_mul_self_eq_self_of_nonneg`).

The square roots here are `cfc Real.sqrt`, matching the operator-square-root API
(`ToMathlib.Analysis.InnerProductSpace.CFC`); the bridge to `CFC.sqrt` (used only for its
monotonicity) is `CFC.sqrt_eq_real_sqrt`.

This is the operator ingredient behind the *commuting-family* case of the pretty-good discrimination
paired-trace bound (`State.pairedTraceBound_of_commute`, Nielsen & Chuang Problem 5.5): a commuting
family of density operators — e.g. the coset reduced states of an *abelian* hidden-subgroup
instance, simultaneously diagonal in the character basis — satisfies the paired-trace inequality
unconditionally.
-/

@[expose] public section

open scoped ComplexOrder

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Operator-monotonicity of `cfc Real.sqrt`** on nonnegative operators: `A ≤ B` (with `0 ≤ A`)
implies `√A ≤ √B`, where `√· = cfc Real.sqrt ·`.  This is the `cfc Real.sqrt`-facing restatement of
the C\*-algebra square-root monotonicity `CFC.sqrt_le_sqrt`, bridged through
`CFC.sqrt_eq_real_sqrt`. -/
theorem cfc_real_sqrt_le_cfc_real_sqrt {A B : E →L[ℂ] E} (hA : 0 ≤ A) (h : A ≤ B) :
    cfc Real.sqrt A ≤ cfc Real.sqrt B := by
  have hB : 0 ≤ B := hA.trans h
  have eA : CFC.sqrt A = cfc Real.sqrt A := by rw [CFC.sqrt_eq_real_sqrt A, cfcₙ_eq_cfc]
  have eB : CFC.sqrt B = cfc Real.sqrt B := by rw [CFC.sqrt_eq_real_sqrt B, cfcₙ_eq_cfc]
  rw [← eA, ← eB]
  exact CFC.sqrt_le_sqrt A B h

/-- **Subadditivity of the operator square root for two commuting positive operators**:
`√(A + B) ≤ √A + √B` when `0 ≤ A`, `0 ≤ B` and `Commute A B` (`√· = cfc Real.sqrt ·`).

The commutativity is essential — the inequality is *false* for general positive `A, B`.  With
`R = √A + √B`, commutativity makes `√A √B` positive (`Commute.mul_nonneg`), so
`R² = A + B + 2•(√A √B) ≥ A + B`; the square root is operator-monotone, and `√(R²) = R`. -/
theorem cfc_real_sqrt_add_le_of_commute {A B : E →L[ℂ] E} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : Commute A B) : cfc Real.sqrt (A + B) ≤ cfc Real.sqrt A + cfc Real.sqrt B := by
  set p := cfc Real.sqrt A with hp
  set q := cfc Real.sqrt B with hq
  have hpnn : 0 ≤ p := cfc_real_sqrt_nonneg A
  have hqnn : 0 ≤ q := cfc_real_sqrt_nonneg B
  -- `√A` and `√B` commute since `A` and `B` do.
  have hpq : Commute p q := by
    have h1 : Commute p B := IsSelfAdjoint.commute_cfc hA.isSelfAdjoint hc Real.sqrt
    exact (IsSelfAdjoint.commute_cfc hB.isSelfAdjoint h1.symm Real.sqrt).symm
  have hpq_nn : 0 ≤ p * q := hpq.mul_nonneg hpnn hqnn
  have hpp : p * p = A := cfc_real_sqrt_mul_self_of_nonneg hA
  have hqq : q * q = B := cfc_real_sqrt_mul_self_of_nonneg hB
  have hRnn : 0 ≤ p + q := add_nonneg hpnn hqnn
  have hRR : (p + q) * (p + q) = (A + B) + 2 • (p * q) := by
    have hexp : (p + q) * (p + q) = p * p + q * q + (p * q + q * p) := by noncomm_ring
    rw [hexp, hpp, hqq, hpq.eq]; module
  have hle : (A + B) ≤ (p + q) * (p + q) := by
    rw [hRR]; exact le_add_of_nonneg_right (by positivity)
  calc cfc Real.sqrt (A + B) ≤ cfc Real.sqrt ((p + q) * (p + q)) :=
        cfc_real_sqrt_le_cfc_real_sqrt (add_nonneg hA hB) hle
    _ = p + q := cfc_real_sqrt_mul_self_eq_self_of_nonneg hRnn

/-- **Subadditivity of the operator square root over a pairwise-commuting family**:
`√(∑ᵢ Aᵢ) ≤ ∑ᵢ √Aᵢ` for a finite family of positive operators that pairwise commute
(`√· = cfc Real.sqrt ·`).  Proved by induction on the finset from the two-operator case
`cfc_real_sqrt_add_le_of_commute` (each new summand commutes with the running partial sum, by
`Commute.sum_right`). -/
theorem cfc_real_sqrt_sum_le_of_commute {ι : Type*} (s : Finset ι) (A : ι → E →L[ℂ] E)
    (hA : ∀ i, 0 ≤ A i) (hc : ∀ i j, Commute (A i) (A j)) :
    cfc Real.sqrt (∑ i ∈ s, A i) ≤ ∑ i ∈ s, cfc Real.sqrt (A i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hcomm : Commute (A a) (∑ i ∈ s, A i) :=
      Commute.sum_right s A (A a) (fun j _ => hc a j)
    calc cfc Real.sqrt (A a + ∑ i ∈ s, A i)
        ≤ cfc Real.sqrt (A a) + cfc Real.sqrt (∑ i ∈ s, A i) :=
          cfc_real_sqrt_add_le_of_commute (hA a) (Finset.sum_nonneg fun i _ => hA i) hcomm
      _ ≤ cfc Real.sqrt (A a) + ∑ i ∈ s, cfc Real.sqrt (A i) := by gcongr

end ContinuousLinearMap
