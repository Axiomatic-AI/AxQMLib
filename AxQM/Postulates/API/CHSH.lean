/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Observable
import AxQM.Postulates.API.Qubit
import ToMathlib.Algebra.Star.CHSH

/-!
# AxQM.Postulates.API — CHSH operators of a bipartite system (Tsirelson)

Results assembling the **CHSH operators** on a composite system
`S ⊗ T` out of a pair of observables on each factor, and specialising the algebraic
Clauser–Horne–Shimony–Holt / Tsirelson machinery (`Mathlib.Algebra.Star.CHSH`) to them.
This is the operator-level core of Nielsen & Chuang **Problem 2.3** (Tsirelson's inequality);
the *physical* expectation bound (2.234) it feeds is stated in
`AxQM/NC/Ch2/Problem2_3.lean`.

* `isCHSHTuple_tmul` — the four embedded operators `A₀ ⊗ I, A₁ ⊗ I, I ⊗ B₀, I ⊗ B₁` of two
  involutive observable pairs form an `IsCHSHTuple`: self-adjoint involutions, with the
  `Aᵢ ⊗ I` commuting with the `I ⊗ Bⱼ` (they act on different factors).
* `chsh_tmul_sq` — **N&C (2.233)**, tensor form: for involutive observables the square of the
  CHSH operator `A₀⊗B₀ + A₀⊗B₁ + A₁⊗B₀ - A₁⊗B₁` is `4 + ⁅A₁, A₀⁆ ⊗ ⁅B₀, B₁⁆`, where the
  scalar `4` is `4·(identity) = 4I`. Under the dictionary below this is N&C's
  `(Q⊗S + R⊗S + R⊗T - Q⊗T)² = 4I + [Q,R]⊗[S,T]`.
* `PureState.expectation_chsh_tmul_le` — the **Tsirelson expectation bound**: for two-factor
  involutive observables and any pure state, the CHSH combination of expectations is `≤ 2√2`.
  Descends `tsirelson_inequality` through the operator-order → expectation bridge. Its
  qubit-Pauli instance `pauliObservable_chsh_expectation_le` is N&C **(2.234)**
  (`AxQM/NC/Ch2/Problem2_3.lean`).

## Design notes

The N&C ↦ CHSH-tuple dictionary is `A₀ = R, A₁ = Q, B₀ = S, B₁ = T`, under which the tuple
combination `A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` is N&C's `R⊗S + R⊗T + Q⊗S - Q⊗T`, equal (as a sum) to
`Q⊗S + R⊗S + R⊗T - Q⊗T`; and the commutator term `-⁅A₀,A₁⁆·⁅B₀,B₁⁆` from the squaring identity
is `⁅A₁,A₀⁆ ⊗ ⁅B₀,B₁⁆ = [Q,R] ⊗ [S,T]` (the two sign flips — one from `⁅A₁,A₀⁆ = -⁅A₀,A₁⁆`,
one absorbed into `mapL`).
-/

open scoped InnerProductSpace TensorProduct ComplexOrder

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **The two-factor Pauli-style CHSH tuple.** If `A₀, A₁` are involutive observables on `S`
and `B₀, B₁` involutive observables on `T` (`X.op * X.op = 1`, the ±1-valued condition), then
their embedded operators `A₀ ⊗ I, A₁ ⊗ I, I ⊗ B₀, I ⊗ B₁` form an `IsCHSHTuple`: each is a
self-adjoint involution, and each `Aᵢ ⊗ I` commutes with each `I ⊗ Bⱼ` because they act on
different tensor factors. This is the hypothesis-assembly step for `tsirelson_inequality`. -/
theorem isCHSHTuple_tmul (A₀ A₁ : Observable S) (B₀ B₁ : Observable T)
    (hA₀ : A₀.op * A₀.op = 1) (hA₁ : A₁.op * A₁.op = 1)
    (hB₀ : B₀.op * B₀.op = 1) (hB₁ : B₁.op * B₁.op = 1) :
    IsCHSHTuple (TensorProduct.mapL A₀.op 1) (TensorProduct.mapL A₁.op 1)
      (TensorProduct.mapL (1 : S →L[ℂ] S) B₀.op) (TensorProduct.mapL (1 : S →L[ℂ] S) B₁.op) where
  A₀_inv := by rw [sq, ← TensorProduct.mapL_mul, hA₀, mul_one, TensorProduct.mapL_one]
  A₁_inv := by rw [sq, ← TensorProduct.mapL_mul, hA₁, mul_one, TensorProduct.mapL_one]
  B₀_inv := by rw [sq, ← TensorProduct.mapL_mul, one_mul, hB₀, TensorProduct.mapL_one]
  B₁_inv := by rw [sq, ← TensorProduct.mapL_mul, one_mul, hB₁, TensorProduct.mapL_one]
  A₀_sa := IsSelfAdjoint.tensorMapL A₀.selfAdjoint (IsSelfAdjoint.one _)
  A₁_sa := IsSelfAdjoint.tensorMapL A₁.selfAdjoint (IsSelfAdjoint.one _)
  B₀_sa := IsSelfAdjoint.tensorMapL (IsSelfAdjoint.one _) B₀.selfAdjoint
  B₁_sa := IsSelfAdjoint.tensorMapL (IsSelfAdjoint.one _) B₁.selfAdjoint
  A₀B₀_commutes := by
    rw [← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul, mul_one, one_mul, one_mul, mul_one]
  A₀B₁_commutes := by
    rw [← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul, mul_one, one_mul, one_mul, mul_one]
  A₁B₀_commutes := by
    rw [← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul, mul_one, one_mul, one_mul, mul_one]
  A₁B₁_commutes := by
    rw [← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul, mul_one, one_mul, one_mul, mul_one]

/-- **Nielsen & Chuang (2.233), tensor form.** For involutive observables `A₀, A₁` on `S` and
`B₀, B₁` on `T`, the square of the CHSH operator is
`(A₀⊗B₀ + A₀⊗B₁ + A₁⊗B₀ - A₁⊗B₁)² = 4 + ⁅A₁,A₀⁆ ⊗ ⁅B₀,B₁⁆`, where the scalar `4` is the
`4·(identity)` of the operator algebra — the `4I` of the textbook.

Under the N&C dictionary `A₀=R, A₁=Q, B₀=S, B₁=T` this is exactly
`(Q⊗S + R⊗S + R⊗T - Q⊗T)² = 4I + [Q,R]⊗[S,T]`; the two-qubit Pauli case is the instance where
`A₀…B₁` are `pauliObservable`s and the involution hypotheses are discharged by
`pauliObservable_op_mul_self`. Proof: prove the identity in the raw tensor operator ring
`↑S ⊗ ↑T →L ↑S ⊗ ↑T` as a standalone `have` and transport it to the goal by defeq
(`(A⊗B).op` is definitionally `mapL A.op B.op`); inside, rewrite each `mapL A.op B.op` into the
product of embedded operators `(A ⊗ I)·(I ⊗ B)`, square via the algebraic identity
`IsCHSHTuple.sq_chsh`
(which gives `4 - ⁅A₀⊗I,A₁⊗I⁆·⁅I⊗B₀,I⊗B₁⁆`), then factor the two embedded commutators back
through `mapL` (`⁅A₀⊗I,A₁⊗I⁆ = ⁅A₀,A₁⁆ ⊗ I`, etc.) and flip the sign via `⁅A₁,A₀⁆ = -⁅A₀,A₁⁆`. -/
theorem chsh_tmul_sq (A₀ A₁ : Observable S) (B₀ B₁ : Observable T)
    (hA₀ : A₀.op * A₀.op = 1) (hA₁ : A₁.op * A₁.op = 1)
    (hB₀ : B₀.op * B₀.op = 1) (hB₁ : B₁.op * B₁.op = 1) :
    ((A₀ ⊗ B₀).op + (A₀ ⊗ B₁).op + (A₁ ⊗ B₀).op - (A₁ ⊗ B₁).op) ^ 2
      = 4 • (1 : (S ⊗ T) →L[ℂ] (S ⊗ T)) + TensorProduct.mapL ⁅A₁.op, A₀.op⁆ ⁅B₀.op, B₁.op⁆ := by
  -- Each `mapL f g` splits into a product of embedded operators `(f ⊗ I)·(I ⊗ g)`.
  have emb : ∀ (f : S →L[ℂ] S) (g : T →L[ℂ] T),
      TensorProduct.mapL f g = TensorProduct.mapL f 1 * TensorProduct.mapL 1 g := fun f g => by
    rw [← TensorProduct.mapL_mul, mul_one, one_mul]
  -- The `⁅A₁,A₀⁆` in the target is `-⁅A₀,A₁⁆`.
  have hswap : (⁅A₁.op, A₀.op⁆ : S →L[ℂ] S) = -⁅A₀.op, A₁.op⁆ := by
    rw [Ring.lie_def, Ring.lie_def, neg_sub]
  -- Prove the identity in the raw tensor ring `↑S ⊗ ↑T →L …` (elaborated independently, so the
  -- power/products are uniformly in that ring), then transport it to the goal by defeq
  -- (`(A ⊗ B).op` is definitionally `mapL A.op B.op`). The two embedded commutators factor through
  -- `mapL` by the companion lemmas `mapL_lie_left`/`mapL_lie_right`.
  have H : (TensorProduct.mapL A₀.op B₀.op + TensorProduct.mapL A₀.op B₁.op
        + TensorProduct.mapL A₁.op B₀.op - TensorProduct.mapL A₁.op B₁.op) ^ 2
      = 4 • 1 + TensorProduct.mapL ⁅A₁.op, A₀.op⁆ ⁅B₀.op, B₁.op⁆ := by
    rw [emb A₀.op B₀.op, emb A₀.op B₁.op, emb A₁.op B₀.op, emb A₁.op B₁.op,
      (isCHSHTuple_tmul A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁).sq_chsh,
      TensorProduct.mapL_lie_left A₀.op A₁.op, TensorProduct.mapL_lie_right B₀.op B₁.op,
      ← TensorProduct.mapL_mul, mul_one, one_mul, hswap, TensorProduct.mapL_neg_left]
    -- Goal: `4 - X = 4 • 1 + -X`; rewrite `4 • 1 = 4` and close additively.
    rw [nsmul_eq_mul, Nat.cast_ofNat, mul_one]
    abel
  exact H

/-- **The Tsirelson expectation bound.** For involutive observables `A₀, A₁` on `S` and
`B₀, B₁` on `T`, and any normalized pure state `ψ` of `S ⊗ T`, the CHSH combination of
expectation values satisfies
`⟪A₀⊗B₀⟫ + ⟪A₀⊗B₁⟫ + ⟪A₁⊗B₀⟫ - ⟪A₁⊗B₁⟫ ≤ 2√2`.

This is the operator-level statement of Nielsen & Chuang **(2.234)** (the physical, qubit-Pauli
instance is `pauliObservable_chsh_expectation_le` in `NC/Ch2/Problem2_3.lean`). Proof:
`tsirelson_inequality` on the CHSH tuple (`isCHSHTuple_tmul`) gives the operator bound
`A₀⊗B₀ + … ≤ √2³ • 1`; rewriting `√2³ = 2√2` and the embedded products back to the four
`Observable.tmul` operators, the operator-order → expectation bridge
(`re_inner_apply_le_of_le_smul_one`) and additivity of the inner product descend it to the sum
of expectation values. -/
theorem PureState.expectation_chsh_tmul_le (ψ : PureState (S ⊗ T))
    (A₀ A₁ : Observable S) (B₀ B₁ : Observable T)
    (hA₀ : A₀.op * A₀.op = 1) (hA₁ : A₁.op * A₁.op = 1)
    (hB₀ : B₀.op * B₀.op = 1) (hB₁ : B₁.op * B₁.op = 1) :
    ψ.expectation (A₀ ⊗ B₀) + ψ.expectation (A₀ ⊗ B₁) + ψ.expectation (A₁ ⊗ B₀)
      - ψ.expectation (A₁ ⊗ B₁) ≤ 2 * Real.sqrt 2 := by
  have hbound := tsirelson_inequality (TensorProduct.mapL A₀.op 1) (TensorProduct.mapL A₁.op 1)
    (TensorProduct.mapL (1 : S →L[ℂ] S) B₀.op) (TensorProduct.mapL (1 : S →L[ℂ] S) B₁.op)
    (isCHSHTuple_tmul A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁)
  -- Collapse the embedded products `(Aᵢ ⊗ I)·(I ⊗ Bⱼ)` to `mapL Aᵢ.op Bⱼ.op`.
  simp only [← TensorProduct.mapL_mul, mul_one, one_mul] at hbound
  -- `mapL Aᵢ.op Bⱼ.op` is definitionally `(Aᵢ ⊗ Bⱼ).op`: move the bound into the `↑(S ⊗ T)`
  -- operator ring, where it applies to `ψ.vec` and matches the expectation generators.
  have hbound' : (A₀ ⊗ B₀).op + (A₀ ⊗ B₁).op + (A₁ ⊗ B₀).op - (A₁ ⊗ B₁).op
      ≤ (Real.sqrt 2 ^ 3 : ℝ) • (1 : (S ⊗ T) →L[ℂ] (S ⊗ T)) := hbound
  -- Descend the operator bound to expectation values via the raw-operator bridge.
  have key := ψ.re_inner_apply_le_of_le_smul_one hbound'
  have h23 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [pow_succ, h2]
  rw [h23] at key
  simp only [PureState.expectation, add_apply,
    sub_apply, inner_add_right, inner_sub_right, Complex.add_re,
    Complex.sub_re] at key ⊢
  linarith

end AxQM
