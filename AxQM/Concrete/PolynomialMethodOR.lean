/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.OrPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Concrete: the polynomial-method lower bound `Q₀(OR) ≥ N` (Nielsen & Chuang, Exercise 6.20)

Nielsen & Chuang, Exercise 6.20 (p. 274): a zero-error quantum circuit for OR yields a polynomial
representing OR, whence `Q₀(OR) ≥ N`.

## The argument (N&C §6.7, the *method of polynomials*)

A quantum algorithm making `T` oracle queries produces output amplitudes `cₖ(X)` that are
polynomials of degree at most `T` in the oracle bits `X₀, …, X_{N-1}` (N&C eqs. 6.58–6.61: each
oracle call raises the degree by at most one, unitaries in between do not raise it). For a
**zero-error** algorithm computing OR, split the computational basis into the "answer `0`",
"answer `1`" and "inconclusive" blocks. Zero error forces two things:

* on every input `X` with `OR(X) = 1` the algorithm never answers `0`, so the total answer-`0`
  probability `∑_{k answer 0} |cₖ(X)|²` is `0`, whence **every** answer-`0` amplitude `cₖ(X)`
  vanishes there;
* on the unique input `X = 0` with `OR(X) = 0` the algorithm answers `0` with probability `> 1/2`,
  so some answer-`0` amplitude `cₖ(0) ≠ 0`.

Fix that `k`; a real or imaginary part of `cₖ` is then a **real** polynomial `c` of total degree
`≤ T` (N&C treats every polynomial as multilinear, since `Xⱼ² = Xⱼ` on `{0,1}`) that vanishes at
every Boolean point with `OR = 1` and is nonzero at `0`. Normalising,
`P(X) = 1 − c(0)⁻¹·c(X)` is `0` at `X = 0` and `1` at every other Boolean point — it **represents
OR** — and `deg P ≤ deg c ≤ T`. Since the (multilinear) representative of OR is unique
(Exercise 6.18) and equals `1 − ∏ₖ(1 − Xₖ)` of total degree `N` (Exercise 6.19), `P` *is* that
polynomial, so `N = deg P ≤ T`. As this holds for every zero-error `T`-query circuit, `Q₀(OR) ≥ N`.

## The declarations

The genuinely formal content is the **polynomial construction and the degree bound**, taking N&C's
established "the amplitude is a degree-`≤ T` polynomial" (eqs. 6.58–6.61) as the premise — exactly
the input the exercise says to use:

* `totalDegree_one_sub_X`, `totalDegree_prod_one_sub_X` — degree bookkeeping for `1 − Xⱼ` and
  `∏ⱼ(1 − Xⱼ)`, over a field.
* `totalDegree_orPoly` — the OR polynomial `1 − ∏ₖ(1 − Xₖ)` has total degree `N = Fintype.card σ`
  (`deg(OR) = N`).
* `orZeroErrorPoly` — the constructed polynomial `P(X) = 1 − c(0)⁻¹·c(X)`.
* `orZeroErrorPoly_represents` — **the exercise's construction**: `P` represents OR, whenever `c`
  vanishes on the `OR = 1` inputs and `c(0) ≠ 0`.
* `orZeroErrorPoly_isMultilinear` — `P` is multilinear when `c` is.
* `orZeroError_query_lower_bound` — **Exercise 6.20**: any multilinear degree-`≤ T` polynomial `c`
  with those zero-error properties forces `Fintype.card σ ≤ T` (i.e. `Q₀(OR) ≥ N`).
* `orZeroError_query_lower_bound_of_totalDegree_le` — the same lower bound *without* assuming `c`
  multilinear: a physical query amplitude (a degree-`≤ T` polynomial in the oracle bits, N&C
  eqs. 6.58–6.61) is not manifestly multilinear, so this multilinearizes it first
  (`MvPolynomial.multilinearize`, which preserves Boolean values and does not raise the degree)
  and applies `orZeroError_query_lower_bound`. 

## Scope

Once N&C's method-of-polynomials reduction (a `T`-query circuit's
amplitude is a degree-`≤ T` polynomial in the oracle bits) is in hand — which the exercise instructs
us to use, and which the chapter derives in eqs. 6.58–6.61 — the exercise's remaining content is
pure commutative algebra: a construction on `MvPolynomial σ K` and a bound on `totalDegree`
(compare the OR polynomial of Exercise 6.19). The statement of Exercise 6.20 is in
`AxQM/NC/Ch6/Exercise6_20.lean`. Compare also the query-complexity exercises 6.8 and 6.15, whose
formalisable propositions are likewise pure mathematics. The physics reduction itself is *not*
re-derived here: the library has no general quantum-query-circuit model (there is no notion of a
`T`-query oracle circuit nor a theorem that its amplitudes are bounded-degree polynomials), and
building one is a separate development; taking that reduction as the premise is faithful to the
exercise, which supplies it from the preceding text.

## Faithfulness

The hypotheses on `c` are exactly the fingerprint of "the answer-`0` amplitude of a zero-error
`T`-query OR circuit": multilinear (N&C: `Xⱼ² = Xⱼ`), total degree `≤ T` (the `T`-query bound),
vanishing at every `OR = 1` Boolean input (zero error never answers `0` there), nonzero at `0` (it
does answer `0` on the all-zero input). The setting is an arbitrary field `K` (N&C's `K = ℝ`); a
field is genuinely required — the construction inverts `c(0)` — and is faithful, not a weakening.
The size `N` is `Fintype.card σ` for an arbitrary finite index type `σ` (N&C's `σ = Fin N`).
-/

namespace AxQM.Concrete

open MvPolynomial

variable {σ : Type*} {K : Type*} [Field K]

/-- The single factor `1 − Xₐ` has total degree `1` (over a nontrivial ring: the linear term
dominates the constant `1`). -/
theorem totalDegree_one_sub_X (a : σ) : (1 - X a : MvPolynomial σ K).totalDegree = 1 := by
  rw [sub_eq_add_neg,
    totalDegree_add_eq_right_of_totalDegree_lt
      (by rw [totalDegree_one, totalDegree_neg, totalDegree_X]; exact Nat.zero_lt_one),
    totalDegree_neg, totalDegree_X]

/-- The factor `1 − Xₐ` is a nonzero polynomial. -/
theorem one_sub_X_ne_zero (a : σ) : (1 - X a : MvPolynomial σ K) ≠ 0 := by
  intro h
  have hd := totalDegree_one_sub_X (K := K) a
  rw [h, totalDegree_zero] at hd
  exact absurd hd (by norm_num)

/-- The product `∏_{i ∈ s} (1 − Xᵢ)` has total degree `s.card`: over a field the total degree is
additive across the (nonzero) factors, each of degree `1`. -/
theorem totalDegree_prod_one_sub_X (s : Finset σ) :
    (∏ i ∈ s, (1 - X i : MvPolynomial σ K)).totalDegree = s.card := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      totalDegree_mul_of_isDomain (one_sub_X_ne_zero a)
        (Finset.prod_ne_zero_iff.mpr (fun i _ => one_sub_X_ne_zero i)),
      totalDegree_one_sub_X a, ih]
    omega

/-- **`deg(OR) = N`.** The OR polynomial `1 − ∏ₖ(1 − Xₖ)` (Exercise 6.19) has total degree
`N = Fintype.card σ`: the top term `∏ₖ Xₖ` of the product survives, and subtracting from the
constant `1` cannot cancel it. -/
theorem totalDegree_orPoly [Fintype σ] :
    (orPoly : MvPolynomial σ K).totalDegree = Fintype.card σ := by
  have hprod : (∏ i : σ, (1 - X i : MvPolynomial σ K)).totalDegree = Fintype.card σ := by
    rw [← Finset.card_univ]; exact totalDegree_prod_one_sub_X Finset.univ
  rcases Nat.eq_zero_or_pos (Fintype.card σ) with h | h
  · -- `σ` empty: the product is the empty product `1`, so `orPoly = 1 - 1 = 0`.
    have hcard : (Finset.univ : Finset σ) = ∅ := by
      rw [← Finset.card_eq_zero, Finset.card_univ, h]
    rw [orPoly, hcard, Finset.prod_empty, sub_self, totalDegree_zero, h]
  · rw [orPoly, sub_eq_add_neg,
      totalDegree_add_eq_right_of_totalDegree_lt
        (by rw [totalDegree_one, totalDegree_neg, hprod]; exact h),
      totalDegree_neg, hprod]

/-- **The polynomial constructed from a zero-error OR circuit** (Nielsen & Chuang, Exercise 6.20):
`P(X) = 1 − c(0)⁻¹·c(X)`, where `c` is (a real/imaginary component of) an answer-`0` amplitude of
the circuit, evaluated at the all-zero point `c(0)`. -/
noncomputable def orZeroErrorPoly (c : MvPolynomial σ K) : MvPolynomial σ K :=
  1 - (eval (fun _ => (0 : K)) c)⁻¹ • c

/-- **The construction represents OR** (the heart of Exercise 6.20). If `c` vanishes at every
Boolean point where OR is `true` (the zero-error algorithm never answers `0` there) and `c(0) ≠ 0`
(it answers `0` on the all-zero input), then `P(X) = 1 − c(0)⁻¹·c(X)` represents the OR function:
it is `1` wherever `c` vanishes and `1 − c(0)⁻¹·c(0) = 0` at the all-zero input. -/
theorem orZeroErrorPoly_represents [Fintype σ] {c : MvPolynomial σ K}
    (hvanish : ∀ b : σ → Bool, (∃ i, b i = true) →
      eval (fun i => if b i then (1 : K) else 0) c = 0)
    (h0 : eval (fun _ => (0 : K)) c ≠ 0) :
    Represents (orZeroErrorPoly c) orFun := by
  intro b
  rw [orZeroErrorPoly, smul_eq_C_mul, map_sub, map_one, map_mul, eval_C]
  by_cases hex : ∃ i, b i = true
  · have hor : orFun b = true := (orFun_eq_true_iff b).mpr hex
    rw [hvanish b hex, mul_zero, sub_zero, ite_eq_left hor]
  · have hor : orFun b = false := by
      rcases Bool.eq_false_or_eq_true (orFun b) with h | h
      · exact absurd ((orFun_eq_true_iff b).mp h) hex
      · exact h
    have hpt : (fun i => if b i then (1 : K) else 0) = (fun _ => (0 : K)) := by
      funext i
      have hbi : b i = false := by
        rcases Bool.eq_false_or_eq_true (b i) with h | h
        · exact absurd ⟨i, h⟩ hex
        · exact h
      simp [hbi]
    rw [hpt, inv_mul_cancel₀ h0, sub_self, ite_eq_right (by rw [hor]; simp)]

/-- **The construction is multilinear** when `c` is: scaling by the constant `c(0)⁻¹` and
subtracting from `1` keeps every variable to degree at most one. -/
theorem orZeroErrorPoly_isMultilinear {c : MvPolynomial σ K} (hc : c.IsMultilinear) :
    (orZeroErrorPoly c).IsMultilinear := by
  rw [orZeroErrorPoly, smul_eq_C_mul]
  refine IsMultilinear.sub (fun i => ?_) (fun i => ?_)
  · rw [degreeOf_one]; exact Nat.zero_le 1
  · calc degreeOf i (C (eval (fun _ => (0 : K)) c)⁻¹ * c)
        ≤ degreeOf i (C (eval (fun _ => (0 : K)) c)⁻¹) + degreeOf i c := degreeOf_mul_le i _ _
      _ = degreeOf i c := by rw [degreeOf_C, zero_add]
      _ ≤ 1 := hc i

/-- Two multilinear polynomials that both represent the same Boolean function are equal — the
`Represents`-phrased form of the uniqueness of the multilinear representation (Exercise 6.18). -/
theorem eq_of_represents {p q : MvPolynomial σ K} {F : (σ → Bool) → Bool}
    (hp : p.IsMultilinear) (hq : q.IsMultilinear)
    (hpF : Represents p F) (hqF : Represents q F) : p = q := by
  classical
  refine hp.eq_of_forall_eval_boolean hq (fun x hx => ?_)
  set b : σ → Bool := fun i => decide (x i = 1) with hb
  have hxb : (fun i => if b i then (1 : K) else 0) = x := by
    funext i
    rcases hx i with h | h
    · have hbi : b i = false := by rw [hb]; exact decide_eq_false (by rw [h]; exact zero_ne_one)
      rw [hbi]; simp [h]
    · have hbi : b i = true := by rw [hb]; exact decide_eq_true (by rw [h])
      rw [hbi]; simp [h]
  rw [← hxb, hpF b, hqF b]

/-- **Nielsen & Chuang, Exercise 6.20: `Q₀(OR) ≥ N`.** Let `c` be a multilinear polynomial of total
degree at most `T` — the answer-`0` amplitude of a zero-error `T`-query circuit computing OR — that
vanishes at every Boolean input where OR is `true` and is nonzero at the all-zero input. Then
`N = Fintype.card σ ≤ T`. Since this bounds the query count `T` of *every* such circuit from below
by `N`, the zero-error quantum query complexity satisfies `Q₀(OR) ≥ N`.

The proof builds `P = 1 − c(0)⁻¹·c` (`orZeroErrorPoly`), shows it represents OR and is multilinear,
identifies it by uniqueness with the OR polynomial `1 − ∏ₖ(1 − Xₖ)` of total degree `N`
(`totalDegree_orPoly`), and reads off `N = deg P ≤ deg c ≤ T`. -/
theorem orZeroError_query_lower_bound [Fintype σ] {T : ℕ} {c : MvPolynomial σ K}
    (hml : c.IsMultilinear)
    (hvanish : ∀ b : σ → Bool, (∃ i, b i = true) →
      eval (fun i => if b i then (1 : K) else 0) c = 0)
    (h0 : eval (fun _ => (0 : K)) c ≠ 0)
    (hdeg : c.totalDegree ≤ T) :
    Fintype.card σ ≤ T := by
  have hPeq : orZeroErrorPoly c = (orPoly : MvPolynomial σ K) :=
    eq_of_represents (orZeroErrorPoly_isMultilinear hml) isMultilinear_orPoly
      (orZeroErrorPoly_represents hvanish h0) orPoly_represents_orFun
  have hdegP : (orZeroErrorPoly c).totalDegree ≤ T := by
    rw [orZeroErrorPoly]
    refine (totalDegree_sub _ _).trans ?_
    rw [totalDegree_one]
    exact max_le (Nat.zero_le _) ((totalDegree_smul_le _ _).trans hdeg)
  calc Fintype.card σ = (orPoly : MvPolynomial σ K).totalDegree := totalDegree_orPoly.symm
    _ = (orZeroErrorPoly c).totalDegree := by rw [hPeq]
    _ ≤ T := hdegP

/-- **Nielsen & Chuang, Exercise 6.20 for a not-necessarily-multilinear amplitude: `Q₀(OR) ≥ N`.**
The multilinearity hypothesis of `orZeroError_query_lower_bound` is dropped. A physical query
amplitude produced by the method of polynomials (N&C eqs. 6.58–6.61) is a polynomial of total degree
`≤ T` in the oracle bits, but is *not* presented in multilinear form; N&C reduce it using
`Xⱼ² = Xⱼ`. Here that reduction is `MvPolynomial.multilinearize`, which agrees with `c` at every
Boolean point (`eval_multilinearize`) and does not raise the total degree
(`totalDegree_multilinearize_le`). So `multilinearize c` still vanishes at every `OR = 1` Boolean
input, is still nonzero at the all-zero input, and has total degree `≤ T` — and being multilinear it
feeds `orZeroError_query_lower_bound`, giving `N = Fintype.card σ ≤ T`. This is the form the
Born-rule physics headline (Exercise 6.20's boundary statement) consumes. -/
theorem orZeroError_query_lower_bound_of_totalDegree_le [Fintype σ] {T : ℕ} {c : MvPolynomial σ K}
    (hvanish : ∀ b : σ → Bool, (∃ i, b i = true) →
      eval (fun i => if b i then (1 : K) else 0) c = 0)
    (h0 : eval (fun _ => (0 : K)) c ≠ 0)
    (hdeg : c.totalDegree ≤ T) :
    Fintype.card σ ≤ T := by
  have hbool : ∀ b : σ → Bool, ∀ i,
      (if b i then (1 : K) else 0) = 0 ∨ (if b i then (1 : K) else 0) = 1 := by
    intro b i; by_cases h : b i = true <;> simp [h]
  apply orZeroError_query_lower_bound (c := multilinearize c) (isMultilinear_multilinearize c)
  · intro b hb
    rw [eval_multilinearize (hbool b) c]
    exact hvanish b hb
  · rw [eval_multilinearize (fun _ => Or.inl rfl) c]
    exact h0
  · exact (totalDegree_multilinearize_le c).trans hdeg

end AxQM.Concrete
