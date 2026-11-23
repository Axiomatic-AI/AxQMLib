/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import ToMathlib.RingTheory.MvPolynomial.Multilinear

/-!
# Concrete: the OR polynomial `1 - ∏ₖ (1 - Xₖ)` (Nielsen & Chuang, Exercise 6.19)

Nielsen & Chuang, Exercise 6.19 (p. 273): the polynomial
`P(X) = 1 − (1 − X₀)(1 − X₁) … (1 − X_{N-1})` represents OR.

## Statement and reading

In the *method of polynomials* (N&C §6.7) a polynomial `p : Rᴺ → R` **represents** a Boolean
function `F` when `p(X) = F(X)` for every `X ∈ {0, 1}ᴺ`, with the Boolean value `F(X) ∈ {0, 1}`
read inside `R`. The OR function is `F(X) = X₀ ∨ X₁ ∨ ⋯ ∨ X_{N-1}` — it is `1` iff at least one
coordinate is `1`. The exercise asks to verify that the explicit polynomial
`P(X) = 1 − ∏ₖ (1 − Xₖ)` represents it.

The content is elementary: on the Boolean cube each factor `1 − Xₖ` is `1` when `Xₖ = 0` and `0`
when `Xₖ = 1`, so the product `∏ₖ (1 − Xₖ)` is `1` exactly when *every* `Xₖ = 0`, and `0` as soon
as some `Xₖ = 1`. Hence `1 − ∏ₖ (1 − Xₖ)` is `0` when all coordinates vanish and `1` otherwise —
precisely the OR function.

## Declarations

* `Represents p F` — N&C's representation predicate: `p` evaluated at every Boolean point
  (encoding `true ↦ 1`, `false ↦ 0`) returns the `{0, 1}`-encoded value of `F`.
* `orFun` — the OR Boolean function `b ↦ (∃ k, bₖ = true)`.
* `orPoly` — the polynomial `1 - ∏ᵢ (1 - Xᵢ)`.
* `eval_orPoly` — its evaluation at a Boolean point: `1` if some coordinate is `true`, else `0`.
* `orPoly_represents_orFun` — **Exercise 6.19 itself**: `orPoly` represents `orFun`.
* `isMultilinear_orPoly` — `orPoly` is multilinear (each variable to degree `≤ 1`), so it lies in
  the class N&C's method considers and, by the uniqueness of the multilinear representation
  (`MvPolynomial.IsMultilinear.eq_of_forall_eval_boolean`, Exercise 6.18), it is *the*
  minimum-degree representative of OR.

The statement of Exercise 6.19 is in `AxQM/NC/Ch6/Exercise6_19.lean`.

## Faithfulness

Everything is stated for an arbitrary finite index type `σ` (N&C's `σ = Fin N`) and an arbitrary
commutative ring `R` (N&C's `R = ℝ`), a strengthening rather than a weakening: the representation
identity holds over any commutative ring. The multilinearity fact additionally needs `R` nontrivial
(over the zero ring degrees are vacuously `0` anyway); N&C's `ℝ` is nontrivial.
-/

namespace AxQM.Concrete

open MvPolynomial

variable {σ : Type*} {R : Type*} [CommRing R]

/-- **Representation of a Boolean function by a polynomial** (Nielsen & Chuang, §6.7). A polynomial
`p` *represents* the Boolean function `F : (σ → Bool) → Bool` when, evaluated at every Boolean point
`X ∈ {0, 1}ˢ` (encoding `true ↦ 1`, `false ↦ 0`), it returns the `{0, 1}`-encoded value `F(X)`:
`p(X) = F(X)` for all `X`. This is N&C's notion of a polynomial representing a Boolean function. -/
def Represents (p : MvPolynomial σ R) (F : (σ → Bool) → Bool) : Prop :=
  ∀ b : σ → Bool, eval (fun i => if b i then (1 : R) else 0) p = if F b then 1 else 0

/-- **The OR Boolean function**: `true` iff at least one coordinate is `true`, i.e. N&C's
`X₀ ∨ X₁ ∨ ⋯ ∨ X_{N-1}`. -/
def orFun [Fintype σ] (b : σ → Bool) : Bool := decide (∃ i, b i = true)

/-- **The OR polynomial** `P(X) = 1 − (1 − X₀)(1 − X₁) ⋯ (1 − X_{N-1})` of Nielsen & Chuang,
Exercise 6.19: the explicit multilinear polynomial claimed to represent the OR function. -/
noncomputable def orPoly [Fintype σ] : MvPolynomial σ R := 1 - ∏ i, (1 - X i)

/-- The OR function is `true` at `b` exactly when some coordinate of `b` is `true`. -/
@[simp] theorem orFun_eq_true_iff [Fintype σ] (b : σ → Bool) :
    orFun b = true ↔ ∃ i, b i = true := by
  simp [orFun]

/-- **Evaluation of the OR polynomial on the Boolean cube.** At a Boolean point `b` the OR
polynomial evaluates to `1` if some coordinate is `true` and to `0` otherwise: the product
`∏ᵢ (1 - bᵢ)` vanishes as soon as one factor `1 - bᵢ` is `0` (i.e. `bᵢ = true`), and is `1` when
every factor is `1` (i.e. all `bᵢ = false`). -/
theorem eval_orPoly [Fintype σ] (b : σ → Bool) :
    eval (fun i => if b i then (1 : R) else 0) (orPoly : MvPolynomial σ R)
      = if ∃ i, b i = true then 1 else 0 := by
  rw [orPoly]
  simp only [map_sub, map_one, map_prod, eval_X]
  by_cases hex : ∃ i, b i = true
  · rw [ite_eq_left hex]
    obtain ⟨j, hj⟩ := hex
    have hzero : (1 : R) - (if b j then (1 : R) else 0) = 0 := by simp [hj]
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hzero, sub_zero]
  · rw [ite_eq_right hex]
    have hall : ∀ i ∈ (Finset.univ : Finset σ),
        (1 : R) - (if b i then (1 : R) else 0) = 1 := by
      intro i _
      have hbi : b i = false := by
        simp only [not_exists, Bool.not_eq_true] at hex; exact hex i
      simp [hbi]
    rw [Finset.prod_eq_one hall, sub_self]

/-- **Nielsen & Chuang, Exercise 6.19.** The polynomial `P(X) = 1 − ∏ₖ (1 − Xₖ)` represents the
OR function. -/
theorem orPoly_represents_orFun [Fintype σ] :
    Represents (orPoly : MvPolynomial σ R) orFun := by
  intro b
  rw [eval_orPoly, orFun]
  simp only [decide_eq_true_eq]

/-- **The OR polynomial is multilinear** (each variable occurs to degree at most one). Together with
the uniqueness of the multilinear representation
(`MvPolynomial.IsMultilinear.eq_of_forall_eval_boolean`, Exercise 6.18) this identifies `orPoly` as
the minimum-degree polynomial representing OR. -/
theorem isMultilinear_orPoly [Fintype σ] [Nontrivial R] :
    (orPoly : MvPolynomial σ R).IsMultilinear := by
  classical
  intro j
  have hprod : degreeOf j (∏ i, ((1 : MvPolynomial σ R) - X i)) ≤ 1 := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => (1 : MvPolynomial σ R) - X i)
      (Finset.mem_univ j)]
    refine (degreeOf_mul_le j _ _).trans ?_
    have h1 : degreeOf j ((1 : MvPolynomial σ R) - X j) ≤ 1 := by
      refine (degreeOf_sub_le j 1 (X j)).trans ?_
      rw [degreeOf_one, degreeOf_X]
      simp
    have h2 : degreeOf j (∏ i ∈ Finset.univ.erase j, ((1 : MvPolynomial σ R) - X i)) = 0 := by
      refine Nat.le_zero.mp ((degreeOf_prod_le j _ _).trans (le_of_eq ?_))
      refine Finset.sum_eq_zero fun i hi => ?_
      have hij : j ≠ i := (Finset.ne_of_mem_erase hi).symm
      refine Nat.le_zero.mp ((degreeOf_sub_le j 1 (X i)).trans ?_)
      rw [degreeOf_one, degreeOf_X, ite_eq_right hij]
      simp
    omega
  rw [orPoly]
  refine (degreeOf_sub_le j 1 _).trans ?_
  rw [degreeOf_one]
  exact max_le (Nat.zero_le _) hprod

end AxQM.Concrete
