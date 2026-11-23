/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Order.Preorder.Finite

/-! # Multilinear polynomials and the uniqueness of Boolean representations

A multivariate polynomial is *multilinear* when every variable occurs to degree at most one, i.e.
every monomial in its support is square-free. On the Boolean cube `{0, 1} ⊆ R` a multilinear
polynomial is determined by the function it computes: two multilinear polynomials that agree at
every point with all coordinates in `{0, 1}` are equal.

## Main definitions

* `MvPolynomial.IsMultilinear p`: every variable of `p` has degree at most `1`
  (`∀ i, p.degreeOf i ≤ 1`); equivalently `p ∈ MvPolynomial.restrictDegree σ R 1`
  (`MvPolynomial.isMultilinear_iff_mem_restrictDegree`).
* `MvPolynomial.multilinearize p`: the **multilinear reduction** of `p`, obtained by replacing every
  monomial `∏ᵢ Xᵢ^{mᵢ}` by its squarefree part `∏_{i : mᵢ > 0} Xᵢ`. It realises the reduction
  `Xₖ² = Xₖ` used throughout the method of polynomials (N&C §6.7).

## Main results

* `MvPolynomial.IsMultilinear.eq_zero_of_forall_eval_boolean`: a multilinear polynomial that
  evaluates to `0` at every Boolean point is the zero polynomial.
* `MvPolynomial.IsMultilinear.eq_of_forall_eval_boolean`: two multilinear polynomials that agree
  at every Boolean point are equal — the *uniqueness of the multilinear representation* of a
  function `{0, 1}ˢ → R`.
* `MvPolynomial.isMultilinear_multilinearize`, `MvPolynomial.eval_multilinearize`,
  `MvPolynomial.totalDegree_multilinearize_le`: the multilinear reduction is multilinear, agrees
  with `p` at every Boolean point, and has no larger total degree — so it is *the* unique
  multilinear representative of the function `p` computes on `{0, 1}ˢ`, and it is of minimal degree.

The last statement is Exercise 6.18 of Nielsen & Chuang, *Quantum Computation and Quantum
Information*: "the minimum degree polynomial representing a Boolean function `F` is unique". In the
method of polynomials (N&C §6.7) every polynomial considered is multilinear, since `Xₖ² = Xₖ` on
`{0, 1}`, and the unique multilinear representative is automatically the minimum-degree one; the
faithful content of the exercise is therefore uniqueness *among multilinear polynomials* (see the
"Implementation notes"). It underlies the polynomial lower bounds `deg(F) ≤ 2·Qₑ(F)` etc.

## Implementation notes

Everything is stated for an arbitrary index type `σ` (not necessarily finite — the support of a
polynomial is finite regardless) and an arbitrary commutative (semi)ring `R`; N&C's `σ = Fin N`,
`R = ℝ` is the special case. No nontriviality of `R` is needed.

The multilinear restriction is essential and *not* a weakening: without it the minimum-degree
representative is genuinely non-unique. For example over `R = ℝ`, `X₀·X₁ + X₀^2` and
`X₀·X₁ + X₀` are distinct degree-`2` polynomials computing the same function on `{0, 1}²`.
Reducing `Xₖ^2` to `Xₖ` (which never raises the degree) sends every representative to the unique
multilinear one, which is thus the minimum-degree representative in N&C's multilinear setting.

The proof of `eq_zero_of_forall_eval_boolean` avoids Möbius inversion: pick a monomial `m₀` that is
minimal in the support for the pointwise order on `σ →₀ ℕ`, and evaluate at its own `0/1`
indicator `x i = m₀ i`. For any other support monomial `m`, minimality gives `¬ m ≤ m₀`, so some
variable `i` has `m i = 1` while `m₀ i = 0`, making the monomial vanish at `x`; only the `m₀` term
survives, so `eval x p = coeff m₀ p`, which is nonzero — contradicting that `p` vanishes on the
cube.
-/

@[expose] public section

namespace MvPolynomial

variable {σ : Type*} {R : Type*}

section CommSemiring
variable [CommSemiring R]

/-- A multivariate polynomial is **multilinear** when every variable occurs to degree at most one;
equivalently, every monomial in its support is square-free. See
`MvPolynomial.isMultilinear_iff_mem_restrictDegree` for the reformulation as membership in
`MvPolynomial.restrictDegree σ R 1`. -/
def IsMultilinear (p : MvPolynomial σ R) : Prop := ∀ i, p.degreeOf i ≤ 1

/-- A polynomial is multilinear iff it lies in the degree-`1` restriction submodule
`MvPolynomial.restrictDegree σ R 1`. This identifies `IsMultilinear` with the existing Mathlib
notion and, via `Submodule.sub_mem`, gives closure under subtraction (`IsMultilinear.sub`). -/
theorem isMultilinear_iff_mem_restrictDegree {p : MvPolynomial σ R} :
    p.IsMultilinear ↔ p ∈ restrictDegree σ R 1 := by
  simp only [IsMultilinear, mem_restrictDegree, degreeOf_le_iff]
  exact ⟨fun h s hs i => h i s hs, fun h i s hs => h s hs i⟩

/-- A polynomial is multilinear iff every monomial in its support has all exponents at most `1`. -/
theorem isMultilinear_iff {p : MvPolynomial σ R} :
    p.IsMultilinear ↔ ∀ m ∈ p.support, ∀ i, m i ≤ 1 := by
  rw [isMultilinear_iff_mem_restrictDegree, mem_restrictDegree]

/-- Every exponent of every support monomial of a multilinear polynomial is at most `1`. -/
theorem IsMultilinear.exponent_le {p : MvPolynomial σ R} (hp : p.IsMultilinear)
    {m : σ →₀ ℕ} (hm : m ∈ p.support) (i : σ) : m i ≤ 1 :=
  isMultilinear_iff.mp hp m hm i

/-- A multilinear polynomial that evaluates to `0` at every point of the Boolean cube (every
`x : σ → R` with each coordinate in `{0, 1}`) is the zero polynomial.

The argument picks a support monomial `m₀` minimal for the pointwise order on `σ →₀ ℕ` and
evaluates at its own indicator point `x i = m₀ i ∈ {0, 1}`; minimality kills every other support
term, so `eval x p = coeff m₀ p ≠ 0`, contradicting that `p` vanishes on the cube. -/
theorem IsMultilinear.eq_zero_of_forall_eval_boolean {p : MvPolynomial σ R}
    (hp : p.IsMultilinear)
    (h : ∀ x : σ → R, (∀ i, x i = 0 ∨ x i = 1) → eval x p = 0) : p = 0 := by
  by_contra hp0
  have hne : p.support.Nonempty := support_nonempty.mpr hp0
  -- a support monomial minimal for the pointwise order
  obtain ⟨m₀, hm₀mem, hm₀min⟩ := Finset.exists_minimal hne
  -- evaluate at the `0/1` indicator of `m₀`
  set x : σ → R := fun i => (m₀ i : R) with hx_def
  have hxbool : ∀ i, x i = 0 ∨ x i = 1 := by
    intro i
    have hi : m₀ i ≤ 1 := hp.exponent_le hm₀mem i
    obtain h0 | h1 : m₀ i = 0 ∨ m₀ i = 1 := by omega
    · left; simp [hx_def, h0]
    · right; simp [hx_def, h1]
  -- the `m₀` monomial evaluates to `1` at its own indicator
  have hprod_m0 : (∏ i ∈ m₀.support, x i ^ m₀ i) = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    have hne0 : m₀ i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hle : m₀ i ≤ 1 := hp.exponent_le hm₀mem i
    have h1 : m₀ i = 1 := by omega
    simp [hx_def, h1]
  -- only the `m₀` term of `eval x p` survives
  have hkey : eval x p = p.coeff m₀ := by
    rw [eval_eq]
    refine (Finset.sum_eq_single_of_mem m₀ hm₀mem ?_).trans ?_
    · intro m hm hmne
      have hnotle : ¬ m ≤ m₀ := fun hle => hmne (le_antisymm hle (hm₀min hm hle))
      simp only [Finsupp.le_def, not_forall, not_le] at hnotle
      obtain ⟨i, hi⟩ := hnotle
      have hmi : m i = 1 := by have := hp.exponent_le hm i; omega
      have hm0i : m₀ i = 0 := by omega
      have hzero : x i ^ m i = 0 := by simp [hx_def, hm0i, hmi]
      exact mul_eq_zero_of_right _
        (Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr (by omega : m i ≠ 0)) hzero)
    · rw [hprod_m0, mul_one]
  -- but `coeff m₀ p ≠ 0` since `m₀ ∈ p.support`
  have hc0 : p.coeff m₀ = 0 := by rw [← hkey]; exact h x hxbool
  exact (mem_support_iff.mp hm₀mem) hc0

/-- The **squarefree reduction** of a monomial exponent vector `m : σ →₀ ℕ`: clamp every exponent
to at most `1`, so `clampExp m i = min (m i) 1`. It sends the exponent vector of `∏ᵢ Xᵢ^{mᵢ}` to
that of its squarefree part `∏_{i : mᵢ > 0} Xᵢ`. On the Boolean cube (`Xᵢ² = Xᵢ`) this leaves a
monomial's value unchanged, which is what makes `MvPolynomial.multilinearize` preserve Boolean
evaluations. -/
noncomputable def clampExp (m : σ →₀ ℕ) : σ →₀ ℕ := m.mapRange (fun n => min n 1) (by simp)

/-- The clamped exponent at a variable is `min (m i) 1`. -/
@[simp] theorem clampExp_apply (m : σ →₀ ℕ) (i : σ) : clampExp m i = min (m i) 1 :=
  Finsupp.mapRange_apply

/-- Clamping does not change which variables occur: `min (m i) 1 = 0 ↔ m i = 0`. -/
theorem clampExp_support (m : σ →₀ ℕ) : (clampExp m).support = m.support := by
  ext i
  simp only [Finsupp.mem_support_iff, clampExp_apply, ne_eq]
  omega

/-- The **multilinearization** of a multivariate polynomial `p`: reduce every monomial of `p` to its
squarefree part (`clampExp`), i.e. `∏ᵢ Xᵢ^{mᵢ} ↦ ∏_{i : mᵢ > 0} Xᵢ`, adding up the coefficients of
monomials that collide. It is multilinear (`isMultilinear_multilinearize`), agrees with `p` at every
point of the Boolean cube (`eval_multilinearize`), and has no larger total degree
(`totalDegree_multilinearize_le`); hence, by `IsMultilinear.eq_of_forall_eval_boolean`, it is the
unique multilinear polynomial representing the function `p` computes on `{0, 1}ˢ`, and it is of
minimal degree among all such representatives. This is the formal content of "every polynomial may
be taken multilinear, since `Xₖ² = Xₖ`" in the method of polynomials (N&C §6.7). -/
noncomputable def multilinearize (p : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ m ∈ p.support, monomial (clampExp m) (p.coeff m)

/-- The multilinearization of `p` is multilinear: every monomial in its support is a squarefree
`clampExp m`, all of whose exponents are `≤ 1`. -/
theorem isMultilinear_multilinearize (p : MvPolynomial σ R) :
    (multilinearize p).IsMultilinear := by
  classical
  rw [isMultilinear_iff]
  intro n hn i
  obtain ⟨m, -, hn'⟩ := Finset.mem_biUnion.mp (support_sum hn)
  rw [Finset.mem_singleton.mp (support_monomial_subset hn'), clampExp_apply]
  omega

/-- **Multilinearization preserves Boolean evaluations.** At any point `x` of the Boolean cube
(each `x i ∈ {0, 1}`), `eval x (multilinearize p) = eval x p`: reducing `Xᵢ^{mᵢ}` to its squarefree
factor `Xᵢ` changes nothing, since `x i ^ mᵢ = x i` whenever `x i ∈ {0, 1}` and `mᵢ ≥ 1`. -/
theorem eval_multilinearize {x : σ → R} (hx : ∀ i, x i = 0 ∨ x i = 1) (p : MvPolynomial σ R) :
    eval x (multilinearize p) = eval x p := by
  classical
  conv_rhs => rw [p.as_sum]
  rw [multilinearize, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [eval_monomial, eval_monomial, clampExp,
    Finsupp.prod_mapRange_index (fun a => pow_zero (x a))]
  congr 1
  refine Finsupp.prod_congr fun i hi => ?_
  have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp hi
  rcases hx i with h0 | h1
  · rw [h0, zero_pow (by omega : min (m i) 1 ≠ 0), zero_pow hmi]
  · rw [h1, one_pow, one_pow]

/-- **Multilinearization does not raise the total degree**: `(multilinearize p).totalDegree ≤
p.totalDegree`. Clamping each exponent to at most `1` can only shrink a monomial's degree, so the
squarefree reduction of every monomial of `p` has total degree at most that monomial's, hence at
most `p.totalDegree`. -/
theorem totalDegree_multilinearize_le (p : MvPolynomial σ R) :
    (multilinearize p).totalDegree ≤ p.totalDegree := by
  classical
  rw [multilinearize]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  refine (totalDegree_monomial_le _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum, Finsupp.sum, clampExp_support]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [id_eq, clampExp_apply]
  omega

end CommSemiring

section CommRing
variable [CommRing R]

/-- Multilinearity is preserved under subtraction. -/
theorem IsMultilinear.sub {p q : MvPolynomial σ R}
    (hp : p.IsMultilinear) (hq : q.IsMultilinear) : (p - q).IsMultilinear :=
  isMultilinear_iff_mem_restrictDegree.mpr <|
    (restrictDegree σ R 1).sub_mem
      (isMultilinear_iff_mem_restrictDegree.mp hp)
      (isMultilinear_iff_mem_restrictDegree.mp hq)

/-- **Uniqueness of the multilinear representation** (Nielsen & Chuang, Exercise 6.18): two
multilinear polynomials that agree at every point of the Boolean cube (every `x : σ → R` with each
coordinate in `{0, 1}`) are equal.

Consequently a function `{0, 1}ˢ → R` has at most one multilinear polynomial representing it; since
`Xₖ² = Xₖ` on `{0, 1}` reduces any representative to a multilinear one of no larger degree, this
multilinear representative is the minimum-degree one. -/
theorem IsMultilinear.eq_of_forall_eval_boolean {p q : MvPolynomial σ R}
    (hp : p.IsMultilinear) (hq : q.IsMultilinear)
    (h : ∀ x : σ → R, (∀ i, x i = 0 ∨ x i = 1) → eval x p = eval x q) : p = q := by
  rw [← sub_eq_zero]
  refine (hp.sub hq).eq_zero_of_forall_eval_boolean fun x hx => ?_
  rw [map_sub, sub_eq_zero]
  exact h x hx

end CommRing

end MvPolynomial
