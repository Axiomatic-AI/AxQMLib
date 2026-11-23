/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Classical fidelity between probability distributions (Nielsen & Chuang §9.1)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §9.1 (p. 400)
introduce the **fidelity** of two probability distributions `{pₓ}` and `{qₓ}`
over a common finite index set, N&C equation `(9.2)`:
```
F(pₓ, qₓ) ≡ ∑ₓ √(pₓ qₓ).
```
Geometrically this is the inner product `⟨(√pₓ), (√qₓ)⟩` of the two vectors of
coordinate-wise square roots, which lie on the unit sphere (N&C Figure 9.1); it
is also known as the Bhattacharyya coefficient. Unlike the trace distance it is
*not* a metric — N&C note that for identical distributions `F(pₓ, pₓ) = ∑ₓ pₓ = 1`
(a maximum, not a zero) — but a metric can be derived from it.

It is the classical quantity that N&C's quantum fidelity
`F(ρ, σ) = tr √(√ρ σ √ρ)` (their `(9.53)`) generalizes: for commuting
(simultaneously diagonal) states the quantum fidelity reduces to exactly this sum,
as `AxQM.Concrete.matrixFidelity_diagonal` already records.

A distribution is modelled by a real-valued family `p : ι → ℝ` on a `Fintype ι`;
the definition and its basic properties do not need the normalization `∑ₓ pₓ = 1`,
so we do not impose it globally (the concrete instances of interest are, of
course, normalized). We mirror `AxQM.Concrete.classicalTraceDist`, the
companion §9.1 quantity.

## Main definitions

* `classicalFidelity` — the fidelity `∑ₓ √(pₓ qₓ)` of `(9.2)`.

## Main statements

* `classicalFidelity_comm`, `classicalFidelity_nonneg` — symmetry
  `F(p, q) = F(q, p)` and nonnegativity `0 ≤ F(p, q)`.
* `classicalFidelity_self`, `classicalFidelity_self_eq_one` — N&C's remark that
  `F(p, p) = ∑ₓ pₓ`, hence `= 1` for a normalized distribution (fidelity is
  maximized, not minimized, by coincident distributions — it is not a metric).
* `classicalFidelity_deterministic_uniform` — **Exercise 9.3, part 1**: the
  fidelity between the deterministic distribution `(1, 0)` and the uniform
  distribution `(1/2, 1/2)` is `√2 / 2` (i.e. `1/√2`).
* `classicalFidelity_ternary_example` — **Exercise 9.3, part 2**: the fidelity
  between `(1/2, 1/3, 1/6)` and `(3/4, 1/8, 1/8)` is `(4√6 + √3) / 12`.
-/

namespace AxQM.Concrete

open scoped BigOperators

/-- The **classical fidelity** between two probability distributions
`p, q : ι → ℝ` over a finite index set, Nielsen & Chuang `(9.2)`:
`F(pₓ, qₓ) ≡ ∑ₓ √(pₓ qₓ)`. Also known as the Bhattacharyya coefficient; it is the
inner product of the vectors of coordinate-wise square roots (N&C Figure 9.1). -/
noncomputable def classicalFidelity {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ x, Real.sqrt (p x * q x)

/-- The classical fidelity is symmetric, `F(p, q) = F(q, p)`. -/
theorem classicalFidelity_comm {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    classicalFidelity p q = classicalFidelity q p := by
  simp only [classicalFidelity, mul_comm]

/-- The classical fidelity is nonnegative, `0 ≤ F(p, q)`, being a sum of square
roots (this holds for arbitrary real families, without any positivity or
normalization hypothesis). -/
theorem classicalFidelity_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    0 ≤ classicalFidelity p q :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- The fidelity of a distribution with itself is the total weight `∑ₓ pₓ`, since
`√(pₓ pₓ) = pₓ` for `pₓ ≥ 0` (N&C: `F(pₓ, pₓ) = ∑ₓ pₓ`). -/
theorem classicalFidelity_self {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ x, 0 ≤ p x) : classicalFidelity p p = ∑ x, p x :=
  Finset.sum_congr rfl fun x _ => Real.sqrt_mul_self (hp x)

/-- For a normalized distribution the self-fidelity is `1` (N&C: `F(pₓ, pₓ) = 1`),
witnessing that the fidelity is *maximized* — not zeroed — by coincident
distributions, so it is not a metric. -/
theorem classicalFidelity_self_eq_one {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) : classicalFidelity p p = 1 := by
  rw [classicalFidelity_self hp, hsum]

/-- `√(b / c²) = √b / c` for nonnegative `b` and `c`. A small reusable helper for
evaluating square roots of rationals: rewrite the radicand as `b / c²` and this
lemma reads off the closed form. -/
theorem sqrt_div_sq {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (b / c ^ 2) = Real.sqrt b / c := by
  rw [Real.sqrt_div hb, Real.sqrt_sq hc]

/-- **Nielsen & Chuang, Exercise 9.3 (part 1).** The fidelity between the
deterministic distribution `(1, 0)` and the uniform distribution `(1/2, 1/2)` is
`√2 / 2` (equivalently `1/√2`): `√(1·½) + √(0·½) = √(1/2) + 0 = √2 / 2`. -/
theorem classicalFidelity_deterministic_uniform :
    classicalFidelity ![1, 0] ![1 / 2, 1 / 2] = Real.sqrt 2 / 2 := by
  simp only [classicalFidelity, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (1 : ℝ) * (1 / 2) = 2 / 2 ^ 2 by norm_num, show (0 : ℝ) * (1 / 2) = 0 by norm_num,
    Real.sqrt_zero, add_zero, sqrt_div_sq (by norm_num) (by norm_num)]

/-- **Nielsen & Chuang, Exercise 9.3 (part 2).** The fidelity between
`(1/2, 1/3, 1/6)` and `(3/4, 1/8, 1/8)` is `(4√6 + √3) / 12`:
`√(3/8) + √(1/24) + √(1/48) = √6/4 + √6/12 + √3/12 = (4√6 + √3)/12 ≈ 0.9608`. -/
theorem classicalFidelity_ternary_example :
    classicalFidelity ![1 / 2, 1 / 3, 1 / 6] ![3 / 4, 1 / 8, 1 / 8]
      = (4 * Real.sqrt 6 + Real.sqrt 3) / 12 := by
  simp only [classicalFidelity, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [show (1 : ℝ) / 2 * (3 / 4) = 6 / 4 ^ 2 by norm_num, sqrt_div_sq (by norm_num) (by norm_num),
    show (1 : ℝ) / 3 * (1 / 8) = 6 / 12 ^ 2 by norm_num, sqrt_div_sq (by norm_num) (by norm_num),
    show (1 : ℝ) / 6 * (1 / 8) = 3 / 12 ^ 2 by norm_num, sqrt_div_sq (by norm_num) (by norm_num)]
  ring

end AxQM.Concrete
