/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Classical trace distance between probability distributions (Nielsen & Chuang §9.1)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §9.1 (p. 400)
introduce the **trace distance** (a.k.a. the `L¹` or Kolmogorov distance)
between two probability distributions `{pₓ}` and `{qₓ}` over a common finite
index set, N&C equation `(9.1)`:
```
D(pₓ, qₓ) ≡ ½ ∑ₓ |pₓ − qₓ|.
```
It is the classical quantity that the quantum trace
distance `½ tr|ρ − σ|` (N&C `(9.11)`) generalizes, and it is reused by several
Chapter 9 items (Exercises 9.1, 9.2, 9.4).

A distribution is modelled by a real-valued family `p : ι → ℝ` on a `Fintype ι`;
the definition and its basic properties do not need the normalization `∑ₓ pₓ = 1`,
so we do not impose it here (the concrete instances of interest are, of course,
normalized).

## Main definitions

* `classicalTraceDist` — the trace distance `½ ∑ₓ |pₓ − qₓ|` of `(9.1)`.

## Main statements

* `classicalTraceDist_self`, `classicalTraceDist_comm`, `classicalTraceDist_nonneg`
  — the basic "distance" properties N&C invoke in justifying the term *distance*
  (`D(x, x) = 0`, symmetry `D(x, y) = D(y, x)`, and nonnegativity).
* `classicalTraceDist_deterministic_uniform` — **Exercise 9.1, part 1**: the
  trace distance between the deterministic distribution `(1, 0)` and the uniform
  distribution `(1/2, 1/2)` is `1/2`.
* `classicalTraceDist_ternary_example` — **Exercise 9.1, part 2**: the trace
  distance between `(1/2, 1/3, 1/6)` and `(3/4, 1/8, 1/8)` is `1/4`.
* `classicalTraceDist_binary` — **Exercise 9.2**: the trace distance between the
  two-outcome distributions `(p, 1 − p)` and `(q, 1 − q)` is `|p − q|`, for
  arbitrary real parameters `p` and `q`.
* `classicalTraceDist_eq_sum_posPart` — for equal-total-mass `p, q`, the trace
  distance equals `∑ₓ (pₓ − qₓ)⁺` (the algebraic core of Exercise 9.4).
* `sum_sub_sum_le_classicalTraceDist`, `abs_sum_sub_sum_le_classicalTraceDist`,
  `exists_finset_sum_sub_eq_classicalTraceDist` — the one-sided / two-sided bound
  and the attainment that assemble Exercise 9.4.
* `classicalTraceDist_isGreatest` (and its probability-distribution corollary
  `classicalTraceDist_isGreatest_of_sum_eq_one`) — **Exercise 9.4**, N&C `(9.3)`:
  `D(p, q) = max_S |p(S) − q(S)|`, the maximum over all events `S` of the gap in
  the probability assigned to `S`.
* `classicalTraceDist_isGreatest_sub` (and its probability-distribution corollary
  `classicalTraceDist_isGreatest_sub_of_sum_eq_one`) — **Exercise 9.5**, N&C
  `(9.4)`: the absolute value signs may be removed, `D(p, q) = max_S (p(S) − q(S))`,
  because the optimal event `S⁺ = {x | pₓ ≥ qₓ}` already makes the gap nonnegative.
-/

namespace AxQM.Concrete

open scoped BigOperators

/-- The **classical trace distance** between two probability distributions
`p, q : ι → ℝ` over a finite index set, Nielsen & Chuang `(9.1)`:
`D(pₓ, qₓ) ≡ ½ ∑ₓ |pₓ − qₓ|`. Also known as the `L¹` or Kolmogorov distance. -/
noncomputable def classicalTraceDist {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  (∑ x, |p x - q x|) / 2

/-- The classical trace distance of a distribution from itself is `0`
(N&C: a metric satisfies `D(x, x) = 0`). -/
theorem classicalTraceDist_self {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    classicalTraceDist p p = 0 := by
  simp [classicalTraceDist]

/-- The classical trace distance is symmetric, `D(p, q) = D(q, p)`
(N&C: a metric must be symmetric). -/
theorem classicalTraceDist_comm {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    classicalTraceDist p q = classicalTraceDist q p := by
  simp only [classicalTraceDist, abs_sub_comm]

/-- The classical trace distance is nonnegative, `0 ≤ D(p, q)`. -/
theorem classicalTraceDist_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    0 ≤ classicalTraceDist p q :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

/-- **Nielsen & Chuang, Exercise 9.1 (part 1).** The trace distance between the
deterministic distribution `(1, 0)` and the uniform distribution `(1/2, 1/2)` is
`1/2`: `½(|1 − 1/2| + |0 − 1/2|) = ½(1/2 + 1/2) = 1/2`. -/
theorem classicalTraceDist_deterministic_uniform :
    classicalTraceDist ![1, 0] ![1 / 2, 1 / 2] = 1 / 2 := by
  simp [classicalTraceDist, Fin.sum_univ_two]
  norm_num

/-- **Nielsen & Chuang, Exercise 9.1 (part 2).** The trace distance between
`(1/2, 1/3, 1/6)` and `(3/4, 1/8, 1/8)` is `1/4`:
`½(|1/2 − 3/4| + |1/3 − 1/8| + |1/6 − 1/8|) = ½(1/4 + 5/24 + 1/24) = ½·(1/2) = 1/4`. -/
theorem classicalTraceDist_ternary_example :
    classicalTraceDist ![1 / 2, 1 / 3, 1 / 6] ![3 / 4, 1 / 8, 1 / 8] = 1 / 4 := by
  simp [classicalTraceDist, Fin.sum_univ_three]
  norm_num

/-- **Nielsen & Chuang, Exercise 9.2.** The trace distance between the two-outcome
distributions `(p, 1 − p)` and `(q, 1 − q)` is `|p − q|`, for arbitrary real
parameters `p q : ℝ`. The second summand collapses onto the first because the two
outcomes' deviations are equal and opposite:
`½(|p − q| + |(1 − p) − (1 − q)|) = ½(|p − q| + |q − p|) = ½(2|p − q|) = |p − q|`. -/
theorem classicalTraceDist_binary (p q : ℝ) :
    classicalTraceDist ![p, 1 - p] ![q, 1 - q] = |p - q| := by
  have h : (1 - p) - (1 - q) = -(p - q) := by ring
  simp only [classicalTraceDist, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, h, abs_neg]
  ring

/-- **Positive-part form of the trace distance** (the algebraic core of
Exercise 9.4). When `p` and `q` have equal total mass — in particular when both
are probability distributions, `∑ₓ pₓ = ∑ₓ qₓ = 1` — the trace distance equals
the sum of the positive parts of the pointwise differences:
`D(p, q) = ½ ∑ₓ |pₓ − qₓ| = ∑ₓ (pₓ − qₓ)⁺`.
Since the differences sum to zero, the positive and negative parts have equal
total, so each is half of `∑ₓ |pₓ − qₓ|`. -/
theorem classicalTraceDist_eq_sum_posPart {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (h : ∑ x, p x = ∑ x, q x) :
    classicalTraceDist p q = ∑ x, (p x - q x)⁺ := by
  have hsum : ∑ x, (p x - q x) = 0 := by rw [Finset.sum_sub_distrib, h, sub_self]
  have e1 : ∑ x, |p x - q x| = (∑ x, (p x - q x)⁺) + ∑ x, (p x - q x)⁻ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [add_comm]; exact (negPart_add_posPart _).symm
  have e2 : (0 : ℝ) = (∑ x, (p x - q x)⁺) - ∑ x, (p x - q x)⁻ := by
    rw [← Finset.sum_sub_distrib, ← hsum]
    exact Finset.sum_congr rfl fun x _ => (posPart_sub_negPart _).symm
  have key : ∑ x, (p x - q x)⁺ = ∑ x, (p x - q x)⁻ := by linarith
  unfold classicalTraceDist
  rw [e1, key]; ring

/-- **One-sided distinguishability bound** (Exercise 9.4). For any event
`S ⊆ {x}` and distributions of equal total mass, the excess probability that `S`
receives under `p` over `q`, `p(S) − q(S) = ∑_{x∈S} pₓ − ∑_{x∈S} qₓ`, is at most
the trace distance `D(p, q)`. The bound is saturated by the event where `p ≥ q`;
see `exists_finset_sum_sub_eq_classicalTraceDist`. -/
theorem sum_sub_sum_le_classicalTraceDist {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (h : ∑ x, p x = ∑ x, q x) (S : Finset ι) :
    (∑ x ∈ S, p x) - (∑ x ∈ S, q x) ≤ classicalTraceDist p q := by
  rw [classicalTraceDist_eq_sum_posPart h, ← Finset.sum_sub_distrib]
  calc ∑ x ∈ S, (p x - q x) ≤ ∑ x ∈ S, (p x - q x)⁺ :=
        Finset.sum_le_sum fun x _ => le_posPart _
    _ ≤ ∑ x, (p x - q x)⁺ := Finset.sum_le_univ_sum_of_nonneg fun x => posPart_nonneg _

/-- **Two-sided distinguishability bound** (Exercise 9.4). For any event
`S ⊆ {x}`, the absolute gap `|p(S) − q(S)|` between the probabilities `S`
receives under `p` and `q` is at most the trace distance `D(p, q)`. The lower
direction follows from the one-sided bound applied to the swapped pair, using
symmetry of the trace distance (`classicalTraceDist_comm`). -/
theorem abs_sum_sub_sum_le_classicalTraceDist {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (h : ∑ x, p x = ∑ x, q x) (S : Finset ι) :
    |(∑ x ∈ S, p x) - (∑ x ∈ S, q x)| ≤ classicalTraceDist p q := by
  rw [abs_le]
  refine ⟨?_, sum_sub_sum_le_classicalTraceDist h S⟩
  have hswap := sum_sub_sum_le_classicalTraceDist h.symm S
  rw [classicalTraceDist_comm q p] at hswap
  linarith

/-- **Attainment of the trace distance by an optimal event** (Exercise 9.4). For
distributions of equal total mass there is a subset `S` — the set of indices
where `p ≥ q` — whose signed probability excess equals the trace distance
exactly, `p(S) − q(S) = D(p, q)`. Combined with the two-sided bound this exhibits
`D(p, q)` as the maximum of `|p(S) − q(S)|`. (This absolute-value-free attainment
is also the content of Exercise 9.5.) -/
theorem exists_finset_sum_sub_eq_classicalTraceDist {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (h : ∑ x, p x = ∑ x, q x) :
    ∃ S : Finset ι, (∑ x ∈ S, p x) - (∑ x ∈ S, q x) = classicalTraceDist p q := by
  classical
  refine ⟨Finset.univ.filter fun x => q x ≤ p x, ?_⟩
  rw [classicalTraceDist_eq_sum_posPart h, ← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => q x ≤ p x)
      fun x => (p x - q x)⁺]
  have hpos : ∑ x ∈ Finset.univ.filter (fun x => q x ≤ p x), (p x - q x) =
      ∑ x ∈ Finset.univ.filter (fun x => q x ≤ p x), (p x - q x)⁺ :=
    Finset.sum_congr rfl fun x hx => by
      simp only [Finset.mem_filter] at hx; rw [posPart_eq_self.2 (by linarith [hx.2])]
  have hneg : ∑ x ∈ Finset.univ.filter (fun x => ¬ q x ≤ p x), (p x - q x)⁺ = 0 :=
    Finset.sum_eq_zero fun x hx => by
      simp only [Finset.mem_filter, not_le] at hx; rw [posPart_eq_zero.2 (by linarith [hx.2])]
  rw [hpos, hneg, add_zero]

/-- **Nielsen & Chuang, Exercise 9.4** — equation `(9.3)`. For two distributions
`p, q : ι → ℝ` of equal total mass (probability distributions in particular), the
trace distance is the greatest value of `|p(S) − q(S)|` over all events
`S ⊆ {x}`:
`D(p, q) = max_S |p(S) − q(S)| = max_S |∑_{x∈S} pₓ − ∑_{x∈S} qₓ|`.
The event `S` is the optimal test for distinguishing `p` from `q`, with the trace
distance governing how well the distinction can be made. `IsGreatest` packages
both halves of `(9.3)`: `D(p, q)` is attained (by the event where `p ≥ q`) and is
an upper bound over all events. -/
theorem classicalTraceDist_isGreatest {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (h : ∑ x, p x = ∑ x, q x) :
    IsGreatest (Set.range fun S : Finset ι => |(∑ x ∈ S, p x) - (∑ x ∈ S, q x)|)
      (classicalTraceDist p q) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hS⟩ := exists_finset_sum_sub_eq_classicalTraceDist h
    exact ⟨S, by simp only [hS, abs_of_nonneg (classicalTraceDist_nonneg p q)]⟩
  · rintro _ ⟨S, rfl⟩
    exact abs_sum_sub_sum_le_classicalTraceDist h S

/-- **Nielsen & Chuang, Exercise 9.4** for probability distributions. Specializing
`classicalTraceDist_isGreatest` to genuine probability distributions `p, q` (each
summing to `1`), the trace distance is the maximum over events `S` of the gap
`|p(S) − q(S)|` in the probability assigned to `S`, N&C `(9.3)`. -/
theorem classicalTraceDist_isGreatest_of_sum_eq_one {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) :
    IsGreatest (Set.range fun S : Finset ι => |(∑ x ∈ S, p x) - (∑ x ∈ S, q x)|)
      (classicalTraceDist p q) :=
  classicalTraceDist_isGreatest (hp.trans hq.symm)

/-- **Nielsen & Chuang, Exercise 9.5** — equation `(9.4)`. The absolute value
signs may be removed from `(9.3)`: for two distributions `p, q : ι → ℝ` of equal
total mass, the trace distance is the greatest value of the *signed* gap
`p(S) − q(S)` over all events `S ⊆ {x}`:
`D(p, q) = max_S (p(S) − q(S)) = max_S (∑_{x∈S} pₓ − ∑_{x∈S} qₓ)`.
Removing the absolute value cannot lower the maximum (the signed gap is bounded
above by `|p(S) − q(S)| ≤ D(p, q)`), and the bound is still attained — by the very
same optimal event `S⁺ = {x | pₓ ≥ qₓ}`, whose signed gap is already the
nonnegative value `D(p, q)` (`exists_finset_sum_sub_eq_classicalTraceDist`). So
the two maxima coincide. `IsGreatest` packages both halves: `D(p, q)` is attained
and is an upper bound, now over the signed gaps rather than their absolute
values. -/
theorem classicalTraceDist_isGreatest_sub {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (h : ∑ x, p x = ∑ x, q x) :
    IsGreatest (Set.range fun S : Finset ι => (∑ x ∈ S, p x) - (∑ x ∈ S, q x))
      (classicalTraceDist p q) := by
  refine ⟨exists_finset_sum_sub_eq_classicalTraceDist h, ?_⟩
  rintro _ ⟨S, rfl⟩
  exact sum_sub_sum_le_classicalTraceDist h S

/-- **Nielsen & Chuang, Exercise 9.5** for probability distributions. Specializing
`classicalTraceDist_isGreatest_sub` to genuine probability distributions `p, q`
(each summing to `1`), the trace distance is the maximum over events `S` of the
signed gap `p(S) − q(S)` in the probability assigned to `S`, N&C `(9.4)`. -/
theorem classicalTraceDist_isGreatest_sub_of_sum_eq_one {ι : Type*} [Fintype ι]
    {p q : ι → ℝ} (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) :
    IsGreatest (Set.range fun S : Finset ι => (∑ x ∈ S, p x) - (∑ x ∈ S, q x))
      (classicalTraceDist p q) :=
  classicalTraceDist_isGreatest_sub (hp.trans hq.symm)

end AxQM.Concrete
