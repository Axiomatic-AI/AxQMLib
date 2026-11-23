/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ClassicalQueryModel
import AxQM.Concrete.ClassicalCountingIntervals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Concrete: any classical counting algorithm needs `Ω(N)` oracle calls (N&C Exercise 6.14)

Nielsen & Chuang, Exercise 6.14 (p. 262):

Query lower bound for classical counting to accuracy c√M with probability ≥ 3/4: Ω(N) oracle calls.

This is the **faithful, general** statement: a lower bound against *any* classical counting
algorithm making oracle calls, not merely against the uniform-independent *sampling* model of
Exercise 6.13. (A previous formalisation over the i.i.d. sampling model — an arbitrary estimator of
`k` independent `Bernoulli(M/N)` bits — is a strictly weaker claim, since sampling is one restricted
algorithm class; it is retired in favour of this file.)

## The model — an adaptive randomized decision tree

Any *deterministic* classical algorithm consulting a Boolean oracle `f : Fin N → Bool` is an
adaptive decision tree `QueryTree N` (`AxQM/Concrete/ClassicalQueryModel.lean`): it makes
at most `depth t` oracle calls, its output is `eval f t`, and the points it consults are `queried f
t`. A *randomized* algorithm is a probability distribution over such trees, which we bundle as a
`RandomizedCountingAlgorithm`: a probability space `(Ω, μ)`, a measurable family of trees
`alg : Ω → QueryTree N` each of `depth ≤ budget`, so the output on each oracle is a measurable
random variable whose success probability is well-defined. This is the standard, fully general model
— it subsumes both finite and continuous internal randomness — so the resulting bound holds against
every classical counting algorithm. The `budget` is the worst-case number of oracle calls, i.e. the
quantity the exercise asks to bound below.

## The argument — two-point locality + union bound + measure averaging

Fix `m := ⌈c²⌉₊ + 1`, so `c √m < m` (the accuracy at `M = m` cannot reach `0`). The hard family is
the all-`false` oracle (`M = 0`, whose accuracy `c √0 = 0` forces the estimate to be exactly `0`)
against the `N − m + 1` length-`m` interval oracles `intervalOracle m s` (`M = m`).

* **Locality.** If a tree is correct on the all-`false` oracle (`eval = 0`) and a length-`m`
  interval avoids the tree's query set `Q` (`s ∈ missStarts m Q`), then by `eval_eq_of_agree` the
  tree returns `0` on that interval oracle too — hence it is *wrong* there, because `c √m < m`.
* **Union bound.** `Q` has `≤ budget` points, so it meets at most `m · budget` intervals
  (`card_hitStarts_le`); at least `(N − m + 1) − m · budget` intervals avoid it
  (`card_missStarts_ge`). Thus for every outcome correct on all-`false`, the algorithm is wrong on
  at least that many intervals.
* **Averaging.** Integrating this pointwise count against `μ` (`counting_query_lower_bound`): with
  `wrong on all-false ≤ 1/4` and `wrong on each interval ≤ 1/4` (from success `≥ 3/4`),
  `((N − m + 1) − m · budget) · (3/4) ≤ (N − m + 1) · (1/4)`, i.e. `2 (N − m + 1) ≤ 3 m · budget`.

`counting_query_needs_linear_oracle_calls` repackages this as `Ω(N)`: for each accuracy constant
`c ≥ 0` there is `a > 0` with `a · N ≤ budget` once `N` is large enough (`2 (⌈c²⌉₊ + 1) ≤ N`) for
the hard instances to exist.

The statement of Exercise 6.14 is in `AxQM/NC/Ch6/Exercise6_14.lean`.
-/

open MeasureTheory

namespace AxQM.Concrete

/-- The **all-`false` oracle**: every index reports "not a solution" (`numSolutions = 0`). It is the
`M = 0` half of the two-point hard family. -/
def allFalse {N : ℕ} : Fin N → Bool := Function.const (Fin N) false

/-- The all-`false` oracle has no solutions. -/
lemma numSolutions_allFalse {N : ℕ} : numSolutions (allFalse : Fin N → Bool) = 0 := by
  simp [numSolutions, allFalse]

/-- **Locality at a missed interval.** If the length-`m` interval starting at `s` avoids every index
queried by `t` on the all-`false` oracle (`s ∈ missStarts m (t.queried allFalse)`), then `t` cannot
tell `intervalOracle m s` apart from `allFalse`: it returns the same estimate on both. This is the
locality lemma `eval_eq_of_agree` applied to the two oracles, which agree off the query set. -/
lemma eval_intervalOracle_eq_of_missStart {N m : ℕ} (t : QueryTree N) {s : ℕ}
    (hs : s ∈ missStarts m (t.queried allFalse)) :
    t.eval (intervalOracle m s) = t.eval allFalse := by
  apply QueryTree.eval_eq_of_agree
  intro x hx
  unfold missStarts at hs
  rw [Finset.mem_filter] at hs
  have hfalse : intervalOracle (N := N) m s x = false := hs.2 x hx
  simp [allFalse, hfalse]

/-- A **randomized classical counting algorithm** on a Boolean oracle over `Fin N`: a probability
distribution over deterministic adaptive decision trees, each making at most `budget` oracle calls.
This is the standard, fully general model of a classical algorithm consulting the oracle: the
internal randomness is an arbitrary probability space `(Ω, μ)`, and running the tree selected by the
randomness against an oracle `f` yields the estimate `(alg ω).eval f`. The measurability field makes
each such estimate a genuine random variable, so its success probability is well-defined. -/
structure RandomizedCountingAlgorithm (N : ℕ) where
  /-- The sample space of the algorithm's internal randomness. -/
  Ω : Type*
  /-- The measurable-space structure on the randomness. -/
  mΩ : MeasurableSpace Ω
  /-- The distribution over the randomness. -/
  μ : @MeasureTheory.Measure Ω mΩ
  /-- `μ` is a probability measure. -/
  isProb : @MeasureTheory.IsProbabilityMeasure Ω mΩ μ
  /-- The worst-case number of oracle calls (query budget) — the quantity the lower bound is on. -/
  budget : ℕ
  /-- The deterministic decision tree run for each value of the randomness. -/
  alg : Ω → QueryTree N
  /-- Every realised tree makes at most `budget` oracle calls. -/
  depth_le : ∀ ω, (alg ω).depth ≤ budget
  /-- For every oracle, the algorithm's output is a measurable function of the randomness, so the
  probability of any accuracy event is well-defined. -/
  measurable_eval : ∀ f : Fin N → Bool, Measurable[mΩ] (fun ω => (alg ω).eval f)

/-- The outcomes on which the algorithm's estimate for the all-`false` oracle is exactly `0` — the
only estimate the `M = 0` accuracy `c √0 = 0` permits. -/
def correctAllFalse {N : ℕ} (A : RandomizedCountingAlgorithm N) : Set A.Ω :=
  {ω | (A.alg ω).eval allFalse = 0}

/-- The outcomes on which the algorithm is **not** correct on the length-`m` interval oracle at `s`:
its estimate is farther than `c √m` from the true count `m`. -/
def wrongOnInterval {N : ℕ} (A : RandomizedCountingAlgorithm N) (m s : ℕ) (c : ℝ) : Set A.Ω :=
  {ω | ¬ |(A.alg ω).eval (intervalOracle m s) - (m : ℝ)| ≤ c * Real.sqrt m}

/-- **Exercise 6.14 (Nielsen & Chuang), quantitative core.** Any randomized classical counting
algorithm `A` that, for *every* oracle `f`, estimates its number of solutions to accuracy
`c √(numSolutions f)` with probability at least `3/4`, must have query budget `T := A.budget`
satisfying `2 (N − m + 1) ≤ 3 m · T`, where `m := ⌈c²⌉₊ + 1`. Since the right side is linear in `T`
and the left is linear in `N`, this is a linear (`Ω(N)`) lower bound on the number of oracle calls;
see `counting_query_needs_linear_oracle_calls`.

The hypothesis `⌈c²⌉₊ + 1 ≤ N` only says `N` is large enough for the hard instances to exist.

The proof pits the all-`false` oracle against the `N − m + 1` length-`m` interval oracles. By
locality (`eval_intervalOracle_eq_of_missStart`), an outcome correct on all-`false` is wrong on
every interval avoiding its query set, and the union bound (`card_missStarts_ge`) says at least
`(N − m + 1) − m · T` intervals do. Integrating this pointwise count against `A.μ` and using the two
per-oracle success bounds gives the inequality. -/
theorem counting_query_lower_bound {N : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hmN : ⌈c ^ 2⌉₊ + 1 ≤ N) (A : RandomizedCountingAlgorithm N)
    (hsucc : ∀ f : Fin N → Bool,
      3 / 4 ≤ A.μ.real {ω | |(A.alg ω).eval f - (numSolutions f : ℝ)|
        ≤ c * Real.sqrt (numSolutions f)}) :
    2 * ((N - (⌈c ^ 2⌉₊ + 1) + 1 : ℕ) : ℝ) ≤ 3 * ((⌈c ^ 2⌉₊ + 1 : ℕ) : ℝ) * (A.budget : ℝ) := by
  classical
  let : MeasurableSpace A.Ω := A.mΩ
  have : IsProbabilityMeasure A.μ := A.isProb
  set m : ℕ := ⌈c ^ 2⌉₊ + 1 with hm_def
  set T : ℕ := A.budget with hT_def
  set K : ℕ := (N - m + 1) - m * T with hK_def
  -- `c √m < m`, from `c² < m`.
  have hcm : (c : ℝ) ^ 2 < m := lt_of_le_of_lt (Nat.le_ceil _) (by rw [hm_def]; push_cast; linarith)
  have hmR_pos : (0 : ℝ) < m := lt_of_le_of_lt (sq_nonneg c) hcm
  have hc_lt : c < Real.sqrt m := (Real.lt_sqrt hc).mpr hcm
  have hcsqrt : c * Real.sqrt m < m := by
    calc c * Real.sqrt m < Real.sqrt m * Real.sqrt m :=
          mul_lt_mul_of_pos_right hc_lt (Real.sqrt_pos.mpr hmR_pos)
      _ = m := Real.mul_self_sqrt hmR_pos.le
  -- measurability of the two accuracy events.
  have hAFmeas : MeasurableSet (correctAllFalse A) := by
    have hpre : correctAllFalse A = (fun ω => (A.alg ω).eval allFalse) ⁻¹' {0} := by
      ext ω; simp [correctAllFalse]
    rw [hpre]; exact (A.measurable_eval allFalse) (measurableSet_singleton 0)
  have hWrongmeas : ∀ s, MeasurableSet (wrongOnInterval A m s c) := by
    intro s
    have hcompl : wrongOnInterval A m s c
        = ({ω | |(A.alg ω).eval (intervalOracle m s) - (m:ℝ)| ≤ c * Real.sqrt m})ᶜ := rfl
    rw [hcompl]
    exact (measurableSet_le (((A.measurable_eval (intervalOracle m s)).sub measurable_const).abs)
      measurable_const).compl
  -- correct on all-`false` with probability `≥ 3/4`.
  have hcAF : 3 / 4 ≤ A.μ.real (correctAllFalse A) := by
    have hh := hsucc allFalse
    rw [numSolutions_allFalse] at hh
    have hset : {ω | |(A.alg ω).eval allFalse - ((0:ℕ):ℝ)| ≤ c * Real.sqrt ((0:ℕ):ℝ)}
        = correctAllFalse A := by
      ext ω
      simp only [correctAllFalse, Set.mem_ofPred_eq, Nat.cast_zero, Real.sqrt_zero, mul_zero,
        sub_zero, abs_nonpos_iff]
    rwa [hset] at hh
  -- wrong on each fitting interval oracle with probability `≤ 1/4`.
  have hbad_le : ∀ s : ℕ, s + m ≤ N → A.μ.real (wrongOnInterval A m s c) ≤ 1 / 4 := by
    intro s hsm
    have hGmeas : MeasurableSet
        {ω | |(A.alg ω).eval (intervalOracle m s) - (m:ℝ)| ≤ c * Real.sqrt m} :=
      measurableSet_le (((A.measurable_eval (intervalOracle m s)).sub measurable_const).abs)
        measurable_const
    have hnum : numSolutions (intervalOracle (N:=N) m s) = m := numSolutions_intervalOracle hsm
    have hh := hsucc (intervalOracle m s)
    rw [hnum] at hh
    have hcompl : wrongOnInterval A m s c
        = ({ω | |(A.alg ω).eval (intervalOracle m s) - (m:ℝ)| ≤ c * Real.sqrt m})ᶜ := rfl
    rw [hcompl, measureReal_compl hGmeas, probReal_univ]
    linarith [hh]
  -- two-point locality: a run correct on all-`false` is wrong on every avoided interval.
  have hmiss_wrong : ∀ ω, (A.alg ω).eval allFalse = 0 →
      ∀ s ∈ missStarts m ((A.alg ω).queried allFalse), ω ∈ wrongOnInterval A m s c := by
    intro ω h0 s hs
    have heval : (A.alg ω).eval (intervalOracle m s) = (A.alg ω).eval allFalse :=
      eval_intervalOracle_eq_of_missStart (A.alg ω) hs
    change ¬ |(A.alg ω).eval (intervalOracle m s) - (m:ℝ)| ≤ c * Real.sqrt m
    rw [heval, h0, zero_sub, abs_neg, abs_of_nonneg hmR_pos.le]
    exact not_le.mpr hcsqrt
  -- pointwise count: `K · 1[correct on all-false] ≤ ∑ₛ 1[wrong on interval s]`.
  have hpoint : ∀ ω, (K : ℝ) * (correctAllFalse A).indicator (fun _ => (1:ℝ)) ω
      ≤ ∑ s ∈ Finset.range (N - m + 1), (wrongOnInterval A m s c).indicator (fun _ => (1:ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ correctAllFalse A
    · rw [Set.indicator_of_mem hω, mul_one]
      have h0 : (A.alg ω).eval allFalse = 0 := hω
      have hwrong1 : ∀ s ∈ missStarts m ((A.alg ω).queried allFalse),
          (wrongOnInterval A m s c).indicator (fun _ => (1:ℝ)) ω = 1 := fun s hs =>
        Set.indicator_of_mem (hmiss_wrong ω h0 s hs) _
      have hsub : missStarts m ((A.alg ω).queried allFalse) ⊆ Finset.range (N - m + 1) := by
        unfold missStarts; exact Finset.filter_subset _ _
      have hcard : K ≤ (missStarts m ((A.alg ω).queried allFalse)).card := by
        have hmc := card_missStarts_ge m ((A.alg ω).queried allFalse)
        have hQT : ((A.alg ω).queried allFalse).card ≤ T :=
          le_trans (QueryTree.card_queried_le_depth allFalse (A.alg ω)) (A.depth_le ω)
        have h2 : m * ((A.alg ω).queried allFalse).card ≤ m * T := Nat.mul_le_mul (le_refl m) hQT
        omega
      calc (K:ℝ) ≤ ((missStarts m ((A.alg ω).queried allFalse)).card : ℝ) := by exact_mod_cast hcard
        _ = ∑ s ∈ missStarts m ((A.alg ω).queried allFalse),
              (wrongOnInterval A m s c).indicator (fun _ => (1:ℝ)) ω := by
            rw [Finset.sum_congr rfl hwrong1, Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ s ∈ Finset.range (N - m + 1),
              (wrongOnInterval A m s c).indicator (fun _ => (1:ℝ)) ω :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun s _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    · rw [Set.indicator_of_notMem hω, mul_zero]
      exact Finset.sum_nonneg (fun s _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  -- integrate the pointwise count against `μ`.
  have hint_wrong : ∀ s, Integrable
      (fun ω => (wrongOnInterval A m s c).indicator (fun _ => (1:ℝ)) ω) A.μ :=
    fun s => (integrable_const (1:ℝ)).indicator (hWrongmeas s)
  have hint_AF : Integrable
      (fun ω => (K:ℝ) * (correctAllFalse A).indicator (fun _ => (1:ℝ)) ω) A.μ :=
    ((integrable_const (1:ℝ)).indicator hAFmeas).const_mul (K:ℝ)
  have hint_sum : Integrable
      (fun ω => ∑ s ∈ Finset.range (N - m + 1),
        (wrongOnInterval A m s c).indicator (fun _ => (1:ℝ)) ω) A.μ :=
    integrable_finsetSum _ (fun s _ => hint_wrong s)
  have hIntKey : (K:ℝ) * A.μ.real (correctAllFalse A)
      ≤ ∑ s ∈ Finset.range (N - m + 1), A.μ.real (wrongOnInterval A m s c) := by
    have hmono := integral_mono hint_AF hint_sum hpoint
    rw [integral_const_mul, integral_indicator_const (1:ℝ) hAFmeas, smul_eq_mul, mul_one,
      integral_finsetSum _ (fun s _ => hint_wrong s)] at hmono
    simp only [integral_indicator_const (1:ℝ) (hWrongmeas _), smul_eq_mul, mul_one] at hmono
    exact hmono
  -- each of the `N − m + 1` interval terms is `≤ 1/4`.
  have hUpper : ∑ s ∈ Finset.range (N - m + 1), A.μ.real (wrongOnInterval A m s c)
      ≤ ((N - m + 1 : ℕ) : ℝ) * (1 / 4) := by
    calc ∑ s ∈ Finset.range (N - m + 1), A.μ.real (wrongOnInterval A m s c)
        ≤ ∑ _s ∈ Finset.range (N - m + 1), (1 / 4 : ℝ) := by
          apply Finset.sum_le_sum
          intro s hs
          rw [Finset.mem_range] at hs
          exact hbad_le s (by omega)
      _ = ((N - m + 1 : ℕ) : ℝ) * (1 / 4) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- assemble the arithmetic: `2 (N − m + 1) ≤ 3 m T`.
  have hKnn : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  have hlow : (K:ℝ) * (3 / 4) ≤ (K:ℝ) * A.μ.real (correctAllFalse A) :=
    mul_le_mul_of_nonneg_left hcAF hKnn
  have hchain : (K:ℝ) * (3 / 4) ≤ ((N - m + 1 : ℕ) : ℝ) * (1 / 4) :=
    le_trans hlow (le_trans hIntKey hUpper)
  have h3K : 3 * (K:ℝ) ≤ ((N - m + 1 : ℕ) : ℝ) := by linarith
  have h3Knat : 3 * K ≤ N - m + 1 := by exact_mod_cast h3K
  have hfin : 2 * (N - m + 1) ≤ 3 * (m * T) := by omega
  calc (2 : ℝ) * ((N - m + 1 : ℕ) : ℝ)
      = ((2 * (N - m + 1) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((3 * (m * T) : ℕ) : ℝ) := by exact_mod_cast hfin
    _ = 3 * ((m:ℕ):ℝ) * (T:ℝ) := by push_cast; ring

/-- **Exercise 6.14 (Nielsen & Chuang), `Ω(N)` form.** For each accuracy constant `c ≥ 0` there is a
positive constant `a` (depending only on `c`) such that any randomized classical counting algorithm
correct to accuracy `c √M` with probability `≥ 3/4` for every oracle makes `a · N ≤ budget` oracle
calls, once `N` is large enough for the hard instances to exist (`2 (⌈c²⌉₊ + 1) ≤ N`). This is the
statement that any such algorithm makes `Ω(N)` oracle calls. -/
theorem counting_query_needs_linear_oracle_calls {c : ℝ} (hc : 0 ≤ c) :
    ∃ a : ℝ, 0 < a ∧ ∀ (N : ℕ) (A : RandomizedCountingAlgorithm N),
      2 * (⌈c ^ 2⌉₊ + 1) ≤ N →
      (∀ f : Fin N → Bool,
        3 / 4 ≤ A.μ.real {ω | |(A.alg ω).eval f - (numSolutions f : ℝ)|
          ≤ c * Real.sqrt (numSolutions f)}) →
      a * N ≤ A.budget := by
  refine ⟨1 / (3 * ((⌈c ^ 2⌉₊ + 1 : ℕ) : ℝ)), by positivity, ?_⟩
  intro N A hN hsucc
  set m : ℕ := ⌈c ^ 2⌉₊ + 1 with hm_def
  have hmleN : m ≤ N := by omega
  have hmN : ⌈c ^ 2⌉₊ + 1 ≤ N := by rw [← hm_def]; exact hmleN
  have hlow := counting_query_lower_bound hc hmN A hsucc
  rw [← hm_def] at hlow
  have hmR_pos : (0:ℝ) < (m:ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hcast : ((N - m + 1 : ℕ) : ℝ) = (N:ℝ) - (m:ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hmleN, Nat.cast_one]
  rw [hcast] at hlow
  have h2mN : (2:ℝ) * (m:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity : (0:ℝ) < 3 * (m:ℝ))]
  nlinarith [hlow, h2mN]

end AxQM.Concrete
