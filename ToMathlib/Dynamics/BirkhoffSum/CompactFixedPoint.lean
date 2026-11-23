/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Dynamics.BirkhoffSum.NormedSpace
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.Sequences

/-!
# A fixed-point theorem via Birkhoff averaging

A continuous linear self-map `Φ` of a nonempty, compact, convex set `s` of a real normed space
has a fixed point in `s`. This is the finite/linear content of the **Markov–Kakutani** and
Schauder fixed-point theorems, obtained by the elementary **mean-ergodic / Cesàro averaging**
argument: the Birkhoff averages `Aₙ = (1/n) ∑_{k<n} Φᵏ x₀` of a starting point stay in the
compact convex set, and any subsequential limit is a fixed point because the telescoping
difference `Φ(Aₙ) − Aₙ = (Φⁿ x₀ − x₀)/n → 0`
(`tendsto_birkhoffAverage_apply_sub_birkhoffAverage`).

## Main results

* `ContinuousLinearMap.exists_isFixedPt_of_isCompact_of_convex`: a continuous linear self-map of
  a nonempty compact convex set has a fixed point in that set.
-/

@[expose] public section

open Filter Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Markov–Kakutani fixed-point theorem for a single continuous linear map.** A continuous
linear endomorphism `Φ` of a real normed space that maps a nonempty, compact, convex set `s`
into itself has a fixed point in `s`.

The proof is the mean-ergodic / Cesàro-averaging argument. Starting from any `x₀ ∈ s`, the
Birkhoff averages `Aₙ = (1/n) ∑_{k<n} Φᵏ x₀` lie in `s` (convex combinations of the orbit
points, which stay in `s`); by compactness a subsequence converges to some `a ∈ s`; and the
telescoping estimate `Φ(Aₙ) − Aₙ = (Φⁿ x₀ − x₀)/n → 0` forces `Φ a = a` in the limit. -/
theorem exists_isFixedPt_of_isCompact_of_convex {s : Set E} (hne : s.Nonempty)
    (hcpt : IsCompact s) (hconv : Convex ℝ s) {Φ : E →L[ℝ] E} (hmaps : Set.MapsTo Φ s s) :
    ∃ x ∈ s, Φ x = x := by
  obtain ⟨x₀, hx₀⟩ := hne
  -- The forward orbit of `x₀` stays in `s`, hence is bounded.
  have horbit : ∀ k, (⇑Φ)^[k] x₀ ∈ s := fun k => hmaps.iterate k hx₀
  have hbdd : Bornology.IsBounded (Set.range fun k => id ((⇑Φ)^[k] x₀)) :=
    hcpt.isBounded.subset (Set.range_subset_iff.mpr fun k => horbit k)
  -- Each Birkhoff average of the orbit is a convex combination of orbit points, so lies in `s`.
  have hmem : ∀ n, 1 ≤ n → birkhoffAverage ℝ (⇑Φ) id n x₀ ∈ s := by
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have heq : birkhoffAverage ℝ (⇑Φ) id n x₀
        = ∑ k ∈ Finset.range n, (n : ℝ)⁻¹ • (⇑Φ)^[k] x₀ := by
      simp only [birkhoffAverage, birkhoffSum, Finset.smul_sum, id_eq]
    rw [heq]
    refine hconv.sum_mem (fun i _ => by positivity) ?_ (fun k _ => horbit k)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_inv_cancel₀ hn0]
  -- `Φ` commutes with the Birkhoff average (it is linear).
  have hmapavg : ∀ n, Φ (birkhoffAverage ℝ (⇑Φ) id n x₀)
      = birkhoffAverage ℝ (⇑Φ) id n (Φ x₀) := by
    intro n
    simp only [birkhoffAverage, birkhoffSum, id_eq, map_smul, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ =>
      (Function.iterate_succ_apply' (⇑Φ) k x₀).symm.trans (Function.iterate_succ_apply (⇑Φ) k x₀)
  -- The telescoping difference of shifted averages tends to `0`.
  have hsub : Tendsto (fun n => birkhoffAverage ℝ (⇑Φ) id n (Φ x₀)
      - birkhoffAverage ℝ (⇑Φ) id n x₀) atTop (𝓝 0) :=
    tendsto_birkhoffAverage_apply_sub_birkhoffAverage (f := ⇑Φ) (g := id) (x := x₀) ℝ hbdd
  -- Hence `Φ(A_{n+1}) − A_{n+1} → 0` for the sequence of nonempty averages.
  have hdiff : Tendsto (fun n => Φ (birkhoffAverage ℝ (⇑Φ) id (n + 1) x₀)
      - birkhoffAverage ℝ (⇑Φ) id (n + 1) x₀) atTop (𝓝 0) := by
    have hcongr : (fun n => Φ (birkhoffAverage ℝ (⇑Φ) id (n + 1) x₀)
          - birkhoffAverage ℝ (⇑Φ) id (n + 1) x₀)
        = (fun n => birkhoffAverage ℝ (⇑Φ) id n (Φ x₀)
          - birkhoffAverage ℝ (⇑Φ) id n x₀) ∘ (· + 1) := by
      funext n; simp only [Function.comp_apply, hmapavg (n + 1)]
    rw [hcongr]
    exact hsub.comp (tendsto_add_atTop_nat 1)
  -- A convergent subsequence of the averages; its limit is the fixed point.
  obtain ⟨a, ha, φ, hφ_mono, hφ_tendsto⟩ :=
    hcpt.tendsto_subseq (x := fun n => birkhoffAverage ℝ (⇑Φ) id (n + 1) x₀)
      (fun n => hmem (n + 1) (Nat.le_add_left 1 n))
  refine ⟨a, ha, ?_⟩
  have h1 : Tendsto (fun k => Φ (birkhoffAverage ℝ (⇑Φ) id (φ k + 1) x₀)
      - birkhoffAverage ℝ (⇑Φ) id (φ k + 1) x₀) atTop (𝓝 (Φ a - a)) :=
    ((Φ.continuous.tendsto a).comp hφ_tendsto).sub hφ_tendsto
  have h2 : Tendsto (fun k => Φ (birkhoffAverage ℝ (⇑Φ) id (φ k + 1) x₀)
      - birkhoffAverage ℝ (⇑Φ) id (φ k + 1) x₀) atTop (𝓝 0) :=
    hdiff.comp hφ_mono.tendsto_atTop
  have hfix := tendsto_nhds_unique h1 h2
  rwa [sub_eq_zero] at hfix

end ContinuousLinearMap
