/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# `qaryEntropy` unfolding lemma

Extends `Mathlib.Analysis.SpecialFunctions.BinaryEntropy` with the defining decomposition lemma
for `Real.qaryEntropy`.

`Real.qaryEntropy` is defined upstream as exactly `p * log (q - 1 : ℤ) + binEntropy p`, but the
definition is not `@[expose]`d, so its body is opaque across the module boundary from this file:
neither `rfl`, `unfold qaryEntropy`, nor `simp [qaryEntropy]` can unfold it here. Marking the
upstream def `@[expose]` would need a change to Mathlib itself. Instead,
`qaryEntropy_eq_log_add_binEntropy` is proved
analytically purely from the public API: both sides are continuous everywhere, agree at `p = 0`
and `p = 1` (`qaryEntropy_zero`/`_one`, `binEntropy_zero`/`_one`), and have equal derivatives away
from `0`/`1` (`hasDerivAt_qaryEntropy`, `hasDerivAt_binEntropy`), so they agree on each of the open
intervals `Iio 0`, `Ioo 0 1`, `Ioi 1` by the mean-value corollary
`IsOpen.exists_eq_add_of_deriv_eq`, with the additive shift pinned to `0` by taking the limit
towards the shared boundary point and using continuity there.
-/

public section

namespace Real

open Filter Topology Set

/-- Helper for `qaryEntropy_eq_log_add_binEntropy`: on a connected open set `s` all of whose points
are `≠ 0` and `≠ 1`, and along whose boundary point `b` (in the sense of a nontrivial `𝓝[s] b`) the
two sides agree, `qaryEntropy q` and `p ↦ p * log (q - 1) + binEntropy p` agree throughout `s`. The
two functions have equal derivatives on `s` (both `log (q - 1) + log (1 - p) - log p`), so they
differ on `s` by a fixed additive constant (`IsOpen.exists_eq_add_of_deriv_eq`); continuity of both
sides at `b`, together with the hypothesis that they already agree at `b`, forces that constant to
be `0`. -/
private lemma qaryEntropy_eqOn_add_binEntropy_of_boundary (q : ℕ) {s : Set ℝ} {b : ℝ}
    (hs : IsOpen s) (hs' : IsPreconnected s) (hbne : (𝓝[s] b).NeBot)
    (hmem : ∀ p ∈ s, p ≠ 0 ∧ p ≠ 1)
    (hb : qaryEntropy q b = b * log (q - 1 : ℤ) + binEntropy b) :
    s.EqOn (qaryEntropy q) (fun p => p * log (q - 1 : ℤ) + binEntropy p) := by
  have := hbne
  have hlogcast : log ((q : ℝ) - 1) = log (q - 1 : ℤ) := by
    congr 1; push_cast; ring
  have hgc : Continuous (fun p : ℝ => p * log (q - 1 : ℤ) + binEntropy p) := by fun_prop
  have hf : DifferentiableOn ℝ (qaryEntropy q) s := fun p hp =>
    (differentiableAt_qaryEntropy (hmem p hp).1 (hmem p hp).2).differentiableWithinAt
  have hg : DifferentiableOn ℝ (fun p => p * log (q - 1 : ℤ) + binEntropy p) s := fun p hp =>
    (((hasDerivAt_id' (x := p)).mul_const (log (q - 1 : ℤ))).add
      (hasDerivAt_binEntropy (hmem p hp).1 (hmem p hp).2)).differentiableAt.differentiableWithinAt
  have hderiv : s.EqOn (deriv (qaryEntropy q))
      (deriv (fun p => p * log (q - 1 : ℤ) + binEntropy p)) := by
    intro p hp
    have h0 := (hmem p hp).1
    have h1 := (hmem p hp).2
    have hf' : HasDerivAt (qaryEntropy q) (log (q - 1) + log (1 - p) - log p) p :=
      hasDerivAt_qaryEntropy h0 h1
    have hg' : HasDerivAt (fun p => p * log (q - 1 : ℤ) + binEntropy p)
        (1 * log (q - 1 : ℤ) + (log (1 - p) - log p)) p :=
      ((hasDerivAt_id' (x := p)).mul_const (log (q - 1 : ℤ))).add
        (hasDerivAt_binEntropy h0 h1)
    rw [hf'.deriv, hg'.deriv, hlogcast]
    ring
  obtain ⟨a, ha⟩ := hs.exists_eq_add_of_deriv_eq hs' hf hg hderiv
  have htf : Tendsto (qaryEntropy q) (𝓝[s] b) (𝓝 (qaryEntropy q b)) :=
    qaryEntropy_continuous.continuousAt.continuousWithinAt
  have htg : Tendsto (fun p => (p * log (q - 1 : ℤ) + binEntropy p) + a) (𝓝[s] b)
      (𝓝 ((b * log (q - 1 : ℤ) + binEntropy b) + a)) :=
    (hgc.continuousAt.continuousWithinAt).add tendsto_const_nhds
  have heq : (qaryEntropy q) =ᶠ[𝓝[s] b]
      (fun p => (p * log (q - 1 : ℤ) + binEntropy p) + a) :=
    Filter.eventually_of_mem self_mem_nhdsWithin ha
  have hlim := tendsto_nhds_unique_of_eventuallyEq htf htg heq
  have ha0 : a = 0 := by rw [hb] at hlim; linarith
  intro p hp
  have := ha hp
  rw [ha0] at this
  simpa using this

/-- The defining decomposition of `qaryEntropy` as the `log (q - 1)` term plus the binary
entropy, mirroring `binEntropy_eq_negMulLog_add_negMulLog_one_sub`. -/
lemma qaryEntropy_eq_log_add_binEntropy (q : ℕ) (p : ℝ) :
    qaryEntropy q p = p * log (q - 1 : ℤ) + binEntropy p := by
  have hb0 : qaryEntropy q 0 = 0 * log (q - 1 : ℤ) + binEntropy 0 := by simp
  have hb1 : qaryEntropy q 1 = 1 * log (q - 1 : ℤ) + binEntropy 1 := by simp
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · exact qaryEntropy_eqOn_add_binEntropy_of_boundary q isOpen_Iio
      (convex_Iio 0).isPreconnected (b := 0) inferInstance
      (fun p hp => ⟨hp.ne, hp.trans_le zero_le_one |>.ne⟩) hb0 (show p ∈ Iio (0 : ℝ) from hp)
  · exact hb0
  rcases lt_trichotomy p 1 with hp1 | rfl | hp1
  · exact qaryEntropy_eqOn_add_binEntropy_of_boundary q isOpen_Ioo
      (convex_Ioo 0 1).isPreconnected (b := 0) (left_nhdsWithin_Ioo_neBot (by norm_num))
      (fun p hp => ⟨hp.1.ne', hp.2.ne⟩) hb0 (show p ∈ Ioo (0 : ℝ) 1 from ⟨hp, hp1⟩)
  · exact hb1
  · exact qaryEntropy_eqOn_add_binEntropy_of_boundary q isOpen_Ioi
      (convex_Ioi 1).isPreconnected (b := 1) inferInstance
      (fun p hp => ⟨(zero_lt_one.trans hp).ne', hp.ne'⟩) hb1 (show p ∈ Ioi (1 : ℝ) from hp1)

end Real
