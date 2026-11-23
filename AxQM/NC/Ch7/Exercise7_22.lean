/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.KerrAbsorptionLoss

/-!
# Nielsen & Chuang, Exercise 7.22 (cross-phase-modulation loss)

Compute the photon-absorption loss probability 1−⟨110|U|110⟩ from (7.82); compare with
1−⟨100|U|100⟩.

(N&C p. 306.) In the microscopic Kerr model (N&C §7.5.3) two polarised photon modes `a`, `b`
interact with a three-level atom; the relevant Hamiltonian is block diagonal (7.82),
`H = diag(H₀, H₁, H₂)`,
with `H₁` (7.84) the single-excitation block and `H₂` (7.85) the two-excitation block. With
`U = exp(-iHt)` the exercise asks for the photon-absorption probability of the two-photon input
`|110⟩` and its comparison with the single-photon input `|100⟩`.

The matrix element `⟨110|U|110⟩` is a complex number; the *probability that a photon is absorbed*
(what the prose defines) is the survival **probability** `|⟨110|U|110⟩|²` subtracted from `1`, i.e.
`1 - |⟨110|U|110⟩|²` — exactly the form of N&C's own single-atom absorption
`χ_r = ∑ₖ|⟨0k|U|10⟩|² = 1 - |⟨10|U|10⟩|²` (eq. 7.79). We formalise that faithful reading.

The content is a computation about complex `Matrix` data, its `NormedSpace.exp`, and
`Complex.normSq`. Compare Exercise 7.21 (`AxQM/Concrete/KerrTwoPhotonPhase.lean`).

## The formalisation

In `AxQM/Concrete/KerrAbsorptionLoss.lean` (building on the reusable `2 × 2` detuned-block
core of `AxQM/Concrete/DetunedRabiAbsorption.lean` and the two-photon amplitude of
`AxQM/Concrete/KerrTwoPhotonPhase.lean`, Exercise 7.21):

* `detunedAbsorptionLoss` — the detuned-block Lorentzian absorption profile (7.79)
  `γ(δ, g, t) = g²/(δ²+g²)·sin²(√(δ²+g²)·t)`, the shared form of both losses.
* `kerrBlockOne` — the single-excitation block `H₁` (7.84), as
  `detunedBlock δ gₐ ⊕ detunedBlock δ g_b`; `kerrBlockOne_exp_apply_zero_zero` reduces
  `⟨100|exp(zH₁)|100⟩` to the mode-`a` `2 × 2` amplitude.
* `kerrBlockTwo_exp_neg_apply_zero_zero` — the two-photon amplitude `⟨110|U|110⟩` equals the
  `detunedBlock` amplitude at the **effective coupling** `√(gₐ²+g_b²)` (`H₂`'s bright subspace).
* `kerrSinglePhotonAbsorptionProb` — **the single-photon loss**
  `1 - |⟨100|U|100⟩|² = detunedAbsorptionLoss δ gₐ t`.
* `kerrTwoPhotonAbsorptionProb` — **the two-photon loss**
  `1 - |⟨110|U|110⟩|² = detunedAbsorptionLoss δ √(gₐ²+g_b²) t`.
* `detunedAbsorptionLoss_sqrt` — the two-photon loss in explicit closed form
  `(gₐ²+g_b²)/(δ²+gₐ²+g_b²)·sin²(√(δ²+gₐ²+g_b²)·t)`.

**The comparison** (the exercise's point): both losses are the *same* profile
`detunedAbsorptionLoss δ · t`, evaluated at coupling `gₐ` (one photon) versus the larger effective
coupling `√(gₐ²+g_b²)` (two photons) — adding the second mode raises both the peak loss `g²/(δ²+g²)`
and the Rabi frequency `√(δ²+g²)`.
-/
