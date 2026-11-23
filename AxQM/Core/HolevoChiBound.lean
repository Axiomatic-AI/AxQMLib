/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.HolevoChi

/-!
# AxQM — the Holevo χ quantity is bounded by the entropy of the mixture

The Holevo χ quantity `χ = S(∑ᵢ pᵢ ρᵢ) − ∑ᵢ pᵢ S(ρᵢ)` of an ensemble is at most the von Neumann
entropy of the mixture, because the average component entropy `∑ᵢ pᵢ S(ρᵢ)` is non-negative
(each `S(ρᵢ) ≥ 0` and each `pᵢ ≥ 0`). This is the first half of the standard chain
`χ ≤ S(∑ᵢ pᵢ ρᵢ) ≤ log d` bounding χ by the log of the Hilbert-space dimension — the argument of
Nielsen & Chuang's Exercise 12.3.

## Main results

* `AxQM.State.holevoChi_le_vonNeumannEntropy_mix` — `χ({pᵢ, ρᵢ}) ≤ S(∑ᵢ pᵢ ρᵢ)`.
-/

namespace AxQM.State

variable {S : AxQM.QSystem} {ι : Type*} [Fintype ι]

/-- **The Holevo χ quantity is at most the entropy of the mixture**: for an ensemble `{pᵢ, ρᵢ}`,
`χ({pᵢ, ρᵢ}) ≤ S(∑ᵢ pᵢ ρᵢ)`. Since `χ = S(∑ᵢ pᵢ ρᵢ) − ∑ᵢ pᵢ S(ρᵢ)` and the subtracted average
component entropy `∑ᵢ pᵢ S(ρᵢ)` is non-negative (each `pᵢ ≥ 0` and `S(ρᵢ) ≥ 0`), χ can only be
smaller than `S(∑ᵢ pᵢ ρᵢ)`. -/
theorem holevoChi_le_vonNeumannEntropy_mix (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (ρ : ι → State S) :
    holevoChi p hp hsum ρ ≤ (mix p hp hsum ρ).vonNeumannEntropy := by
  rw [holevoChi_def]
  have hnonneg : 0 ≤ ∑ i, p i * (ρ i).vonNeumannEntropy :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (ρ i).vonNeumannEntropy_nonneg
  linarith

end AxQM.State
