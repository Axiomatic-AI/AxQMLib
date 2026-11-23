/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.LogicalLabelingCapacity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The NMR `J`-coupling multiplet: line count and relative magnitudes (Nielsen & Chuang, Ex. 7.37)

The **second half** of Nielsen & Chuang Exercise 7.37 (§7.7, p. 329): for the Hamiltonian
`H = J Z₁(Z₂ + ⋯ + Z_{n+1})` — the observed spin `1` `J`-coupled to `n` *equivalent* neighbour spins
— *how many lines appear in the spectrum of the first spin, and what are their relative magnitudes?*
For the exercise's case `n = 3` (`H = J Z₁(Z₂+Z₃+Z₄)`) the answer is the famous **quartet with
relative magnitudes `1 : 3 : 3 : 1`**.

## The physics

The free-induction-decay signal of spin `1` (N&C eq. 7.143, `k = 1`) is
`V(t) = V₀ tr[e^{-iHt} ρ e^{iHt} (i X₁ + Y₁)]`. As in the coupled-*pair* case
(`Postulates/API/NMRCoupledSpinFIDSignal.lean`, the `H = J Z₁Z₂` half, giving the doublet
`V(t) = i V₀ βℏω₀ cos(2Jt)`), the Heisenberg-evolved readout of spin `1` precesses under the
collective neighbour field. The three couplings `J Z₁Z_k` commute, so the propagator factors
and the readout picks up one precession factor `cos(2Jt) − i sin(2Jt) Z_k` per neighbour:
`e^{iHt}(iX₁+Y₁)e^{-iHt} = (iX₁+Y₁) ∏_k (cos(2Jt) − i sin(2Jt) Z_k)`. Only the `X₁` term of the
`π/2`-pulsed thermal state `ρ` survives the trace (as in the pair case), and Hilbert–Schmidt
orthogonality then gives

> `V(t) = i V₀ βℏω₀ · cos^n(2Jt)`   (for `n` equivalent neighbours).

The spectrum is the Fourier transform of `cos^n(2Jt)`. Grouping the `2ⁿ` neighbour spin
configurations by the eigenvalue of the collective field `Z₂ + ⋯ + Z_{n+1}` — which is exactly the
magnetization `n − 2w` of the `n`-neighbour computational basis state of Hamming weight `w`
(`AxQM.Concrete.magPop`, shared with Ex. 7.44) — each distinct field value is one spectral
**line**, and the number of configurations giving that value (the binomial degeneracy `C(n, w)`) is
its **relative magnitude**. Hence:

* the neighbour field takes `n + 1` distinct values `n, n−2, …, −n` — so there are **`n + 1` lines**
  (for `n = 3`: fields `{3, 1, −1, −3}`, i.e. frequencies `{±6J, ±2J}`, **4 lines**);
* the line at field value `n − 2w` has multiplicity `C(n, w)` — so the **relative magnitudes are the
  binomial coefficients** (for `n = 3`: `C(3,·) = 1 : 3 : 3 : 1`).

## What is proved

Modelling a neighbour configuration `|z₂…z_{n+1}⟩` by the `Finset (Fin n)` of its spin-`|1⟩`
positions (reusing `magPop n A = n − 2·|A|`, the eigenvalue of `Z₂ + ⋯ + Z_{n+1}`):

* `nmrMultiplet_degeneracy` — for any `n`, the number of configurations of Hamming weight `w` is
  `C(n, w)` (`Finset.card_powersetCard`); `nmrMultiplet_lineMagnitude` restates this physically: the
  spectral line at collective-field value `n − 2w` has multiplicity `C(n, w)`.
* `nmrQuartet_lines` / `nmrQuartet_lineCount` — for `n = 3` the collective field takes the four
  values `{3, 1, −1, −3}`: **four lines**.
* `nmrQuartet_relativeMagnitudes` — the four lines (fields `3, 1, −1, −3`) have multiplicities
  `1, 3, 3, 1`.
* `cos_cube` — the trigonometric Fourier decomposition `cos³θ = ¼cos 3θ + ¾cosθ` behind the quartet
  (`θ = 2Jt`): frequencies `3θ = 6Jt` and `θ = 2Jt` with amplitudes `¼ : ¾ = 1 : 3` — the outer and
  inner line pairs of the `1 : 3 : 3 : 1` quartet.
* `nmrQuartet_fourier` — the config-sum form tying the two together: summing one cosine line per
  neighbour configuration, `∑_A cos(magPop 3 A · θ) = 2cos 3θ + 6cosθ` (`= 8cos³θ`), so the
  `1 : 3 : 3 : 1` degeneracies are exactly the Fourier amplitudes of the four lines.

## Scope

"How many lines / what relative magnitudes" is a combinatorial statement about the eigenvalue
multiplicities of the neighbour field `Z₂ + ⋯ + Z_{n+1}` and the Fourier content of `cos^n`. The
declarations are over `Finset (Fin n)`, `ℤ`, `ℕ.choose`, and `Real.cos`. The statement of
Exercise 7.37 (`AxQM/NC/Ch7/Exercise7_37.lean`) points to these and to the coupled-pair physics of
the first half. Compare the NMR exercise 7.44 (`AxQM/Concrete/LogicalLabelingCapacity.lean`),
whose `magPop` it reuses.

## Fidelity

N&C ask for the number of lines and their relative magnitudes; both are pinned exactly — `n + 1`
lines at the `n + 1` distinct collective-field values, with the exact binomial multiplicities
`C(n, w)` (for the exercise's `n = 3`: four lines, `1 : 3 : 3 : 1`). The `cos^n` Fourier signature
(`cos_cube`, `nmrQuartet_fourier`) records the same magnitudes as the amplitudes physically observed
in `V(t) ∝ cos^n(2Jt)`, continuous with the coupled-pair doublet `V(t) = i V₀ βℏω₀ cos(2Jt)` of the
first half.
-/

namespace AxQM.Concrete

open scoped BigOperators

/-- **Binomial degeneracy of the multiplet.** For a spin `J`-coupled to `n` equivalent neighbour
spins, the number of neighbour computational-basis configurations of Hamming weight `w` — modelled
by the `Finset (Fin n)` of spin-`|1⟩` positions — is `C(n, w) = n.choose w`. These are the
configurations sharing one collective-field value `n − 2w`, hence the *relative magnitude* of the
corresponding spectral line. -/
theorem nmrMultiplet_degeneracy (n w : ℕ) :
    (Finset.univ.filter (fun A : Finset (Fin n) => A.card = w)).card = n.choose w := by
  rw [← Finset.powerset_univ, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]

/-- **Relative magnitude of a multiplet line (physical form).** The spectral line of spin `1` at
collective neighbour-field value `n − 2w` (the eigenvalue of `Z₂ + ⋯ + Z_{n+1}` on weight-`w`
configurations, `magPop n`) has multiplicity `C(n, w) = n.choose w`. Same content as
`nmrMultiplet_degeneracy`, read off the field value rather than the Hamming weight. -/
theorem nmrMultiplet_lineMagnitude (n w : ℕ) :
    (Finset.univ.filter (fun A : Finset (Fin n) => magPop n A = (n : ℤ) - 2 * w)).card
      = n.choose w := by
  rw [← nmrMultiplet_degeneracy]
  congr 1
  refine Finset.filter_congr (fun A _ => ?_)
  simp only [magPop]
  omega

/-- **The four lines of the `n = 3` multiplet (Ex. 7.37, `H = J Z₁(Z₂+Z₃+Z₄)`).** The collective
neighbour field `Z₂ + Z₃ + Z₄ = magPop 3` takes exactly the four values `{3, 1, −1, −3}` — the
frequencies `{±6J, ±2J}` of the spin-`1` quartet. -/
theorem nmrQuartet_lines :
    Finset.image (magPop 3) Finset.univ = {3, 1, -1, -3} := by decide

/-- **The first-spin spectrum has four lines** for `H = J Z₁(Z₂+Z₃+Z₄)` (Ex. 7.37): the collective
field takes four distinct values. -/
theorem nmrQuartet_lineCount : (Finset.image (magPop 3) Finset.univ).card = 4 := by decide

/-- **The relative magnitudes of the four lines are `1 : 3 : 3 : 1`** (Ex. 7.37). Reading the lines
in order of collective-field value `3, 1, −1, −3`, the number of neighbour configurations producing
each (its relative magnitude) is `1, 3, 3, 1` — the binomial coefficients `C(3, w)`
(`nmrMultiplet_lineMagnitude`). -/
theorem nmrQuartet_relativeMagnitudes :
    ([3, 1, -1, -3] : List ℤ).map
        (fun m => (Finset.univ.filter (fun A : Finset (Fin 3) => magPop 3 A = m)).card)
      = [1, 3, 3, 1] := by decide

/-- **The `cos³` Fourier decomposition behind the quartet:** `cos³θ = ¼cos 3θ + ¾cosθ`. With
`θ = 2Jt`, the spin-`1` signal `V(t) ∝ cos³(2Jt)` is thus a superposition of the frequency
`3θ = 6Jt` (amplitude `¼`) and `θ = 2Jt` (amplitude `¾`); the `¼ : ¾ = 1 : 3` amplitudes of the
outer and inner line pairs are the `1 : 3 : 3 : 1` relative magnitudes of the four lines. -/
theorem cos_cube (θ : ℝ) :
    Real.cos θ ^ 3 = (1 / 4) * Real.cos (3 * θ) + (3 / 4) * Real.cos θ := by
  rw [Real.cos_three_mul]; ring

/-- **The multiplet Fourier signature as a config sum (Ex. 7.37, `n = 3`).** Assigning to each of
the `2³ = 8` neighbour configurations `A` one cosine line at frequency `magPop 3 A` (the collective
field `Z₂+Z₃+Z₄`), the total spin-`1` signal shape is `∑_A cos(magPop 3 A · θ) = 2cos 3θ + 6cosθ`
(`= 8cos³θ`, `cos_cube`). The amplitudes `2` and `6` are the degeneracies of the field values `{±3}`
and `{±1}` — i.e. the `1 : 3 : 3 : 1` quartet magnitudes appearing directly as Fourier amplitudes of
the four lines at `{±3θ, ±θ}`. -/
theorem nmrQuartet_fourier (θ : ℝ) :
    ∑ A : Finset (Fin 3), Real.cos ((magPop 3 A : ℝ) * θ)
      = 2 * Real.cos (3 * θ) + 6 * Real.cos θ := by
  rw [show (Finset.univ : Finset (Finset (Fin 3)))
      = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} from by decide]
  simp (config := { decide := true }) only [Finset.sum_insert, Finset.sum_singleton, magPop,
    Finset.card_insert_of_notMem, Finset.card_singleton, Finset.card_empty, Finset.mem_insert,
    Finset.mem_singleton]
  push_cast
  simp only [neg_mul, one_mul, Real.cos_neg]
  ring

end AxQM.Concrete
