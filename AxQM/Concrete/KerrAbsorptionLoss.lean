/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.KerrTwoPhotonPhase
import AxQM.Concrete.DetunedRabiAbsorption

/-!
# Concrete: cross-phase-modulation loss (Nielsen & Chuang, Exercise 7.22)

Nielsen & Chuang §7.5.3 models the optical Kerr effect microscopically: two orthogonally polarised
photon modes `a`, `b` (each with at most one photon) interact with a single three-level atom, giving
a modified Jaynes–Cummings Hamiltonian whose relevant part is block diagonal (7.82),
`H = diag(H₀, H₁, H₂)`. The two-photon phase shift (Exercise 7.21) comes with a *loss*: the atom
can absorb a photon. Exercise 7.22 asks to compute this absorption probability for the two-photon
input `|110⟩` and **compare** it with the single-photon input `|100⟩`, as a function of
`δ, gₐ, g_b, t`.

With `U = exp(-iHt)` (the exercise's stated convention) the survival amplitudes are `⟨110|U|110⟩`
(governed by the `3 × 3` block `H₂`, 7.85) and `⟨100|U|100⟩` (governed by the `4 × 4`
single-excitation block `H₁`, 7.84). The exercise writes the loss as `1 - ⟨110|U|110⟩`, but that
matrix element is a complex number; the *probability that a photon is absorbed* — what the prose
asks for — is `1 - |⟨110|U|110⟩|²`, the survival **probability** subtracted from `1` (exactly as in
N&C's own single-atom absorption `χ_r = ∑ₖ|⟨0k|U|10⟩|² = 1 - |⟨10|U|10⟩|²`, eq. 7.79). We formalise
that faithful reading.

## Main results

The engine is the reusable `2 × 2` detuned-block loss `detunedBlock_absorptionProb`
(`Concrete/DetunedRabiAbsorption.lean`), the Lorentzian absorption profile (7.79). Both losses of
Exercise 7.22 are that same profile `detunedAbsorptionLoss` evaluated at the appropriate coupling:

* `kerrSinglePhotonAbsorptionProb` — `1 - |⟨100|U|100⟩|² = detunedAbsorptionLoss δ gₐ t`
  `= gₐ²/(δ²+gₐ²)·sin²(√(δ²+gₐ²)·t)`. The `|100⟩` mode couples (strength `gₐ`) only to `|001⟩`, so
  its `2 × 2` sub-block of `H₁` is `detunedBlock δ gₐ`.
* `kerrTwoPhotonAbsorptionProb` — `1 - |⟨110|U|110⟩|² = detunedAbsorptionLoss δ √(gₐ²+g_b²) t`.
  Reducing `H₂` to its bright subspace turns the two couplings into a single **effective coupling**
  `√(gₐ²+g_b²)`; equivalently, the closed-form amplitude of Exercise 7.21 (`kerrBlockTwo`) coincides
  with the `detunedBlock` amplitude at that effective coupling
  (`kerrBlockTwo_exp_neg_apply_zero_zero`).
* `detunedAbsorptionLoss_sqrt` — the explicit value of the two-photon loss:
  `(gₐ²+g_b²)/(δ²+gₐ²+g_b²)·sin²(√(δ²+gₐ²+g_b²)·t)`, with the generalised Rabi frequency
  `Ω' = √(δ²+gₐ²+g_b²)` of the two-excitation sector.

**The comparison** (the exercise's point) is thus manifest: the two losses are the *same* function
`detunedAbsorptionLoss δ · t`, with coupling `gₐ` for the single photon and the larger effective
coupling `√(gₐ²+g_b²)` for the two photons. Adding the second mode raises both the peak loss
`g²/(δ²+g²)` and the Rabi frequency `√(δ²+g²)`.

The statement of Exercise 7.22 is in `AxQM/NC/Ch7/Exercise7_22.lean`. Compare Exercise 7.21
(`AxQM/Concrete/KerrTwoPhotonPhase.lean`).

A physically inessential nondegeneracy hypothesis (`0 < δ²+gₐ²` for the single photon,
`0 < gₐ²+g_b²` for two photons — a genuine atom–field coupling, as in N&C's Fig. 7.5 where
`gₐ = g_b = 1`) keeps the Rabi frequency positive so the quotient is well defined.
-/

namespace AxQM.Concrete

open NormedSpace Matrix

noncomputable section

open scoped Matrix.Norms.Operator

/-- **The detuned-block absorption/loss profile** (Nielsen & Chuang eq. 7.79): the probability
that a single excitation coupled with strength `g` to a two-level system detuned by `2δ` is
absorbed after time `t`,
`γ(δ, g, t) = g²/(δ²+g²)·sin²(√(δ²+g²)·t)`,
the Lorentzian profile `1 - |⟨0|exp(-itM(δ,g))|0⟩|²` of the `2 × 2` detuned block `detunedBlock δ g`
(`detunedBlock_absorptionProb`). Exercise 7.22's single- and two-photon losses are this profile at
couplings `gₐ` and `√(gₐ²+g_b²)` respectively. -/
def detunedAbsorptionLoss (δ g t : ℝ) : ℝ :=
  g ^ 2 / (δ ^ 2 + g ^ 2) * Real.sin (Real.sqrt (δ ^ 2 + g ^ 2) * t) ^ 2

/-- The **single-excitation block `H₁`** (Nielsen & Chuang eq. 7.84) of the modified
Jaynes–Cummings Hamiltonian, as the block-diagonal direct sum
`detunedBlock δ gₐ ⊕ detunedBlock δ g_b` of the two single-mode detuned blocks. In the basis
`|100⟩, |001⟩, |010⟩, |002⟩` this is exactly
`!![-δ, gₐ, 0, 0; gₐ, δ, 0, 0; 0, 0, -δ, g_b; 0, 0, g_b, δ]` (7.84): mode `a` couples
`|100⟩ ↔ |001⟩` with strength `gₐ`, mode `b` couples `|010⟩ ↔ |002⟩` with strength `g_b`, and the
two modes decouple. We index the sector as `(position, mode) : Fin 2 × Fin 2`, so the
single-photon mode-`a` input state `|100⟩` is `(0, 0)` (position `0`, mode `0`). -/
def kerrBlockOne (δ ga gb : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.blockDiagonal ![detunedBlock δ ga, detunedBlock δ gb]

/-- **Reduction of `H₁` to the `|100⟩` mode block.** Since `H₁` (7.84) is block diagonal and `|100⟩`
lies entirely in the mode-`a` block `detunedBlock δ gₐ`, the survival amplitude `⟨100|exp(zH₁)|100⟩`
equals the `2 × 2` amplitude `⟨0|exp(z·detunedBlock δ gₐ)|0⟩` (the other mode-`b` block is decoupled
from `|100⟩`). Proved by `Matrix.exp_blockDiagonal`. -/
theorem kerrBlockOne_exp_apply_zero_zero (δ ga gb : ℝ) (z : ℂ) :
    (exp (z • kerrBlockOne δ ga gb)) (0, 0) (0, 0) = (exp (z • detunedBlock δ ga)) 0 0 := by
  rw [kerrBlockOne, ← Matrix.blockDiagonal_smul, Matrix.exp_blockDiagonal,
    Matrix.blockDiagonal_apply', ite_eq_left rfl]
  erw [@Pi.coe_exp (Fin 2) (fun _ => Matrix (Fin 2) (Fin 2) ℂ) _ _ _ _
      (z • ![detunedBlock δ ga, detunedBlock δ gb]) 0]
  rfl

/-- **The two-photon amplitude via the effective coupling.** For `U = exp(-iHt)` the two-photon
survival amplitude `⟨110|U|110⟩` (the `(0,0)` entry of `exp(-it·H₂)`, `H₂` = `kerrBlockTwo`, 7.85)
equals the `2 × 2` detuned-block amplitude `⟨0|exp(-it·detunedBlock δ √(gₐ²+g_b²))|0⟩` at
the effective coupling `√(gₐ²+g_b²)`. Both closed forms (Exercise 7.21's
`kerrBlockTwo_exp_apply_zero_zero` evaluated at `-t`, and `detunedBlock_exp_apply_zero_zero`) equal
`cos Ω't + i(δ/Ω') sin Ω't` with `Ω' = √(δ²+gₐ²+g_b²)`. This is N&C's remark that `H₂` reduces to a
two-level block with the two couplings combined. -/
theorem kerrBlockTwo_exp_neg_apply_zero_zero (δ ga gb t : ℝ) (hg : 0 < ga ^ 2 + gb ^ 2) :
    (exp (-(Complex.I * (t : ℂ)) • kerrBlockTwo δ ga gb)) 0 0
      = (exp (-(Complex.I * (t : ℂ)) • detunedBlock δ (Real.sqrt (ga ^ 2 + gb ^ 2)))) 0 0 := by
  set Ω : ℝ := kerrRabiFreq δ ga gb with hΩdef
  have hpos : 0 < δ ^ 2 + ga ^ 2 + gb ^ 2 := by nlinarith [sq_nonneg δ]
  have hΩpos : 0 < Ω := Real.sqrt_pos.mpr hpos
  have hsmul : -(Complex.I * (t : ℂ)) • kerrBlockTwo δ ga gb
      = (Complex.I * ((-t : ℝ) : ℂ)) • kerrBlockTwo δ ga gb := by push_cast; ring_nf
  rw [hsmul, kerrBlockTwo_exp_apply_zero_zero δ ga gb (-t) hg]
  have hsq : (Real.sqrt (ga ^ 2 + gb ^ 2)) ^ 2 = ga ^ 2 + gb ^ 2 := Real.sq_sqrt hg.le
  have hΩeq : Ω = Real.sqrt (δ ^ 2 + (Real.sqrt (ga ^ 2 + gb ^ 2)) ^ 2) := by
    rw [hΩdef, kerrRabiFreq, hsq]; congr 1; ring
  rw [detunedBlock_exp_apply_zero_zero δ (Real.sqrt (ga ^ 2 + gb ^ 2)) t Ω hΩeq hΩpos.ne',
    mul_neg, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- **Exercise 7.22, single-photon loss.** The probability that the single photon `|100⟩` is
absorbed by the atom, `1 - |⟨100|U|100⟩|²` with `U = exp(-iHt)` and `H` as in (7.82), is the
detuned-block absorption profile at coupling `gₐ`:
`1 - |⟨100|U|100⟩|² = detunedAbsorptionLoss δ gₐ t = gₐ²/(δ²+gₐ²)·sin²(√(δ²+gₐ²)·t)`.
The `|100⟩` sector of `H₁` (7.84) is `detunedBlock δ gₐ` (`kerrBlockOne_exp_apply_zero_zero`); the
result is then `detunedBlock_absorptionProb`. -/
theorem kerrSinglePhotonAbsorptionProb (δ ga gb t : ℝ) (hga : 0 < δ ^ 2 + ga ^ 2) :
    1 - Complex.normSq ((exp (-(Complex.I * (t : ℂ)) • kerrBlockOne δ ga gb)) (0, 0) (0, 0))
      = detunedAbsorptionLoss δ ga t := by
  rw [detunedAbsorptionLoss, kerrBlockOne_exp_apply_zero_zero δ ga gb,
    detunedBlock_absorptionProb δ ga t (Real.sqrt (δ ^ 2 + ga ^ 2)) rfl
      (Real.sqrt_ne_zero'.mpr hga)]

/-- **Exercise 7.22, two-photon loss.** The probability that a photon is absorbed from the
two-photon input `|110⟩`, `1 - |⟨110|U|110⟩|²` with `U = exp(-iHt)` and `H` as in (7.82), is the
detuned-block absorption profile at the **effective coupling** `√(gₐ²+g_b²)`:
`1 - |⟨110|U|110⟩|² = detunedAbsorptionLoss δ √(gₐ²+g_b²) t`
(explicitly `(gₐ²+g_b²)/(δ²+gₐ²+g_b²)·sin²(√(δ²+gₐ²+g_b²)·t)`, see `detunedAbsorptionLoss_sqrt`).
Compared with the single photon (`kerrSinglePhotonAbsorptionProb`), the two-photon loss is the same
profile with `gₐ` replaced by the larger `√(gₐ²+g_b²)`. Via `kerrBlockTwo_exp_neg_apply_zero_zero`
and `detunedBlock_absorptionProb`. -/
theorem kerrTwoPhotonAbsorptionProb (δ ga gb t : ℝ) (hg : 0 < ga ^ 2 + gb ^ 2) :
    1 - Complex.normSq ((exp (-(Complex.I * (t : ℂ)) • kerrBlockTwo δ ga gb)) 0 0)
      = detunedAbsorptionLoss δ (Real.sqrt (ga ^ 2 + gb ^ 2)) t := by
  have hpos : 0 < δ ^ 2 + (Real.sqrt (ga ^ 2 + gb ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt hg.le]; nlinarith [sq_nonneg δ]
  rw [detunedAbsorptionLoss, kerrBlockTwo_exp_neg_apply_zero_zero δ ga gb t hg,
    detunedBlock_absorptionProb δ (Real.sqrt (ga ^ 2 + gb ^ 2)) t
      (Real.sqrt (δ ^ 2 + (Real.sqrt (ga ^ 2 + gb ^ 2)) ^ 2)) rfl (Real.sqrt_ne_zero'.mpr hpos)]

/-- The two-photon loss profile in closed form: with the effective coupling `√(gₐ²+g_b²)`,
`detunedAbsorptionLoss δ √(gₐ²+g_b²) t = (gₐ²+g_b²)/(δ²+gₐ²+g_b²)·sin²(Ω'·t)`, where
`Ω' = √(δ²+gₐ²+g_b²) = kerrRabiFreq δ gₐ g_b` is the generalised Rabi frequency (7.86) of the
two-excitation sector. -/
theorem detunedAbsorptionLoss_sqrt (δ ga gb t : ℝ) :
    detunedAbsorptionLoss δ (Real.sqrt (ga ^ 2 + gb ^ 2)) t
      = (ga ^ 2 + gb ^ 2) / (δ ^ 2 + ga ^ 2 + gb ^ 2)
          * Real.sin (kerrRabiFreq δ ga gb * t) ^ 2 := by
  have hg : (0 : ℝ) ≤ ga ^ 2 + gb ^ 2 := by positivity
  have hsq : (Real.sqrt (ga ^ 2 + gb ^ 2)) ^ 2 = ga ^ 2 + gb ^ 2 := Real.sq_sqrt hg
  have hΩ : Real.sqrt (δ ^ 2 + (Real.sqrt (ga ^ 2 + gb ^ 2)) ^ 2) = kerrRabiFreq δ ga gb := by
    rw [hsq, kerrRabiFreq]; congr 1; ring
  rw [detunedAbsorptionLoss, hΩ, hsq]
  ring

end

end AxQM.Concrete
