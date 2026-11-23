/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BellLocalMeasurement

/-!
# Nielsen & Chuang, Exercise 12.32 — local `Z` measurements reproduce the `Π_bf` statistics

*(N&C p. 595.)*

Local X,Z measurements give same statistics as Bell-basis projectors Pi_bf,Pi_pf.

## Context (N&C §12.6.5, p. 595)

In the entanglement-based QKD security proof Alice and Bob must estimate the fidelity of their EPR
pairs by detecting bit-flip and phase-flip errors, whose natural detectors are the Bell-basis
projective measurements

  `Π_bf = |β₀₁⟩⟨β₀₁| + |β₁₁⟩⟨β₁₁| = (I⊗I − Z⊗Z)/2`  (bit flip),
  `Π_pf = |β₁₀⟩⟨β₁₀| + |β₁₁⟩⟨β₁₁| = (I⊗I − X⊗X)/2`  (phase flip).

Bell-basis measurements are nonlocal, but the identities `Π_bf = (I⊗I − Z⊗Z)/2` and
`Π_pf = (I⊗I − X⊗X)/2` mean the *compiled* outcome — the product of the two parties' local `Z`
(resp. `X`) results — has the same distribution as a `Π_bf` (resp. `Π_pf`) measurement, even though
the individual local measurements `Z ⊗ I`, `I ⊗ Z` (resp. `X ⊗ I`, `I ⊗ X`) do **not** commute with
the Bell basis. This file formalises **both** halves: the bit-flip (`Z`) half and the phase-flip
(`X`) half.

## The formalisation

The bit-flip procedure is `localZMeasurement`, the cascade of the two single-qubit `Z` sign
measurements (Alice on the left factor, Bob on the right), with compiled statistic the parity
`zParity (a, b) = a + b` ("did the outcomes disagree?"). The reference `Π_bf` procedure is
`bellMeasurement.coarseGrain bitFlipIndex`, the Bell measurement grouped by whether a bit flip
occurred (`bitFlipIndex (x, y) = y`); its "detected" effect is exactly `bitFlipProjector = Π_bf`
(`bitFlipProjector_eq_bellMap`). The phase-flip procedure `localXMeasurement` and its statistic
`xParity` mirror this in the Hadamard basis, with reference `bellMeasurement.coarseGrain
phaseFlipIndex` (`phaseFlipIndex (x, y) = x`) and "detected" effect `phaseFlipProjector = Π_pf`
(`phaseFlipProjector_eq_bellMap`). The apparatus and the two key operator identities
(`localZMeasurement_map_elements_eq` / `localXMeasurement_map_elements_eq`: the coarse-grained POVM
effects coincide) are in `AxQM/Postulates/API/BellLocalMeasurement.lean`.

The theorems below are stated with `Measurement.bornProb` and `Measurement.coarseGrain`.
They hold for an **arbitrary** received state `ρ` (mixed, as in N&C's noisy channel), because equal
POVM effects give equal Born probabilities on every state.
-/

noncomputable section

namespace AxQM

/-- **Exercise 12.32 (bit-flip half).** The statistics Alice and Bob compile from their **local**
`Z` measurements — the parity `zParity` of the two outcomes, coarse-grained from
`localZMeasurement` — are, for *every* state `ρ`, identical to those of the Bell-basis `Π_bf`
measurement (`bellMeasurement.coarseGrain bitFlipIndex`). Despite `Z ⊗ I` and `I ⊗ Z` not
commuting with the Bell basis, the compiled bit-flip statistic sees only the diagonal of the Bell
decomposition: the two coarse-grained measurements share the same POVM effects
(`localZMeasurement_map_elements_eq`), hence the same Born rule. -/
theorem localZParity_bornProb_eq_bitFlipMeasurement (ρ : State (qubit ⊗ qubit)) (k : Fin 2) :
    (localZMeasurement.coarseGrain zParity).bornProb ρ k
      = (bellMeasurement.coarseGrain bitFlipIndex).bornProb ρ k := by
  rw [Measurement.coarseGrain, Measurement.coarseGrain,
    Measurement.ofPOVM_bornProb_eq_re_trace, Measurement.ofPOVM_bornProb_eq_re_trace,
    localZMeasurement_map_elements_eq]

/-- **Exercise 12.32 (phase-flip half).** The statistics Alice and Bob compile from their **local**
`X` measurements — the parity `xParity` of the two outcomes, coarse-grained from
`localXMeasurement` — are, for *every* state `ρ`, identical to those of the Bell-basis `Π_pf`
measurement (`bellMeasurement.coarseGrain phaseFlipIndex`). Despite `X ⊗ I` and `I ⊗ X` not
commuting with the Bell basis, the compiled phase-flip statistic sees only the diagonal of the Bell
decomposition: the two coarse-grained measurements share the same POVM effects
(`localXMeasurement_map_elements_eq`), hence the same Born rule. The Hadamard-basis mirror of
`localZParity_bornProb_eq_bitFlipMeasurement`. -/
theorem localXParity_bornProb_eq_phaseFlipMeasurement (ρ : State (qubit ⊗ qubit)) (k : Fin 2) :
    (localXMeasurement.coarseGrain xParity).bornProb ρ k
      = (bellMeasurement.coarseGrain phaseFlipIndex).bornProb ρ k := by
  rw [Measurement.coarseGrain, Measurement.coarseGrain,
    Measurement.ofPOVM_bornProb_eq_re_trace, Measurement.ofPOVM_bornProb_eq_re_trace,
    localXMeasurement_map_elements_eq]

end AxQM
