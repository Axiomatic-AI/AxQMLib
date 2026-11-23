/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RabiOscillation

/-!
# Nielsen & Chuang, Exercise 7.18 (Rabi oscillations)

**Exercise 7.18 (p. 303).** *Show that (7.77) is correct by using (7.78) to exponentiate `H`.*
The single-excitation Jaynes–Cummings Hamiltonian (7.76) is exponentiated to the Rabi-oscillation
time-evolution operator (7.77), via the Pauli-exponential identity (7.78) = N&C (4.8).

## The formalisation

The exercise asks to exponentiate the concrete `3×3` matrix `H` (7.76); the statement concerns only
matrices (`Matrix`, `NormedSpace.exp`, `Real.cos`/`Real.sin`, `Complex.exp`). It reuses the
matrix-exponential development of Ex. 2.35 (`AxQM/Concrete/PauliExponential.lean`); compare the
Chapter 7 items Ex. 7.9 (optical Hadamard) and 7.16 (dipole selection rules). The formalisation is
in `AxQM/Concrete/RabiOscillation.lean`:

* `AxQM.Concrete.rabiFrequency` — `Ω = √(g²+δ²)`, the Rabi frequency.
* `AxQM.Concrete.rabiHamiltonian` — `H = -!![δ,0,0; 0,δ,g; 0,g,-δ]` (eq. 7.76), with
  `rabiHamiltonian_isHermitian`.
* `AxQM.Concrete.rabiInvolution` (and its real form `rabiInvolutionReal`) — the involution
  `Ĵ = |00⟩⟨00| + n̂·σ` used to exponentiate `H`, with `rabiInvolution_mul_self` (`Ĵ² = I`).
* `AxQM.Concrete.rabiUnitary` — the time-evolution operator `U` (the corrected eq. 7.77).
* `AxQM.Concrete.exp_neg_I_smul_rabiHamiltonian` — **the exercise**:
  `exp((-i t) • rabiHamiltonian δ g) = rabiUnitary δ g t` for `Ω ≠ 0`, and
  `AxQM.Concrete.rabiUnitary_apply_zero_zero` — the `|00⟩` phase equals `e^{iδt}`.

## Fidelity note

N&C's printed (7.77) has two sign typos (the `|00⟩` phase `e^{-iδt}` should be `e^{+iδt}`, and the
off-diagonal `-i(g/Ω) sin Ωt` should be `+i(g/Ω) sin Ωt` — the two cannot both be produced by any
single sign of `H`/`t`, so as printed it is internally inconsistent); the printed (7.78) swaps
`cos`/`sin` and drops the `I` term. `AxQM/Concrete/RabiOscillation.lean` proves the *true*
exponential of `H` exactly as (7.76) is printed and uses the correct identity (7.78) = (4.8); see
its module docstring for the full discussion. All physical content — the Rabi frequency `Ω`, the
coherent `|01⟩↔|10⟩`
energy exchange, the Lorentzian absorption profile — is exactly as N&C describes.
-/
