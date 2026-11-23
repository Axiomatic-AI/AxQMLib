/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ChannelUnitality

/-!
# Nielsen & Chuang, Exercise 8.29 (Unitality of the single-qubit noise channels)

*(N&C p. 386.)*

Show depolarizing and phase damping channels are unital (E(I)=I) but amplitude damping is not.

## The computation

For a quantum operation in operator-sum form `E(ρ) = ∑ₖ Eₖ ρ Eₖ†`, unitality `E(I) = ∑ₖ Eₖ Eₖ† = I`
is the mirror image of trace preservation (`∑ₖ Eₖ† Eₖ = I`). Evaluating `E(I)` for the three
canonical single-qubit noise channels of N&C §8.3:

* **Depolarizing** (eq. 8.102, `E(ρ) = (1 - 3p/4) ρ + (p/4)(XρX + YρY + ZρZ)`):
  `E(I) = (1 - 3p/4) I + (p/4)(X² + Y² + Z²) = (1 - 3p/4) I + (3p/4) I = I`. **Unital.**
* **Phase damping** (eqs. 8.127–8.128, `E₀ = diag(1,√(1-λ))`, `E₁ = diag(0,√λ)`):
  `E(I) = E₀ E₀† + E₁ E₁† = (P₀ + (1-λ) P₁) + λ P₁ = P₀ + P₁ = I`. **Unital.** (Consistent with
  phase damping being the phase-flip channel — a random mixture of `I` and `Z` — Exercise 8.27.)
* **Amplitude damping** (eq. 8.108, `E₀ = diag(1,√(1-γ))`, `E₁ = √γ |0⟩⟨1|`):
  `E(I) = E₀ E₀† + E₁ E₁† = (P₀ + (1-γ) P₁) + γ P₀ = (1+γ) P₀ + (1-γ) P₁ = I + γ Z`, which is `≠ I`
  for `γ ≠ 0`. **Not unital** — the extra `γ Z` biases population toward `|0⟩` (amplitude damping
  has a preferred fixed point, the `|0⟩` "north pole", not the maximally mixed state).

The depolarizing channel is taken in its **operator-sum** form (eq. 8.102); N&C's completely-mixing
display `E(ρ) = p(I/2) + (1-p)ρ` (eq. 8.100) is affine and correct only on trace-one states, so it
cannot be used to evaluate `E` at the trace-two identity `I` (see the module docstring of
`AxQM/Concrete/ChannelUnitality.lean`).

## Scope

The formal content of Exercise 8.29 is the direct linear-algebra computation of `E(I) = ∑ₖ Eₖ Eₖ†`
for three explicit channels (`LinearMap` on a qubit, `Matrix`, `Concrete.pauliX/Y/Z`). Compare
Exercises 8.17, 8.22 and 8.27. The channels use the amplitude- and phase-damping channels
(`AxQM/Concrete/AmplitudeDampingChannel.lean`, `AxQM/Concrete/PhaseDampingChannel.lean`) and the
Pauli matrices (`AxQM/Concrete/Pauli.lean`).

The grounded predicate `AxQM.IsUnital` (`f (I/d) = I/d`, over `f : State S → State S`)
developed for **Problem 8.3** quantifies over the abstract *space* of channels on a `QSystem` — the
tool for Problem 8.3's structural theorems. Exercise 8.29 is the complementary concrete task of
computing `E(I)` for three named channels; the operator-level facts proved here are exactly what a
grounded `IsUnital` reduces to (`E(I/2) = I/2 ⇔ E(I) = I`), so the two are compatible.

## The formalisation

The formalisation is in `AxQM/Concrete/ChannelUnitality.lean`:

* `AxQM.Concrete.depolChannel` — the qubit depolarizing channel in operator-sum form
  `E(ρ) = (1 - 3p/4) ρ + (p/4)(XρX + YρY + ZρZ)` (eq. 8.102), with
  `AxQM.Concrete.depolChannel_apply_one` — **unital**: `E(I) = I`.
* `AxQM.Concrete.phaseDampChannel_apply_one` — the **phase-damping channel is unital**:
  `E_PD(I) = I` (`0 ≤ λ ≤ 1`). (The channel `AxQM.Concrete.phaseDampChannel` and the
  self-adjointness of its operation elements live in `AxQM/Concrete/PhaseDampingChannel.lean`.)
* `AxQM.Concrete.ampDampChannel_apply_one` — the **value** `E_AD(I) = (1+γ) P₀ + (1-γ) P₁
  = I + γ Z` (`0 ≤ γ ≤ 1`), and `AxQM.Concrete.ampDampChannel_not_unital` — **amplitude
  damping is not unital**: `E_AD(I) ≠ I` for `0 < γ`.

The amplitude-damping value uses the ladder identity `AxQM.Concrete.qubitLower_comp_adjoint_self`
(`σ₋ σ₊ = P₀`) of `AxQM/Concrete/QubitBasisOperators.lean`, together with its companion
`qubitLower_adjoint_comp_self` (`σ₊ σ₋ = P₁`).

See the module docstring of `AxQM/Concrete/ChannelUnitality.lean` for the full argument.
-/
