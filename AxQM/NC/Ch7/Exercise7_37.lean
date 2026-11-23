/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.NMRCoupledSpinFIDSignal
import AxQM.Concrete.NMRMultiplet

/-!
# Nielsen & Chuang, Exercise 7.37 (NMR spectrum of coupled spins)

*(N&C p. 329, §7.7 "Nuclear magnetic resonance".)*

NMR spectrum of coupled spins: compute V(t) for H=JZ1Z2; count spectral lines and magnitudes for
H=JZ1(Z2+Z3+Z4).

The free-induction-decay signal is `V(t) = V₀ tr[e^{-iHt} ρ e^{iHt} (i Xₖ + Yₖ)]` (eq. 7.143, here
`k = 1`, reading out the first spin). The exercise has two parts: **(1)** compute `V(t)` for the
`J`-coupled *pair*; **(2)** count the spectral lines and relative magnitudes of the first spin when
it is instead coupled to *three* equivalent neighbours.

## The answers

**Part 1 (`H = J Z₁Z₂`).** The `90°` read pulse `e^{iπY₁/4}` rotates the population difference
`−βℏω₀ Z₁` into transverse magnetization `+βℏω₀ X₁`; the coupled precession under `J Z₁Z₂` makes
the first spin oscillate at the neighbour-conditioned frequency, giving

> `V(t) = i · V₀ · βℏω₀ · cos(2Jt)` — a single **doublet** at `±2J`.

**Part 2 (`H = J Z₁(Z₂ + Z₃ + Z₄)`).** The first spin now couples to three equivalent neighbours,
whose collective field `Z₂ + Z₃ + Z₄` takes the four values `{3, 1, −1, −3}` with the binomial
degeneracies `C(3, w) = 1, 3, 3, 1`. Hence the spectrum is

> a **quartet: four lines** (frequencies `{±6J, ±2J}`) with **relative magnitudes `1 : 3 : 3 : 1`**.

Equivalently `V(t) ∝ cos³(2Jt) = ¼cos(6Jt) + ¾cos(2Jt)` — the amplitudes `¼ : ¾` of the outer and
inner line pairs are the `1 : 3 : 3 : 1` degeneracies.

## Where the formalisation is

**Part 1.** `V(t)` is the operator trace of the Schrödinger-evolved state against the transverse
readout, formalised in terms of `.op` and `LinearMap.trace`:

* `AxQM.nmrCoupledPairFID` / `nmrCoupledPairFID_eq` — the FID signal `V(t)` and its value
  `i V₀ βℏω₀ cos(2Jt)` (`AxQM/Postulates/API/NMRCoupledSpinFIDSignal.lean`).
* supporting: `couplingZZHamiltonian`, `nmrTransverseReadout` (`i X₁ + Y₁`), `nmrReadout_heisenberg`
  (`AxQM/Postulates/API/NMRCoupledSpinFID.lean`); `nmrCoupledPairPulsedState` /
  `nmrCoupledPairPulsedState_op` — the `π/2`-pulsed thermal state `ρ` and `ρ.op = ¼(1 + βℏω₀ X₁ −
  βℏω₀ Z₂)` (`AxQM/Postulates/API/NMRCoupledSpinPulsedState.lean`); the Heisenberg conjugation
  lemmas `Observable.propagator_conj_op_commute` / `_anticomm`
  (`AxQM/Postulates/API/InvolutionPropagatorConjugation.lean`).

**Part 2.** "How many lines / what relative magnitudes" is a
statement about the eigenvalue multiplicities of the collective field `Z₂ + Z₃ + Z₄` and the Fourier
content of `cos³`, over `Finset (Fin n)`, `ℤ`, `ℕ.choose`, `Real.cos` (compare the NMR exercise
7.44):

* `AxQM.Concrete.nmrQuartet_lineCount` / `nmrQuartet_lines` — **four lines**, at the four
  collective-field values `{3, 1, −1, −3}`.
* `AxQM.Concrete.nmrQuartet_relativeMagnitudes` — the four magnitudes are `1, 3, 3, 1`.
* `AxQM.Concrete.nmrMultiplet_degeneracy` / `nmrMultiplet_lineMagnitude` — the general
  multiplet law: the line at field value `n − 2w` has binomial multiplicity `C(n, w)`.
* `AxQM.Concrete.cos_cube` / `nmrQuartet_fourier` — the `cos³` Fourier signature realising
  the `1 : 3 : 3 : 1` amplitudes (all in `AxQM/Concrete/NMRMultiplet.lean`, using 7.44's
  `magPop`).

## Fidelity

Part 1 formalises the FID `V(t)` of eq. 7.143 exactly, for a state, an evolution
and a readout observable, obtaining N&C's `cos(2Jt)` doublet with no added hypotheses. Part 2 pins
both requested quantities exactly — the number of lines (`n + 1 = 4`) and their relative magnitudes
(the exact binomial coefficients `C(3, ·) = 1 : 3 : 3 : 1`), with the `cos³` Fourier signature
matching the amplitudes physically observed in `V(t) ∝ cos³(2Jt)`, continuous with the Part-1
doublet.
-/
