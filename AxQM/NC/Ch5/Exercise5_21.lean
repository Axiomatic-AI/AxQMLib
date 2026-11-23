/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PeriodShift

/-!
# Nielsen & Chuang, Exercise 5.21 — period-finding and phase estimation

*(N&C p. 238, §5.4.1.)*

Period-finding & phase estimation: eigenvectors of U_y are |f-hat(l)>; realize black box from
|f(x0)>.

Here `f` is the periodic function of Exercise 5.20 (`f(x+r) = f(x)`, `0 ≤ x < N`, `N` a multiple of
`r`), and (N&C eq. 5.63) the Fourier states are

  `|f̂(ℓ)⟩ = (1/√r) ∑_{x=0}^{r−1} e^{−2πiℓx/r} |f(x)⟩`,

the inverse discrete Fourier transform of the value states over one period.

## The model

The period-finding data is: `r` distinct value states `|f(0)⟩, …, |f(r−1)⟩` (`f` is one-to-one on a
period — this is what makes `|f̂(ℓ)⟩` an orthonormal Fourier basis and `U_y` a well-defined
unitary), which the shift `U_y` **cyclically permutes** (`|f(x)⟩ ↦ |f(x+y)⟩`, with `f(x+r) = f(x)`).
An orthonormal family cyclically permuted by a unitary is canonically the computational basis of an
`r`-level register, with `|f(x)⟩ = |x mod r⟩`; the shift is then `|x⟩ ↦ |x+y⟩` on `Fin r`. So the
formalisation takes the **period register** `qudit r`, value states `quditBasis x`, and

* `U_y = periodShift r y` — the cyclic-shift gate `|x⟩ ↦ |x+y⟩` (`+` the modular addition of
  `Fin r`), defined as the shift permutation (`quditPerm (Equiv.addRight y)`), with **no**
  reference to the Fourier transform;
* `|f̂(ℓ)⟩ = qftInverseFourierImage r ℓ` — the inverse-QFT image `F⁻¹|ℓ⟩ = (1/√r) ∑_x e^{−2πiℓx/r}
  |x⟩`, which is exactly eq. (5.63).

Modelling `|f(x)⟩` as `|x mod r⟩` loses no content of parts (1)/(2): any injective periodic `f`
gives the same eigenstructure up to the unitary relabelling `|f(x)⟩ ↔ |x mod r⟩`, and both parts
concern only that eigenstructure. This mirrors how Exercise 5.13 models the order-finding value
states `|xᵏ mod N⟩` as computational-basis states of `qudit N`.

## What is formalised, and where

The formalisation is in `AxQM/Postulates/API/PeriodShift.lean`, as the closely analogous
order-finding eigenstate development for Exercise 5.13 is in
`AxQM/Postulates/API/OrderFindingEigenstate.lean`. The declarations (all in namespace `AxQM`):

* `quditPerm σ` — the general single-register computational-basis permutation gate `|x⟩ ↦ |σ x⟩`
  (`quditPerm_op_apply_quditBasis` / `quditPerm_evolvePure_quditBasis`), the single-register
  companion of `quditPairPerm`.
* `periodShift r y` — **the shift operator `U_y`** of the exercise, `|x⟩ ↦ |x+y⟩`, with
  `periodShift_op_apply_quditBasis` / `periodShift_evolvePure_quditBasis` its defining action.
* `periodShift_hasEigenstate_qftInverseFourierImage` — **part (1):** the Fourier states
  `|f̂(ℓ)⟩ = F⁻¹|ℓ⟩` are the eigenvectors of `U_y`, with **eigenvalue `e^{2πiℓy/r}`**
  (`(periodShift r y).HasEigenstate (e^{2πiℓy/r}) (qftInverseFourierImage r ℓ)`).
* `quditBasis_eq_sum_qftInverseFourierImage` — **part (2), eq. (5.64):** a value state
  `|f(x₀)⟩ = |x₀⟩` is the equal-magnitude superposition `(1/√r) ∑_ℓ e^{2πiℓx₀/r} |f̂(ℓ)⟩` of *all*
  the eigenstates.

## Design notes

* **Part (1) — the eigenvalue.** `U_y|f̂(ℓ)⟩ = (1/√r) ∑_x e^{−2πiℓx/r} |x+y⟩`; reindexing `x ↦ x+y`
  factors out the constant phase `e^{2πiℓy/r}`, returning `|f̂(ℓ)⟩`. So the Fourier basis
  **diagonalises** `U_y` — a *theorem* here, since `periodShift` is defined as the raw shift, not as
  `F⁻¹ (diag) F`. (Contrast Problem 5.6's `additionByFourier`, which *builds* the same shift from
  the Fourier transform; that this file's independently-defined `periodShift` has Fourier
  eigenstates is the substance of part (1).)

* **Part (2) — "as useful as `U`".** Two facts together are the content:
  1. `periodShift_evolvePure_quditBasis`: `U_y|f(x₀)⟩ = |f(x₀+y)⟩` — supplying `y` from a control
     register realises the period-finding black box for the shifted function `g(y) = f(x₀+y)`, which
     has the **same period `r`** (it is `f` translated by the constant `x₀`), hence is just as
     useful as `f`'s black box `U`.
  2. `quditBasis_eq_sum_qftInverseFourierImage` (eq. 5.64): `|f(x₀)⟩` is an *equal-magnitude*
     superposition of all eigenstates `|f̂(ℓ)⟩`. This is the crux: `|f(x₀)⟩` is to `U_y` exactly
     what `|1⟩ = (1/√r) ∑_s |u_s⟩` (eq. 5.44, Exercise 5.13) is to the order-finding operator — a
     single, trivially available state that superposes *every* eigenstate with equal weight. Phase
     estimation on `U_y` started from `|f(x₀)⟩` therefore samples the eigenphases `ℓy/r` (part (1))
     and, by continued fractions, recovers the period `r`.

  The verifiable propositions are these two identities; the surrounding "as useful as" is the
  informal reduction they justify (a control register plus continued fractions — an efficiency/
  circuit-model claim that is not expressed here, cf. the QFT gate counts of
  Problem 5.1).
-/
