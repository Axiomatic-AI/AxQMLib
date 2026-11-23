/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DiscreteLogFourier

/-!
# Nielsen & Chuang, Exercise 5.23 — inverting the discrete-logarithm Fourier double sum

*(N&C p. 239, §5.4.2 "Discrete logarithms".)*

Compute the inverse-Fourier double sum (5.73) using (5.70) and show the result is f(x1,x2).

Here `f(x₁,x₂) = b^{x₁} a^{x₂} = a^{s·x₁+x₂} mod N` is the discrete-log function (`a` of order `r`,
`b = a^s`, `s` the discrete logarithm), and `|f̂(ℓ₁,ℓ₂)⟩` is the Fourier state of eq. (5.70).

## The exercise is faithful; the reconstruction is proved

Eq. (5.70) is stated **with** its constraint (5.71): "the values of `ℓ₁` and `ℓ₂` must satisfy
[`∑_k e^{2πik(ℓ₁/s−ℓ₂)/r} = r`]. Otherwise, the amplitude of `|f̂(ℓ₁,ℓ₂)⟩` is nearly zero." Exercise
5.22 (`dlogFourierDoubleSum_eq_zero_of_not_modEq`) makes this exact: the genuine
two-dimensional Fourier transform `|f̂(ℓ₁,ℓ₂)⟩` **vanishes** unless `ℓ₁ ≡ s·ℓ₂ (mod r)`, and on that
support is the normalized single-`ℓ₂` state `(1/√r) ∑_j e^{−2πiℓ₂j/r}|f(0,j)⟩`. With the constraint
in force, the double sum (5.73) collapses — for each `ℓ₂` only the `ℓ₁ ≡ s·ℓ₂` term survives — to
the single-`ℓ₂` inverse discrete Fourier transform (eq. 5.45), which reconstructs the value state:

  `(1/r) ∑_{ℓ₁,ℓ₂} e^{2πi(ℓ₁x₁+ℓ₂x₂)/r} |f̂(ℓ₁,ℓ₂)⟩ = (1/√r) |f(x₁,x₂)⟩`.

So **the result is `f(x₁,x₂)`**, up to the `1/√r` normalization this schematic section leaves loose
(the same slop it already exhibits in eq. 5.72). This is the faithful content of Exercise 5.23.

Two printed imprecisions are made honest rather than glossed (see the API module docstring):
* **Normalization** — the literal `1/r` prefactor yields `(1/√r)|f(x₁,x₂)⟩`, a scalar multiple of
  the value state (the same quantum ray); the exact scalar is carried, never dropped.
* **Sign** — (5.73) is printed with the *forward* sign `e^{−2πi(…)}`, whereas the book's own inverse
  transform (eq. 5.64) and step 4's "apply inverse Fourier transform" carry `e^{+2πi(…)}`. With the
  printed `−` the sum reconstructs the *reflected* state `|f(−x₁,−x₂)⟩`
  (`dlogForwardFourierSum_eq_smul_reflected`), not `|f(x₁,x₂)⟩`; the inverse sign `+` is the
  faithful one. Both are proved, so the misprint is exhibited, not silently corrected.

(Taking `|f̂(ℓ₁,ℓ₂)⟩` to be `ℓ₁`-independent and nonzero for every `ℓ₁`, discarding the
constraint N&C states in the same breath as (5.70), the redundant `ℓ₁`-sum would kill the double sum
to `0` for `x₁ ≠ 0` — a *refutation*. That contradicts the constraint (5.71) and Exercise 5.22's own
`dlogFourierDoubleSum_eq_zero_of_not_modEq`, so it is not a faithful reading.)

## What is formalised, and where

The value states, the constrained Fourier states of eq. (5.70)/(5.71), and the reconstruction are
built directly on the Exercise 5.22 and 5.13 developments. The formalisation is in
`AxQM/Postulates/API/DiscreteLogFourier.lean`, as the Exercise 5.22 Fourier-state
development is in `AxQM/Postulates/API/DiscreteLogFourierState.lean`. The
declarations (all in namespace `AxQM`):

* `dlogFourierState a s ℓ₁ ℓ₂` — the eq.-(5.70)+(5.71) normalized Fourier state `|f̂(ℓ₁,ℓ₂)⟩`
  (`orderEigenstate a ℓ₂` on the support `ℓ₁ ≡ s·ℓ₂ (mod r)`, else `0`).
* `dlogFourierDoubleSum_eq_smul_dlogFourierState` — the bridge `DoubleSum = r√r · dlogFourierState`
  identifying it as the normalized Exercise-5.22 two-dimensional Fourier transform.
* `dlogInverseFourierSum a s x₁ x₂` — the inverse-Fourier double sum (5.73).
* `dlogInverseFourierSum_collapse` — **computing (5.73) using (5.70):** the `ℓ₁`-sum collapses via
  the constraint to the single-`ℓ₂` inverse transform.
* `dlogInverseFourierSum_eq_smul_dlogBasisState` — **the reconstruction of Exercise 5.23:** the
  double sum is `(1/√r)·|f(x₁,x₂)⟩`.
* `dlogForwardFourierSum a s x₁ x₂`, `dlogForwardFourierSum_eq_smul_reflected` — the literal
  printed-`−` sum and its honest value, the reflected state, exhibiting the sign misprint.

The value state `|f(x₁,x₂)⟩ = dlogBasisState a s x₁ x₂` is the Exercise 5.22 object it builds on.

See the docstring of `AxQM/Postulates/API/DiscreteLogFourier.lean` for the full discussion of the
constraint, normalization, and sign.
-/
