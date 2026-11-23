/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DiscreteLogFourierState

/-!
# Nielsen & Chuang, Exercise 5.22 — the discrete-log Fourier state (5.72)

*(N&C p. 239, §5.4.2 Discrete logarithms.)*

Show the discrete-log Fourier state |f-hat(l1,l2)> equals the (5.72) double sum / phase form.

(Verbatim from p.239: the printed double sum carries **no** prefactor; only the single sum
carries `1/√r`. Contrast (5.73) on the same page, whose double sum shows a visible `1/r`.)

In the quantum discrete-logarithm algorithm (§5.4.2) the function is
`f(x₁, x₂) = bˣ¹aˣ² = a^{s·x₁ + x₂} (mod N)`, where `a` has multiplicative order `r`,
`b = aˢ`, and `s` is the discrete logarithm being computed. Step 3 introduces the Fourier
state `|f̂(ℓ₁,ℓ₂)⟩`; the exercise is the identity that the two-dimensional Fourier transform
of `f` (the double sum) collapses to the one-dimensional transform over the coset
representatives `f(0,j) = aʲ mod N` (the single sum), non-zero only when `ℓ₁ ≡ s·ℓ₂ (mod r)`.

Every statement of the exercise is an identity between explicit state **vectors**: the double
and single Fourier sums are linear combinations of computational-basis states `|f(x₁,x₂)⟩`, viewed
as vectors `PureState.vec` (`PureState` is not itself a vector space). The formalisation builds on
the order-finding eigenstate development for Exercise 5.13 (`orderEigenstate`).

## What is formalised

All in `AxQM/Postulates/API/DiscreteLogFourierState.lean` (namespace `AxQM`),
for a unit `a : (ZMod N)ˣ` of order `r = orderOf a` and integers `s, ℓ₁, ℓ₂ : ℕ`:

* `dlogBasisState a s x₁ x₂` — the function-value state `|f(x₁,x₂)⟩ = |a^{s·x₁+x₂} mod N⟩` as a
  `PureState (qudit N)`; `dlogBasisState_zero_left` gives `|f(0,j)⟩ = |aʲ mod N⟩`.
* `dlogFourierDoubleSum a s ℓ₁ ℓ₂` — the double sum
  `∑_{x₁,x₂<r} e^{-2πi(ℓ₁x₁+ℓ₂x₂)/r} |f(x₁,x₂)⟩` (left side of (5.72));
  `dlogFourierSingleSum a ℓ₂` — the single sum `∑_{j<r} e^{-2πiℓ₂j/r} |f(0,j)⟩` (right side,
  = `√r·|f̂(ℓ₂)⟩`).
* `dlogFourierDoubleSum_factor` — the **phase form**: the double sum factors as a geometric phase
  sum over `x₁` times the single sum.
* `dlogFourierDoubleSum_of_modEq` — **eq. (5.72), on support**: if `ℓ₁ ≡ s·ℓ₂ (mod r)` then the
  double sum is `r • SingleSum` (equivalently `(1/r)·DoubleSum = SingleSum`).
* `dlogFourierDoubleSum_eq_zero_of_not_modEq` — **the constraint**: otherwise the double sum
  is `0`.
* `dlogFourierSingleSum_eq_orderEigenstate` — the single sum is `√r` times the *normalized*
  Fourier state `|f̂(ℓ₂)⟩ = orderEigenstate a ℓ₂` of eq. (5.70).

## Design notes

* **Fidelity.** The identity is proved for arbitrary `ℓ₁, ℓ₂, s : ℕ`, the
  double sum over the fundamental domain `x₁, x₂ < r` exactly as printed. The exact non-vanishing
  condition — the one the `x₁`-geometric sum yields, and the one the theorems use — is
  `ℓ₁ ≡ s·ℓ₂ (mod r)` (the algorithm's surviving state has `ℓ₁ = s·ℓ₂`). N&C's informal
  "`ℓ₁/s − ℓ₂` a multiple of `r`", read literally, presupposes `s ∣ ℓ₁` and is strictly *stronger*
  than `ℓ₁ ≡ s·ℓ₂ (mod r)`, so the formalisation states the mathematically exact condition.

* **On the printed normalization.** As printed, the double sum carries **no** prefactor and only
  the single sum carries `1/√r` — the printed double sum omits the natural unitary 2D-DFT factor
  `1/r` (visible on (5.73)). Writing `DoubleSum` / `SingleSum` for the two un-normalized sums, the
  proved on-support relation is `DoubleSum = r • SingleSum` and `SingleSum = √r·|f̂(ℓ₂)⟩` with
  `|f̂(ℓ₂)⟩` the unit eq.-(5.70) state (`dlogFourierSingleSum_eq_orderEigenstate`). Thus the printed
  left side equals `r^{3/2}·|f̂(ℓ₂)⟩` and the printed right side `|f̂(ℓ₂)⟩`: as literally printed
  they differ by a factor `r^{3/2}`. Supplying the omitted `1/r` makes the two sum forms agree,
  `(1/r)·DoubleSum = SingleSum`. The Lean statements need no change. See the API module docstring
  for the full discussion.
-/
