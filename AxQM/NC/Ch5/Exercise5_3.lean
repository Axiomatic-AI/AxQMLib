/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Fourier.DiscreteFourierComplexity

/-!
# Nielsen & Chuang, Exercise 5.3 (Classical fast Fourier transform)

Classical FFT: DFT on 2^n numbers is Theta(2^2n) direct, reducible to Theta(n 2^n) via product form.
Equation (5.4). (N&C p. 221.)

The two textbook equations the exercise cites (N&C §5.1) are the discrete Fourier transform and
its product form; with `N = 2 ^ n`:

* **(5.1)** — the DFT itself, `y_k = (1 / √N) · ∑_{j=0}^{N-1} x_j · exp(2 π i j k / N)`. Evaluating
  this `N × N` matrix–vector product output-by-output is the "straightforward method" whose cost is
  the *first* claim, `Θ(2 ^ (2 n))`.
* **(5.4)** — the product representation
  `|j₁…jₙ⟩ ↦ 2 ^ (-n / 2) · (|0⟩ + e^{2 π i · 0.jₙ} |1⟩) ⋯ (|0⟩ + e^{2 π i · 0.j₁…jₙ} |1⟩)`, whose
  even/odd divide-and-conquer split is the (classical) fast Fourier transform whose cost is the
  *second* claim, `Θ(n · 2 ^ n)`. (N&C introduce (5.4) for the quantum Fourier transform and note
  the classical FFT falls out "as an incidental bonus … in the exercises".)

This is an operation-count (complexity) statement about two classical
algorithms — the schoolbook discrete Fourier transform and the fast Fourier transform. Compare
Exercise 5.1 and Theorem 5.1.

## What is formalised, and where

The formalisation is in `ToMathlib/Analysis/Fourier/DiscreteFourierComplexity.lean`
(namespace `DiscreteFourier`). Each algorithm's count of *elementary arithmetic operations* is an
explicit `ℕ → ℕ` function whose control structure mirrors the algorithm — the same modelling used
for the gate count of `AxQM.Concrete.mcNotGateBound` (Exercise 4.29) — and the two
`Θ`-claims are `Asymptotics.IsTheta` statements (`=Θ[atTop]`):

* `DiscreteFourier.directDftOpCount` — the direct evaluation count `4 ^ n + 2 ^ n · (2 ^ n − 1)`
  (the `N ^ 2` multiplications and `N · (N − 1)` additions of the `N × N` matrix–vector product,
  `N = 2 ^ n`), and `DiscreteFourier.directDftOpCount_isTheta` : it is `Θ(2 ^ (2 n))`. **First
  claim.**
* `DiscreteFourier.fftOpCount` — the FFT count as the divide-and-conquer recurrence `T 0 = 0`,
  `T (n+1) = 2 · T n + 2 ^ (n+1)` induced by the product form (5.4); `DiscreteFourier.fftOpCount_eq`
  solves it to `n · 2 ^ n`, and `DiscreteFourier.fftOpCount_isTheta` : it is `Θ(n · 2 ^ n)`.
  **Second claim.**
* `DiscreteFourier.eq_mul_two_pow_of_divideAndConquer` — the closed form holds for *any* sequence
  obeying the recurrence (so it is a theorem about the recurrence, not a value chosen to fit).
* `DiscreteFourier.fftOpCount_le_directDftOpCount` and
  `DiscreteFourier.fftOpCount_isLittleO_directDftOpCount` — the "reduction": the FFT never costs
  more, and is asymptotically negligible (`n · 2 ^ n = o(2 ^ (2 n))`).

## Scope

Exercise 5.3 concerns the *operation count*, which is what is formalised. Full verification that an
explicit straight-line program of this length evaluates the DFT (as
`AxQM.Concrete.exists_mcNotCircuit` does for a gate list) is a separate, much larger
development and is not formalised; unitarity/correctness of the DFT itself is
Exercise 5.1 (`ZMod.dftMatrix_mem_unitaryGroup`).
-/
