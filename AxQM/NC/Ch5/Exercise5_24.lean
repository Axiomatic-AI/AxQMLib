/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.NumberTheory.DiophantineApproximation.DiscreteLogRecovery

/-!
# Nielsen & Chuang, Exercise 5.24 (Generalized continued fractions for the discrete logarithm)

*(N&C p. 239, §5.4.2 "Discrete logarithms".)*

Construct the generalized continued fractions algorithm to determine s from sl2/r and l2/r.

The construction is classical number theory — the continued-fractions
recovery of a rational from a good real approximation (Legendre's theorem, N&C Theorem 5.1) applied
to two estimates, followed by modular division to solve for `s`.

## The declarations

All in `ToMathlib/NumberTheory/DiophantineApproximation/DiscreteLogRecovery.lean`, namespace
`DiscreteLogRecovery`:

* `recoverNumerator` / `recoverNumerator_eq` — knowing the order `r`, read the integer numerator `k`
  off the recovered fraction `k / r` (as `(q * r).num`).
* `discreteLogRecover` / `discreteLogRecover_eq` — the modular combination: from the two residues
  `(s·ℓ₂) mod r` and `ℓ₂ mod r`, recover `s` in `ZMod r` by `(s·ℓ₂) · (ℓ₂)⁻¹`.
* `discreteLogRecover_val` — the recovered element determines `s` concretely as its representative
  in `[0, r)`.
* `discreteLog_of_estimates` — the end-to-end correctness of the constructed algorithm (steps 4–6):
  from the two `1/(2r²)`-accurate estimates the algorithm outputs `s`.

The continued-fractions step itself is N&C Theorem 5.1 and is
`Real.exists_convs_eq_of_abs_sub_lt` in
`ToMathlib/NumberTheory/DiophantineApproximation/LegendreSharp.lean`.

## Correspondence to the discrete-log algorithm (N&C p. 239)

Steps 1–3 (create the superposition, query the oracle `U`, and expand `|f(x₁,x₂)⟩` in the Fourier
basis — the quantum content; the oracle itself is Exercise 5.25, and the Fourier state `|f̂(ℓ₁,ℓ₂)⟩`
and its coset constraint are Exercises 5.22/5.23) leave the first two registers holding the two
phases `s·ℓ₂/r` and `ℓ₂/r`. Steps 4–5 apply the inverse Fourier transform and measure, yielding the
two *estimates*. A phase register holds a value mod `1`, so the estimates approximate the fractional
residues `((s·ℓ₂) mod r)/r` and `(ℓ₂ mod r)/r`, not `s·ℓ₂/r` and `ℓ₂/r` literally — which is why the
recovery is genuinely modular and cannot be a plain real division. Exercise 5.24 is **step 6**, the
classical post-processing that turns those two estimates and the known `r` into `s`:

* **6a** — continued fractions on each estimate recovers the exact fraction `k/r`:
  `Real.exists_convs_eq_of_abs_sub_lt` (N&C Theorem 5.1, from `LegendreSharp.lean`).
* **6b** — read the residue `k` off `k/r` knowing `r`: `recoverNumerator` / `recoverNumerator_eq`.
* **6c** — combine the two residues by modular division into `s ∈ ZMod r`:
  `discreteLogRecover` / `discreteLogRecover_eq`.
* **6d** — extract the concrete `s ∈ [0, r)`: `discreteLogRecover_val`.
* **4–6, end-to-end** — from the two estimates the algorithm outputs `s`:
  `discreteLog_of_estimates`.

Step 6a is the single continued-fractions step of order finding (§5.3.1, N&C Theorem 5.1), whose
Legendre bound is `Real.exists_convs_eq_rat`; this exercise uses it once
per estimate — the sole "generalization" over order finding is running
it twice and recombining, per step 6c.

## The construction, and a fidelity point

The single continued-fractions step of order finding (§5.3.1) recovers one fraction `s/r` from one
estimate. The *generalized* algorithm runs it on the two estimates `s·ℓ₂/r` and `ℓ₂/r`, reads the
residues `(s·ℓ₂) mod r` and `ℓ₂ mod r` (both denominators are the known `r`), and combines them by
modular division: `s ≡ (s·ℓ₂) · ℓ₂⁻¹ (mod r)`.

**Coprimality is intrinsic.** The modular division needs `ℓ₂` invertible mod `r`,
i.e. `gcd(ℓ₂, r) = 1` (`IsCoprime ℓ₂ r`). Without it the two residues determine `s` only modulo
`r / gcd(ℓ₂, r)`, so `s` is genuinely not recoverable — this is exactly why the quantum algorithm
succeeds only with probability `O(1)` over the random `ℓ₂`.

**Complexity out of scope.** The `O(⌈log r⌉²)` operation count is a complexity claim with no cost
model in the library; as for Theorem 5.1, it is not formalised. The mathematical
correctness of the recovery is what the algorithm relies on and what is captured here.
-/
