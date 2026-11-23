/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.Complex.PeriodicDFT

/-!
# Nielsen & Chuang, Exercise 5.20 (Fourier transform of a periodic function)

For f(x+r)=f(x), N multiple of r, compute DFT f-hat(l) via (5.68) using the root-of-unity sum
(5.69).

(The block above transcribes N&C p.238 **as printed**, including the printed `√(N/r)` on the
right-hand side of (5.69); see "On the misprint in (5.69)" below — the geometric sum in fact equals
`N/r`.)

## The declarations

All in `ToMathlib/Analysis/SpecialFunctions/Complex/PeriodicDFT.lean`:

* `normDFT` — the normalized length-`n` discrete Fourier transform of `f : ℤ → ℂ`,
  `normDFT n f ℓ = (1/√n) ∑_{x<n} exp(-2πi ℓ x / n) f x` (with `normDFT_apply` its definitional
  unfolding / API surface). This is N&C's `f̂` of (5.68) at length `n`, and — read at length `r` —
  the coefficient form of the period-finding state `|f̂(ℓ)⟩` of (5.63).
* `sum_range_exp_two_pi_mul_I_div` — the "fact" (5.69): the geometric sum of the `m`-th roots of
  unity, `∑_{j<m} exp(2πi ℓ j / m) = m` if `m ∣ ℓ` and `0` otherwise (with `m = N/r`; see the
  erratum note below).
* `normDFT_periodic_eq_zero` — **off-support:** if `ℓ` is not a multiple of `N/r`, then
  `normDFT N f ℓ = 0`.
* `normDFT_periodic_mul` — **on-support (the requested relation to (5.63)):**
  `normDFT N f (k · (N/r)) = √(N/r) · normDFT r f k`.

Supporting lemma `Finset.sum_range_mul_reindex` (the Euclidean reindexing of a sum over
`range (m·r)` into a double sum over blocks) has no DFT content and is in
`ToMathlib/Algebra/BigOperators/Fin.lean` (as a `@[to_additive]` pair with the product version
`Finset.prod_range_mul_reindex`), built on `Fin.sum_univ_eq_sum_range` and `finProdFinEquiv`. The
private `normDFT_sum_factor` (the period splitting of the length-`N` sum into a length-`r` sum times
a geometric sum over the `N/r` periods) stays in the DFT file.

## The computation, and the relation to (5.63)

Writing `x = j + r·i` with `j < r` and `i < N/r`, periodicity `f(j + r·i) = f(j)` factors the
length-`N` sum of (5.68) into `(∑_{j<r} exp(-2πiℓj/N) f(j)) · (∑_{i<N/r} exp(-2πiℓ·r·i/N))`. The
second factor is the root-of-unity sum (5.69): it is `N/r` when `N/r ∣ ℓ` and `0` otherwise. So
`f̂` is supported on the multiples `ℓ = k·(N/r)`, where the first factor's phase `exp(-2πiℓj/N)`
collapses to `exp(-2πi k j/r)`, giving `f̂(k·(N/r)) = (1/√N)·(N/r)·∑_{j<r} exp(-2πikj/r) f(j)
= √(N/r) · [(1/√r) ∑_{j<r} exp(-2πikj/r) f(j)]` — exactly `√(N/r)` times the (5.63) coefficient
`normDFT r f k`. This is the sense in which the length-`N` transform of a period-`r` signal is the
length-`r` transform (5.63), rescaled and resampled onto the harmonics `N/r`.

## On the misprint in (5.69)

As printed, the right-hand side of (5.69) reads `√(N/r)`. This is an erratum: the sum
`∑_{k∈{0,r,…,N-r}} e^{2πikℓ/N}` has exactly `N/r` terms, each equal to `1` when `ℓ` is a multiple of
`N/r`, so its value is `N/r`, **not** `√(N/r)`. The lone `√` in the final answer comes from the
`1/√N` normalization of (5.68) combined with the `1/√r` of (5.63): `(1/√N)·(N/r) = √(N/r)/√r`, so
the resampled coefficient carries a single factor `√(N/r)`. The formalisation
(`sum_range_exp_two_pi_mul_I_div`) states the correct value `N/r` for the sum, and
`normDFT_periodic_mul` carries the correct `√(N/r)` in the relation to (5.63).
-/
