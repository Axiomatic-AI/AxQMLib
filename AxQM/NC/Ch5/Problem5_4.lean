/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.FactoringOpCountAsymptotics

/-!
# Nielsen & Chuang, Problem 5.4 (A tighter runtime bound for factoring)

Show factoring can achieve a better upper bound of O(L^2 log L log log L) operations.

The problem is a purely asymptotic (complexity) statement about real-valued cost functions.
The formalisation is in `AxQM/Concrete/FactoringOpCountAsymptotics.lean`; compare
`AxQM/NC/Ch5/Theorem5_1.lean`.

## What is formalised, and where

The mathematical kernel lives in `AxQM/Concrete/FactoringOpCountAsymptotics.lean`
(namespace `AxQM.Concrete`):

* `modExpMulCount` / `orderFindingRegisterSize` / `factoringModExpMulCount` — the **concrete**
  Box 5.2 modular-exponentiation multiplication count: `(t-1)` squarings + `(t-1)` product
  multiplications on a `t = 2L + 1 + c`-qubit exponent register, i.e. `4L + 2c` for an `L`-bit
  modulus.
* `factoringModExpMulCount_isBigO` — that count is **proved** to be `O(L)` (a combinatorial fact, no
  cost model needed).
* `fastMulOpBound` — the fast (Schönhage–Strassen) per-multiplication cost `L log L log log L`;
  `factoringFastOpBound` — the improved total bound `L² log L log log L`.
* `factoringOpCount_isBigO_of_fastMul` — **the improved bound is achievable**: the proved `O(L)`
  multiplication count, times an `O(L log L log log L)` per-multiplication cost, is
  `O(L² log L log log L)`.
* `factoringOpCount_isBigO_cubic_of_naiveMul` — the same count with the *naive* `O(L²)` per
  multiplication reproduces the textbook `O(L³)`, localising the improvement in the multiplication
  subroutine.
* `factoringFastOpBound_isLittleO_cubic` — **the improved bound is genuinely better**:
  `L² log L log log L = o(L³)`, so it is asymptotically strictly smaller than the `O(L³)` bound N&C
  calls "not tight".
* `factoringQftGateBound` / `factoringQftGateBound_isBigO` — the Hadamard + inverse Fourier
  transform gate bound `(2L+1+c)²` (`Θ(L²)`, N&C §5.1) is `O(L²)`.
* `factoringCircuitOpCount_isBigO_of_fastMul` — **the quantum circuit proper** (N&C p. 232: modular
  exponentiation + Fourier transform) is `O(L² log L log log L)` with fast multiplication;
  `factoringCircuitOpCount_isBigO_cubic_of_naiveMul` gives it the textbook `O(L³)` under naive
  multiplication.
* `factoringTotalOpCount_isBigO_of_fastMul` — **the whole factoring algorithm** is
  `O(L² log L log log L)`: on top of the circuit proper it folds in the continued-fractions recovery
  of the order (`O(L)` split-and-invert steps, Box 5.3 — N&C counts a *further* `O(L³)` here, `hCF`)
  and the `O(L²)` classical order→factor reduction (§5.3.2, Exercise 5.15, `hRed`), matching N&C's
  own accounting (p. 232); `factoringTotalOpCount_isBigO_cubic_of_naiveMul` gives the same whole
  algorithm the textbook `O(L³)` under naive multiplication.

## Fidelity note — the cost-model boundary

The multiplication **count** (`t − 1` squarings + `t − 1` products, `t = O(L)`) is a purely
combinatorial fact of Box 5.2, so it is discharged concretely and *proved* `O(L)` here — no
operational cost model is needed for it.  Only the per-multiplication **cost** is a genuine external
input: fast (Schönhage–Strassen) multiplication is `O(L log L log log L)`, which N&C cites rather
than re-derives, so it enters the achievability theorem as the single explicit `IsBigO` hypothesis
`hMul`.  What is proved is the genuine content of the problem: that the proved `O(L)` count composes
with that cost to the claimed `O(L² log L log log L)`, and that this bound is asymptotically
strictly below `O(L³)`.

The statement is made for **the factoring algorithm as a whole**, matching N&C's own resource
accounting (p. 232), which splits the `O(L³)` into co-equal parts: the *quantum circuit proper*
(modular exponentiation + Fourier transform) **and** the *continued-fractions* post-processing that
recovers the order (a *further* `O(L³)`), plus the `O(L²)` classical order→factor reduction.  The
two arithmetic-bound parts (modular exponentiation, continued fractions) share the single
per-`O(L)`-bit-operation cost `hMul`, since division of `L`-bit integers has the same asymptotic
cost as multiplication; the continued-fractions step count (`O(L)`, Box 5.3) and the reduction cost
(`O(L²)`, Exercise 5.15) enter as the cited hypotheses `hCF`, `hRed`.  Thus
`factoringTotalOpCount_isBigO_of_fastMul` proves the whole total is `O(L² log L log log L)` under
fast arithmetic — the two `O(L²)` parts (Fourier transform, reduction) being dominated either way —
which is exactly Problem 5.4's claim, and not the strictly weaker "improve only the bottleneck".
-/
