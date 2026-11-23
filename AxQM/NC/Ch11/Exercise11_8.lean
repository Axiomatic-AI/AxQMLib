/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.JointEntropy

/-!
# N&C Exercise 11.8 — mutual information is not always subadditive

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.8, p. 509.

Show mutual information is not always subadditive via a modulo-2 example.

Here `H(A : B) = H(A) + H(B) − H(A, B)` is the (Shannon) mutual information, and `H(X, Y : Z)` reads
the pair `(X, Y)` as a single system. The point of the example is that `X` alone and `Y` alone each
tell you *nothing* about `Z = X ⊕ Y` (`H(X : Z) = H(Y : Z) = 0`), yet `(X, Y)` *together* determine
`Z` (`H(X, Y : Z) = H(Z) = 1` bit). So the combined system carries strictly more information about
`Z` than the parts do separately, and the naive subadditivity fails.

## Where the formalisation lives

The exercise quantifies over real-valued distributions on products of the finite type `ZMod 2` and
the real-valued `Real.entropy` / `Real.mutualInfo`. Compare Exercise 11.5
(`AxQM/NC/Ch11/Exercise11_5.lean`).

The declarations are in the namespace `Real.XorMutualInfo` in
`ToMathlib/Analysis/SpecialFunctions/JointEntropy.lean` (the classical-Shannon file that also hosts
N&C Theorem 11.3 and Exercises 11.5/11.6), built on `Real.mutualInfo`:

* `Real.XorMutualInfo.xorDist` — the joint distribution of the triple `(X, Y, Z)`: `X`, `Y`
  independent uniform bits (`ZMod 2`) and `Z = X ⊕ Y`. `Real.XorMutualInfo.xorDist_nonneg` and
  `Real.XorMutualInfo.sum_xorDist` certify it is a genuine probability distribution. The three
  two-variable distributions the exercise compares are all read off this single joint distribution:
  `Real.XorMutualInfo.xorDistPairZ` (the pair `(X, Y)` against `Z`, a regrouping),
  `Real.XorMutualInfo.xorDistXZ` (the `(X, Z)` marginal, summing out `Y`), and
  `Real.XorMutualInfo.xorDistYZ` (the `(Y, Z)` marginal, summing out `X`).
* `Real.XorMutualInfo.mutualInfo_xorDistXZ` and `Real.XorMutualInfo.mutualInfo_xorDistYZ` —
  `H(X : Z) = 0` and `H(Y : Z) = 0`: individually, `X` and `Y` are independent of `Z` (their
  `(·, Z)` marginals are uniform, `xorDistXZ_eq` / `xorDistYZ_eq`).
* `Real.XorMutualInfo.mutualInfo_xorDistPairZ` — `H(X, Y : Z) = Real.log 2` (one bit): the pair
  `(X, Y)` determines `Z`, so `H(X, Y, Z) = H(X, Y)` and only `H(Z)` survives.
* `Real.XorMutualInfo.mutualInfo_xorDist_not_subadditive` — **the exercise's claim (11.34)**:
  `H(X, Y : Z) ≰ H(X : Z) + H(Y : Z)`, since `Real.log 2 > 0 = 0 + 0`.

## Faithfulness note

The library measures entropy in *nats* (natural logarithm), whereas N&C use base-`2` logarithms
(*bits*): N&C's `H(X, Y : Z) = 1` bit is `Real.log 2` nats. A change of logarithm base rescales
every entropy — hence every mutual information — by the same positive factor, so the strict
inequality `H(X, Y : Z) > H(X : Z) + H(Y : Z)` (here `log 2 > 0`) is invariant under the choice of
base. The refutation of (11.34) is therefore faithful to the textbook, not an artefact of the
logarithm convention. `⊕` (addition modulo `2`) is rendered by `+` on `ZMod 2`, the standard model
of the two-element additive group `{0, 1}`.
-/
