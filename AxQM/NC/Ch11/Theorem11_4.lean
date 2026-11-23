/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.ConditionalEntropyChain

/-!
# Nielsen & Chuang, Theorem 11.4 (Chaining rule for conditional entropies)

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.4, p. 508.

Chaining rule for conditional entropies: H(X1..Xn|Y)=sum H(Xi|Y,X1..Xi-1).

Here `H(X, Y) = −∑_{x,y} p(x, y) log p(x, y)` is the joint entropy and `H(X | Y) = H(X, Y) − H(Y)`
is the conditional entropy (eq. (11.19)).

The statement is a real-analysis identity about the Shannon entropies of finite-alphabet random
variables.

**Model and base convention.** `Real.condEntropy`
(`ToMathlib/Analysis/SpecialFunctions/JointEntropy.lean`, N&C Theorem 11.3 substrate) is defined on
a
joint distribution `p : ι × κ → ℝ` as `H(X | Y) = H(X, Y) − H(Y)`. To express the prefix marginals
`Y, X₁, …, Xᵢ₋₁` appearing in the chaining rule, each variable is modelled as a random variable on a
common finite sample space `Ω` with weight `μ : Ω → ℝ`, and `Real.condEntropy` is applied to the
resulting joint *laws* — so every marginal is automatically the law of a sub-tuple, with no ad-hoc
coordinate projection. The alphabets `X₁, …, Xₙ` are a common finite type `α` (WLOG: any finite
family of finite alphabets recodes injectively into a common one, leaving every entropy unchanged);
`Y` has alphabet `β`. Entropy is measured in *nats* (natural log), matching `Real.entropy`; the
identity is base-invariant (both sides scale by the same factor under a change of logarithm base),
so this is a faithful reformulation of N&C's base-2 statement, and it holds for any weight `μ` (no
normalisation needed).

The formalisation is in `ToMathlib/Analysis/SpecialFunctions/ConditionalEntropyChain.lean`:

* `Real.law` — the law (push-forward distribution) `law μ X x = ∑_{ω : X ω = x} μ ω` of a random
  variable `X : Ω → γ`; the joint law of `(X, Y)` is `law μ (fun ω ↦ (X ω, Y ω))`, whose
  `Real.condEntropy` is `H(X | Y)`.
* `Real.entropy_law_congr_equiv`, `Real.marginalSnd_law_prod` — the two bridges the chaining rule
  rests on: joint entropy is invariant under a bijective relabeling of the alphabet (used to reorder
  the components of a tuple), and the second marginal of a joint law is the law of the second
  variable (so `Real.condEntropy` of a joint law is `H(X, Y) − H(Y)`).
* `Real.condEntropy_law_chain` — **Theorem 11.4**: for a sequence of random variables
  `X : ℕ → Ω → α` (of which the first `n` enter) and `Y : Ω → β`,
  `H(X₀, …, X_{n-1} | Y) = ∑ᵢ H(Xᵢ | Y, X₀, …, Xᵢ₋₁)`. Proved by telescoping the joint entropies
  `G k = H(Y, X₀, …, X_{k-1})` of the prefixes: each summand is `G (i+1) − G i`, and the head
  conditional entropy is `G n − G 0`.
-/
