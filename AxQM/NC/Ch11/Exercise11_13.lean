/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EntropyComposite

/-!
# N&C Exercise 11.13 — Entropy of a tensor product

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.13, p. 514.

Show S(rho⊗sigma)=S(rho)+S(sigma) via joint entropy theorem and directly.

The exercise's content is the single additivity identity: the von Neumann entropy of an
uncorrelated composite `ρ ⊗ σ` is the sum of the entropies of its parts,

`S(ρ ⊗ σ) = S(ρ) + S(σ)`,

for arbitrary states `ρ` on a system `S` and `σ` on a system `T` (no purity, rank, or
dimension restriction). The two clauses ("via the joint entropy theorem" and "directly from the
definition") are the two proof routes N&C suggests for that one equation, not two separate claims.

## Where the formalisation lives

The identity is stated for the entropy `State.vonNeumannEntropy` and the product state `State.tmul`:
`(ρ.tmul σ).vonNeumannEntropy = ρ.vonNeumannEntropy + σ.vonNeumannEntropy`. It is used elsewhere,
e.g. for the tensor-iid scaling `S(ρ^⊗ⁿ) = n · S(ρ)`
(`ContinuousLinearMap.IsDensityOp.vonNeumannEntropy_tensorPow`) and in the Problem 11.3
conditional-entropy development, and is proved in `AxQM/Postulates/API/EntropyComposite.lean`,
alongside the mixture bound (Theorem 11.10) and the relative-entropy theorems on the same route.

The declaration:

* `AxQM.State.vonNeumannEntropy_tmul`
  (`AxQM/Postulates/API/EntropyComposite.lean`) — **`S(ρ ⊗ σ) = S(ρ) + S(σ)`**, stated
  for `State.vonNeumannEntropy` and `State.tmul` (with `(ρ.tmul σ).op = ρ.op ⊗ σ.op`
  by `State.tmul_op`). It lifts the operator-level theorem
  `ContinuousLinearMap.IsDensityOp.vonNeumannEntropy_tensorMap`
  (`ToMathlib/Analysis/InnerProductSpace/VonNeumannEntropy.lean`) to states,
  using the density-operator witnesses `ρ.isDensity` / `σ.isDensity`.

## The two N&C proof routes, mapped to the library

Both routes reduce, for general states, to the same fact about the eigenvalue spectra, and that is
how the formalisation proves the identity. `State.vonNeumannEntropy` is defined as the Shannon
entropy `Real.entropy` of the eigenvalue spectrum of `ρ.op`.

* **Route 1 — via the joint entropy theorem** (N&C's first suggestion). The joint entropy theorem
  (Theorem 11.8, part 5) gives `S(∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)`; specialising to the
  spectral decomposition `ρ = ∑ᵢ pᵢ |i⟩⟨i|` and `ρᵢ ≡ σ` yields
  `S(ρ ⊗ σ) = H(p) + ∑ᵢ pᵢ S(σ) = S(ρ) + S(σ)` (since `∑ᵢ pᵢ = 1` and `H(p) = S(ρ)`). The
  distributional heart of this specialisation is that the spectrum of `ρ ⊗ σ` is the product
  `{λᵢ μⱼ}` of the two spectra and the Shannon entropy of a product distribution is additive; the
  operator-level proof captures exactly that, via the eigenvalue-multiset bridge
  `LinearMap.IsSymmetric.vonNeumannEntropy_tensorMap_of_sum_eigenvalues_eq_one` and the
  product-distribution additivity `Real.entropy_prod`.
  (The joint entropy theorem itself — N&C Theorem 11.8 part 5 — is a separate item,
  `Theorem11_8`; it is not needed as a lemma here, since the product-spectrum additivity it
  specialises to is available directly.)

* **Route 2 — directly from the definition** (N&C's second suggestion), `S(ρ) ≡ −tr(ρ log ρ)`.
  Writing `S(ρ ⊗ σ) = −tr((ρ ⊗ σ) log(ρ ⊗ σ))` and using the operator-log factorisation
  `log(ρ ⊗ σ) = log ρ ⊗ I + I ⊗ log σ` (`IsSelfAdjoint.cfc_log_tensorMap`, for strictly positive
  spectra) plus multiplicativity of the trace over a tensor product
  (`ContinuousLinearMap.trace_mapL`, `tr(A ⊗ B) = tr A · tr B`) and `tr ρ = tr σ = 1` gives
  `S(ρ ⊗ σ) = −tr(ρ log ρ) · tr σ − tr ρ · tr(σ log σ) = S(ρ) + S(σ)`. The bridge from N&C's trace
  definition to the spectral one used here is
  `ContinuousLinearMap.IsDensityOp.re_trace_cfc_log_self_eq_neg_vonNeumannEntropy`
  (`re tr((cfc log ρ) ∘ ρ) = −S(ρ)`, for any density operator). The operator identity
  `log(ρ ⊗ σ) = log ρ ⊗ I + I ⊗ log σ` requires strictly positive spectra, but the *traced* quantity
  `tr((ρ ⊗ σ) log(ρ ⊗ σ))` factors for every state through the removable singularity `0·log 0 = 0`,
  so the general (possibly rank-deficient) case coincides with the product-spectrum computation of
  Route 1 — which is why the single spectral proof above discharges both routes uniformly.

## Faithfulness

The statement is fully general — arbitrary `ρ`, `σ`, arbitrary finite dimensions, no faithfulness
or purity hypothesis — matching the exercise exactly; nothing is weakened. `Real.entropy` (hence
`State.vonNeumannEntropy`) is the entropy in nats (natural log); the additivity identity is
invariant under the choice of logarithm base (both sides scale by the same factor), a faithful
base-independent rendering of N&C's base-2 presentation.
-/
