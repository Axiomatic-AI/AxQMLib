/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TripartiteSchmidt

/-!
# Nielsen & Chuang, Exercise 2.77 (no single Schmidt basis for tripartite states)

Show by example a tripartite ABC state not expressible with a single Schmidt basis.

The exercise shows the bipartite Schmidt decomposition (Theorem 2.7) has **no** direct tripartite
analogue: there is no "single Schmidt basis" (triorthogonal) form for a general three-party state.

The result is a structural statement about a pure state of the composite system
`qubit ⊗ (qubit ⊗ qubit)`. As for the Schmidt decomposition itself (Theorem 2.7), the decomposition
`|ψ⟩ = ∑ᵢ λᵢ (|iᴬ⟩ ⊗ |iᴮ⟩ ⊗ |iᴄ⟩)` is an equation between the state vectors `.vec`, since pure
states do not form a vector space.

The formalisation is in `AxQM/Postulates/API/TripartiteSchmidt.lean`:

* `AxQM.PureState.HasTriorthogonalDecomposition` — the tripartite "single Schmidt basis"
  form `|ψ⟩ = ∑ᵢ λᵢ (aᵢ ⊗ bᵢ ⊗ cᵢ)` with orthonormal families `{aᵢ}`, `{bᵢ}`, `{cᵢ}` and real
  `λᵢ`. (Stated with orthonormal *families*, subsuming N&C's orthonormal *bases*.)
* `AxQM.zeroTensorBell` — the counterexample `|0⟩ ⊗ |Φ⁺⟩` on `qubit ⊗ (qubit ⊗ qubit)`.
* `AxQM.zeroTensorBell_not_hasTriorthogonalDecomposition` — `|0⟩ ⊗ |Φ⁺⟩` has no
  triorthogonal decomposition.

The device that isolates one term of the decomposition — the partial inner product
`TensorProduct.contractFst` / `contractFst_tmul` (`x ⊗ w ↦ ⟨v|x⟩ • w`) — is general
inner-product/tensor mathematics, in `ToMathlib/Analysis/InnerProductSpace/TensorProduct.lean`
(next to `rankOne_tmul_self`).

The proof contracts the `A`-factor of a hypothetical decomposition against `aₖ`: orthonormality of
`{aᵢ}` collapses the sum to `⟨aₖ|0⟩ • |Φ⁺⟩ = λₖ • (bₖ ⊗ cₖ)`, so a nonzero term forces the entangled
Bell vector `|Φ⁺⟩` to be a simple tensor — contradicting `Concrete.bellVector_ne_tmul`
(Exercise 2.68).
-/
