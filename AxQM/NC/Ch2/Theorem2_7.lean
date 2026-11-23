/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SchmidtDecomposition

/-!
# Nielsen & Chuang, Theorem 2.7 (Schmidt decomposition)

Schmidt decomposition: pure state of AB = sum lambda_i |i_A>|i_B> with orthonormal Schmidt bases.

The Schmidt decomposition is a structural theorem about a pure state of a composite system.
The decomposition `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩` is an equation between the state vectors `.vec`, in
terms of `⊗ₜ`, `S.space` and `Orthonormal`; pure states do not form a vector space, so the
superposition `∑ᵢ λᵢ …` only makes sense for state vectors.

The formalisation is in two files:

* **`AxQM.PureState.exists_schmidt_decomposition`**
  (`AxQM/Postulates/API/SchmidtDecomposition.lean`) — the physical statement: every
  `ψ : PureState (S ⊗ T)` satisfies `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩` with `0 < λᵢ`, `∑ᵢ λᵢ² = 1`, and
  orthonormal Schmidt bases. Stated in **reduced form** (strictly positive coefficients over the
  Schmidt number of terms, genuine orthonormal bases) — a faithful, indeed slightly stronger,
  reformulation of N&C's `λᵢ ≥ 0` over a full basis, and proved for **arbitrary** dimensions of
  `S`, `T` (so N&C's equal-dimension proof and the Exercise 2.76 generalisation are subsumed).

* **`TensorProduct.exists_orthonormal_schmidt`**
  (`ToMathlib/Analysis/InnerProductSpace/SchmidtDecomposition.lean`) — the underlying pure
  mathematics: the Schmidt decomposition of an abstract bipartite tensor `Ψ : E ⊗[𝕜] F`, obtained
  from the singular value decomposition of the matricized coefficient operator
  `M = matricize b Ψ`. The Schmidt coefficients are the nonzero singular values of `M`, the left
  Schmidt basis is its left singular vectors, and the right Schmidt basis is the `b`-conjugate of
  its right singular vectors; `∑ᵢ λᵢ² = ‖Ψ‖²`.
-/
