/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Matrix.HermitianMajorization

/-!
# Nielsen & Chuang, Theorem 12.13 (operator majorization theorem)

*(N&C p. 575.)*

H prec K (Hermitian) iff H = sum p_j U_j K U_j^dagger.

Here `H ≺ K` means the vector of eigenvalues of `H` is majorized by that of `K` (`Majorize`,
Proposition 12.11).  This is Uhlmann's theorem: majorization of Hermitian operators is exactly the
"random unitary" (mixed-unitary) preorder.

Theorem 12.13 is a purely linear-algebraic statement
about Hermitian matrices over an `RCLike` field — eigenvalue majorization versus expressibility as a
convex combination of unitary conjugates. Compare the neighbouring classical majorization results
Proposition 12.11 (`Proposition12_11`) and Birkhoff's Theorem 12.12 (`Theorem12_12`).

## The formalisation

The formalisation is in `ToMathlib/Analysis/Matrix/HermitianMajorization.lean`
(built on the eigenvalue-majorization API of `ToMathlib/Analysis/Convex/Majorization.lean`, i.e.
Proposition 12.11, and the spectral theorem `Matrix.IsHermitian.spectral_theorem`). N&C's statement
is captured exactly:

* `Matrix.IsHermitian.Majorize hH hK` — N&C's `H ≺ K`, defined as `Majorize hH.eigenvalues
  hK.eigenvalues`: the eigenvalues of `H` are majorized by those of `K`.
* `Matrix.IsHermitian.majorize_iff_exists_sum_smul_unitary_conj` — **Theorem 12.13 itself**:
  `hH.Majorize hK ↔ ∃ (m : ℕ) (p : Fin m → ℝ) (U : Fin m → Matrix n n 𝕜),
  (∀ j, 0 ≤ p j) ∧ (∑ j, p j = 1) ∧ (∀ j, U j ∈ unitaryGroup n 𝕜) ∧
  H = ∑ j, p j • (U j * K * (U j)ᴴ)`. The right-hand side is precisely N&C's `H = ∑ⱼ pⱼ Uⱼ K Uⱼ†`:
  a probability distribution `pⱼ` and unitaries `Uⱼ` with `H` the mixture of the conjugates
  `Uⱼ K Uⱼ†`.

The two directions are also available as standalone theorems:

* `Matrix.IsHermitian.majorize_of_eq_sum_smul_unitary_conj` — the "mixture ⟹ majorization"
  direction, for an *arbitrary* finite index type of unitaries. Reading the joint spectral picture
  `Λ(H) = ∑ⱼ pⱼ Vⱼ Λ(K) Vⱼ†` off its diagonal gives `λ(H) = D *ᵥ λ(K)` with `D` doubly stochastic,
  whence `Majorize.of_mem_doublyStochastic`.
* `Matrix.IsHermitian.exists_eq_sum_smul_unitary_conj_of_majorize` — the "majorization ⟹ mixture"
  direction. From `λ(H) ≺ λ(K)`, Proposition 12.11 (`majorize_iff_exists_sum_perm`) gives convex
  weights `w` over permutations with `λ(H) = ∑_σ wσ (λ(K) ∘ σ)`; lifting to diagonal matrices via
  `Matrix.permMatrix_mul_diagonal_mul_conjTranspose` and conjugating by the spectral unitaries
  produces `H = ∑_σ wσ Uσ K Uσ†` with `Uσ = P · Pσ · Q†` unitary.

Two general matrix facts are proved in
`ToMathlib/LinearAlgebra/Matrix/PermutationUnitary.lean`:
`Matrix.permMatrix_mem_unitaryGroup` (a permutation matrix is unitary) and
`Matrix.permMatrix_mul_diagonal_mul_conjTranspose` (conjugating a diagonal matrix by a permutation
matrix permutes its diagonal).

## Faithfulness

N&C states Theorem 12.13 for Hermitian operators on a finite-dimensional space. The Mathlib
development is stated for Hermitian matrices `H K : Matrix n n 𝕜` over an arbitrary finite index
type `n` and any `RCLike` field `𝕜` (so both `ℝ` and `ℂ`); `n := Fin d`, `𝕜 := ℂ` recovers N&C's
case verbatim. The biconditional's existential quantifies over *some* finite family `Fin m` of
unitaries — exactly N&C's "there is a probability distribution `pⱼ` and unitaries `Uⱼ`" — while
`majorize_of_eq_sum_smul_unitary_conj` establishes the reverse implication for mixtures indexed by
*any* finite type, so nothing is weakened. Both directions are full proofs.
-/
