/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Composite
import ToMathlib.Analysis.InnerProductSpace.SchmidtDecomposition

/-!
# AxQM — the Schmidt decomposition of a bipartite pure state (Nielsen–Chuang Theorem 2.7)

The **Schmidt decomposition** (N&C §2.5, Theorem 2.7): every pure state `|ψ⟩` of a composite
system `S ⊗ T` can be written

  `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩`,

where the **Schmidt coefficients** `λᵢ` are strictly positive reals with `∑ᵢ λᵢ² = 1`, and the
**Schmidt bases** `{|iᴬ⟩}` (in `S`) and `{|iᴮ⟩}` (in `T`) are orthonormal families.

## Statement shape and faithfulness

We state the decomposition in **reduced form**: the sum ranges over `Fin n` with `n` the Schmidt
number (the number of *nonzero* Schmidt coefficients), the coefficients `λᵢ` are *strictly
positive* (`0 < λᵢ`), and the Schmidt bases are *genuine* orthonormal families (`Orthonormal`).
This is a faithful reformulation of N&C — indeed strictly stronger than the textbook's `λᵢ ≥ 0`
over a full basis, since the positive-coefficient form implies the padded form and the two are
equivalent (drop/append zero terms). N&C proves the equal-dimension case (leaving the general
case to Exercise 2.76); we prove it for **arbitrary** dimensions of `S` and `T`, which is more
general, not a weakening.

The statement of Theorem 2.7 is in `AxQM/NC/Ch2/Theorem2_7.lean`.

## Proof

The mathematical core is the abstract Schmidt decomposition of a bipartite *tensor*,
`TensorProduct.exists_orthonormal_schmidt` (`ToMathlib`), obtained from the singular value
decomposition of the matricized coefficient operator `M = matricize ψ.vec`. Here we specialize
it to `ψ.vec` and use the pure-state normalization `‖ψ.vec‖ = 1` (`PureState.normalized`) to turn
the abstract identity `∑ᵢ λᵢ² = ‖ψ.vec‖²` into `∑ᵢ λᵢ² = 1`.

## Main results

* `AxQM.PureState.exists_schmidt_decomposition` — the Schmidt decomposition of a
  bipartite pure state.
* `AxQM.PureState.exists_schmidt_decomposition_card_le` — **Exercise 2.76**: the same
  decomposition with the number of Schmidt terms bounded by the *smaller* subsystem dimension,
  `n ≤ min S.dim T.dim` (the extension to unequal dimensions).
* `AxQM.PureState.IsSchmidtDecomposition` — the predicate "`(l, a, b)` is a (reduced)
  Schmidt decomposition of `ψ`", with `PureState.exists_isSchmidtDecomposition` its existence form
  (used to state a *concrete* state's Schmidt decomposition as a single reusable claim, e.g.
  **Exercise 2.79**).
* `AxQM.PureState.SameSchmidtCoeffs` — the predicate "`ψ` and `φ` have **identical Schmidt
  coefficients**" (a common strictly-positive coefficient family over orthonormal Schmidt bases),
  the hypothesis of **Exercise 2.80**.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **Schmidt decomposition (Nielsen–Chuang Theorem 2.7).** Every bipartite pure state
`ψ : PureState (S ⊗ T)` decomposes as `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩` for strictly positive Schmidt
coefficients `λᵢ` (with `∑ᵢ λᵢ² = 1`) and orthonormal Schmidt bases `{|iᴬ⟩}` (in `S`),
`{|iᴮ⟩}` (in `T`). Proved for arbitrary dimensions of `S` and `T` (N&C's equal-dimension proof
and Exercise 2.76 together; here uniform via the SVD). Specializes the abstract tensor Schmidt
decomposition `TensorProduct.exists_orthonormal_schmidt` to `ψ.vec`, converting `∑ᵢ λᵢ² = ‖ψ.vec‖²`
to `∑ᵢ λᵢ² = 1` via `ψ.normalized`. -/
theorem PureState.exists_schmidt_decomposition (ψ : PureState (S ⊗ T)) :
    ∃ (n : ℕ) (l : Fin n → ℝ) (a : Fin n → S.space) (b : Fin n → T.space),
      (∀ i, 0 < l i) ∧ Orthonormal ℂ a ∧ Orthonormal ℂ b ∧
      (∑ i, l i ^ 2 = 1) ∧ ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i := by
  obtain ⟨n, l, a, b, hl, ha, hb, hsum, hdecomp⟩ :=
    TensorProduct.exists_orthonormal_schmidt (ψ.vec : S.space ⊗[ℂ] T.space)
  refine ⟨n, l, a, b, hl, ha, hb, ?_, hdecomp⟩
  rw [hsum]
  -- the tensor-product norm of `ψ.vec` is defeq to its norm as a state vector, which is `1`.
  change ‖ψ.vec‖ ^ 2 = 1
  rw [ψ.normalized, one_pow]

/-- **Schmidt decomposition for subsystems of possibly unequal dimension (Nielsen–Chuang
Exercise 2.76).** Every bipartite pure state `ψ : PureState (S ⊗ T)` decomposes as
`|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩` (`exists_schmidt_decomposition`) with the number of Schmidt terms bounded
by the *smaller* of the two subsystem dimensions, `n ≤ min S.dim T.dim`.

This is the content of N&C's Exercise 2.76. N&C prove Theorem 2.7 in the equal-dimension case,
where the coefficient array `a` (with `|ψ⟩ = ∑ⱼₖ aⱼₖ |j⟩|k⟩`) is a *square* matrix and its SVD
`a = u d v` uses square unitaries; extending the proof to `dim A ≠ dim B` makes `a` *rectangular*,
and the number of nonzero singular values — the number of Schmidt terms — is at most
`min(#rows, #cols) = min(dim A, dim B)`. Formally the bound is immediate from the Schmidt bases
being orthonormal families: `{|iᴬ⟩}` are `n` orthonormal vectors of `S.space` (so `n ≤ dim A`) and
`{|iᴮ⟩}` are `n` orthonormal vectors of `T.space` (so `n ≤ dim B`), whence `n ≤ min(dim A, dim B)`.
It is a strict *strengthening* of `exists_schmidt_decomposition`, not a weakening: it adds the term
bound and reuses that theorem's decomposition verbatim, bounding its term count via
`LinearIndependent.fintype_card_le_finrank`. -/
theorem PureState.exists_schmidt_decomposition_card_le (ψ : PureState (S ⊗ T)) :
    ∃ (n : ℕ) (l : Fin n → ℝ) (a : Fin n → S.space) (b : Fin n → T.space),
      n ≤ min S.dim T.dim ∧ (∀ i, 0 < l i) ∧ Orthonormal ℂ a ∧ Orthonormal ℂ b ∧
      (∑ i, l i ^ 2 = 1) ∧ ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i := by
  obtain ⟨n, l, a, b, hl, ha, hb, hsum, hdecomp⟩ := ψ.exists_schmidt_decomposition
  refine ⟨n, l, a, b, le_min ?_ ?_, hl, ha, hb, hsum, hdecomp⟩
  · -- `n = card (Fin n) ≤ dim A`, the `n` orthonormal left Schmidt vectors living in `S.space`.
    simpa [QSystem.dim] using ha.linearIndependent.fintype_card_le_finrank
  · -- `n = card (Fin n) ≤ dim B`, the `n` orthonormal right Schmidt vectors living in `T.space`.
    simpa [QSystem.dim] using hb.linearIndependent.fintype_card_le_finrank

/-- **`(l, a, b)` is a Schmidt decomposition of the bipartite pure state `ψ`.** The data of a
Schmidt decomposition `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩` (Nielsen–Chuang Theorem 2.7), stated in reduced
form: strictly positive Schmidt coefficients `l : Fin n → ℝ`, orthonormal Schmidt bases
`a : Fin n → S.space` and `b : Fin n → T.space`, normalisation `∑ᵢ lᵢ² = 1`, and the identity
`ψ.vec = ∑ᵢ (lᵢ : ℂ) • aᵢ ⊗ₜ bᵢ`. Its fields are exactly the conclusion of
`PureState.exists_schmidt_decomposition`; naming the concept lets a *concrete* state's Schmidt
decomposition be a single, reusable claim (e.g. N&C Exercise 2.79). -/
def PureState.IsSchmidtDecomposition (ψ : PureState (S ⊗ T)) {n : ℕ}
    (l : Fin n → ℝ) (a : Fin n → S.space) (b : Fin n → T.space) : Prop :=
  (∀ i, 0 < l i) ∧ Orthonormal ℂ a ∧ Orthonormal ℂ b ∧
    (∑ i, l i ^ 2 = 1) ∧ ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i

/-- **Schmidt decomposition (Nielsen–Chuang Theorem 2.7), packaged via the predicate.** Every
bipartite pure state admits *some* Schmidt decomposition: `∃ n l a b, ψ.IsSchmidtDecomposition
l a b`. This is `PureState.exists_schmidt_decomposition` reread through
`PureState.IsSchmidtDecomposition`, confirming the predicate captures exactly the theorem's
conclusion. -/
theorem PureState.exists_isSchmidtDecomposition (ψ : PureState (S ⊗ T)) :
    ∃ (n : ℕ) (l : Fin n → ℝ) (a : Fin n → S.space) (b : Fin n → T.space),
      ψ.IsSchmidtDecomposition l a b :=
  ψ.exists_schmidt_decomposition

/-- **Two bipartite pure states have identical Schmidt coefficients** (the hypothesis of
Nielsen–Chuang Exercise 2.80). `ψ` and `φ` share a common family of Schmidt coefficients
`l : Fin n → ℝ` — strictly positive reals, `n` the Schmidt number — in the sense that each admits a
reduced Schmidt decomposition over orthonormal Schmidt bases with those *same* coefficients:
`|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩` and `|φ⟩ = ∑ᵢ λᵢ |i'ᴬ⟩|i'ᴮ⟩`.

Since the Schmidt coefficients are the (uniquely determined) nonzero singular values of the
matricized state, this existential — a common *ordered* coefficient family `l` — holds exactly when
`ψ` and `φ` have the same Schmidt coefficients as a multiset: given equal multisets, permute one
decomposition's index to match the other. So the predicate is a faithful rendering of "identical
Schmidt coefficients", neither stronger nor weaker.

It is the hypothesis of `PureState.exists_evolution_tmul_of_sameSchmidtCoeffs`
(`AxQM/NC/Ch2/Exercise2_80.lean`). -/
def PureState.SameSchmidtCoeffs (ψ φ : PureState (S ⊗ T)) : Prop :=
  ∃ (n : ℕ) (l : Fin n → ℝ) (a a' : Fin n → S.space) (b b' : Fin n → T.space),
    (∀ i, 0 < l i) ∧ Orthonormal ℂ a ∧ Orthonormal ℂ b ∧ Orthonormal ℂ a' ∧ Orthonormal ℂ b' ∧
      ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i ∧ φ.vec = ∑ i, (l i : ℂ) • a' i ⊗ₜ[ℂ] b' i

end AxQM
