/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import ToMathlib.Analysis.Convex.Majorization
public import ToMathlib.LinearAlgebra.Matrix.PermutationUnitary

/-!
# Majorization of Hermitian matrices

For Hermitian matrices `H`, `K` over an `RCLike` field, Nielsen and Chuang write `H ≺ K` to mean
that the vector of eigenvalues of `H` is majorized by that of `K`, `λ(H) ≺ λ(K)` (`Majorize`, from
`ToMathlib/Analysis/Convex/Majorization.lean`).  This file records that relation as
`Matrix.IsHermitian.Majorize` and proves the operator majorization theorem (Nielsen–Chuang,
*Quantum Computation and Quantum Information*, Theorem 12.13):

> `H ≺ K` if and only if `H = ∑ⱼ pⱼ Uⱼ K Uⱼ†` for a probability distribution `pⱼ` and unitaries
> `Uⱼ`.

The "easy" (mixture ⟹ majorization) direction works in the joint picture supplied by the spectral
theorem: writing
`Λ(H) = star P * H * P` and `K = Q * Λ(K) * star Q` for the eigenvector unitaries `P`, `Q`, the
hypothesis becomes `Λ(H) = ∑ⱼ pⱼ Vⱼ Λ(K) Vⱼ†` with `Vⱼ = star P * Uⱼ * Q` unitary.  Reading off
the `(k, k)` diagonal entry gives `λ(H) = D *ᵥ λ(K)` for the real matrix `D k l = ∑ⱼ pⱼ ‖Vⱼ k l‖²`,
which
is doubly stochastic because the rows and columns of each `Vⱼ` are unit vectors; the conclusion is
then `Majorize.of_mem_doublyStochastic`.

The converse (majorization ⟹ mixture) is the substance of Theorem 12.13.  From `H ≺ K` — i.e.
`λ(H) ≺ λ(K)` — Proposition 12.11 (`majorize_iff_exists_sum_perm`) supplies convex weights `w` over
permutations `σ` with `λ(H) = ∑_σ wσ (λ(K) ∘ σ)`.  Lifting to the diagonal picture via
`permMatrix_mul_diagonal_mul_conjTranspose` (a permutation matrix conjugates a diagonal matrix to
the permuted diagonal) and assembling with the spectral theorem gives
`H = ∑_σ wσ Uσ K Uσ†` with `Uσ = P · Pσ · Q†` unitary, where `P`, `Q` diagonalise `H`, `K`.

## Main definitions

* `Matrix.IsHermitian.Majorize hH hK`: the eigenvalues of `H` are majorized by those of `K`.

## Main statements

* `Matrix.sum_sq_norm_row_of_mem_unitaryGroup`, `Matrix.sum_sq_norm_col_of_mem_unitaryGroup`: the
  entries in each row (resp. column) of a unitary matrix have squared norms summing to `1`.
* `Matrix.IsHermitian.majorize_of_eq_sum_smul_unitary_conj`: the "mixture implies majorization"
  direction of Theorem 12.13.
* `Matrix.IsHermitian.exists_eq_sum_smul_unitary_conj_of_majorize`: the converse "majorization
  implies mixture" direction.
* `Matrix.IsHermitian.majorize_iff_exists_sum_smul_unitary_conj`: Theorem 12.13 itself, the
  biconditional `H ≺ K ↔ H = ∑ⱼ pⱼ Uⱼ K Uⱼ†`.

## Tags

majorization, Hermitian matrix, doubly stochastic, unitary
-/

public section

open Finset Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared norms of the entries in a single row of a unitary matrix sum to `1`
(the rows of a unitary matrix are unit vectors). -/
lemma sum_sq_norm_row_of_mem_unitaryGroup {U : Matrix n n 𝕜} (hU : U ∈ unitaryGroup n 𝕜) (k : n) :
    ∑ l, ‖U k l‖ ^ 2 = 1 := by
  have h1 : (U * star U) k k = 1 := by rw [mem_unitaryGroup_iff.mp hU, Matrix.one_apply_eq]
  have h2 : (U * star U) k k = ((∑ l, ‖U k l‖ ^ 2 : ℝ) : 𝕜) := by
    rw [Matrix.mul_apply, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.star_apply, ← starRingEnd_apply, RCLike.mul_conj, RCLike.ofReal_pow]
  exact_mod_cast h2.symm.trans h1

/-- The squared norms of the entries in a single column of a unitary matrix sum to `1`
(the columns of a unitary matrix are unit vectors). -/
lemma sum_sq_norm_col_of_mem_unitaryGroup {U : Matrix n n 𝕜} (hU : U ∈ unitaryGroup n 𝕜) (l : n) :
    ∑ k, ‖U k l‖ ^ 2 = 1 := by
  have h1 : (star U * U) l l = 1 := by rw [mem_unitaryGroup_iff'.mp hU, Matrix.one_apply_eq]
  have h2 : (star U * U) l l = ((∑ k, ‖U k l‖ ^ 2 : ℝ) : 𝕜) := by
    rw [Matrix.mul_apply, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.star_apply, ← starRingEnd_apply, RCLike.conj_mul, RCLike.ofReal_pow]
  exact_mod_cast h2.symm.trans h1

/-- The `(k, k)` diagonal entry of a diagonal matrix conjugated by `A`.  For a real vector `d`,
`(A * diagonal (↑ ∘ d) * Aᴴ) k k = ∑ l, d l * ‖A k l‖²` (cast into `𝕜`): the diagonal of a
unitary-style conjugation of a real diagonal matrix is a real combination of the diagonal entries
weighted by the squared entry norms. -/
lemma diag_mul_diagonal_mul_conjTranspose (A : Matrix n n 𝕜) (d : n → ℝ) (k : n) :
    (A * diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ d) * star A) k k
      = ((∑ l, d l * ‖A k l‖ ^ 2 : ℝ) : 𝕜) := by
  rw [Matrix.mul_apply, RCLike.ofReal_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_diagonal, Matrix.star_apply, Function.comp_apply, ← starRingEnd_apply,
    mul_right_comm, RCLike.mul_conj]
  push_cast
  ring

namespace IsHermitian

variable {H K : Matrix n n 𝕜}

/-- Majorization of Hermitian matrices (Nielsen–Chuang §12.5): `hH.Majorize hK` means the vector of
eigenvalues of `H` is majorized by that of `K`.  Written `H ≺ K` in Nielsen and Chuang. -/
def Majorize (hH : H.IsHermitian) (hK : K.IsHermitian) : Prop :=
  _root_.Majorize hH.eigenvalues hK.eigenvalues

/-- The "mixture implies majorization" direction of Nielsen–Chuang Theorem 12.13: if a Hermitian
matrix `H` is a probabilistic mixture `H = ∑ⱼ pⱼ Uⱼ K Uⱼ†` of unitary conjugates of a Hermitian
matrix `K`, then `H ≺ K`, i.e. the eigenvalues of `H` are majorized by those of `K`. -/
theorem majorize_of_eq_sum_smul_unitary_conj (hH : H.IsHermitian) (hK : K.IsHermitian)
    {ι : Type*} [Fintype ι] {p : ι → ℝ} {U : ι → Matrix n n 𝕜}
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (hU : ∀ j, U j ∈ unitaryGroup n 𝕜)
    (hHK : H = ∑ j, p j • (U j * K * (U j)ᴴ)) :
    hH.Majorize hK := by
  set P : Matrix n n 𝕜 := (hH.eigenvectorUnitary : Matrix n n 𝕜) with hP
  set Q : Matrix n n 𝕜 := (hK.eigenvectorUnitary : Matrix n n 𝕜) with hQ
  -- Spectral diagonalizations: `star P * H * P = Λ(H)` and `K = Q * Λ(K) * star Q`.
  have hLH : star P * H * P = diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    simpa only [Unitary.conjStarAlgAut_star_apply, ← hP] using
      hH.conjStarAlgAut_star_eigenvectorUnitary
  have hKs : K = Q * diagonal (RCLike.ofReal ∘ hK.eigenvalues) * star Q := by
    simpa only [Unitary.conjStarAlgAut_apply, ← hQ] using hK.spectral_theorem
  -- The conjugating unitaries `Vⱼ = star P * Uⱼ * Q` and the extracted real matrix `D`.
  set V : ι → Matrix n n 𝕜 := fun j => star P * U j * Q with hV
  set D : Matrix n n ℝ := fun k l => ∑ j, p j * ‖V j k l‖ ^ 2 with hD
  have hVunit : ∀ j, V j ∈ unitaryGroup n 𝕜 := by
    intro j
    simp only [hV, hP, hQ]
    exact mul_mem (mul_mem (Unitary.star_mem (SetLike.coe_mem _)) (hU j)) (SetLike.coe_mem _)
  -- `Λ(H) = ∑ⱼ pⱼ Vⱼ Λ(K) Vⱼ†`.
  have hstar : diagonal (RCLike.ofReal ∘ hH.eigenvalues)
      = ∑ j, p j • (V j * diagonal (RCLike.ofReal ∘ hK.eigenvalues) * star (V j)) := by
    rw [← hLH, hHK, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    simp only [hV, hKs, ← Matrix.star_eq_conjTranspose, star_mul, star_star, mul_assoc]
  -- Read off the `(k, k)` entry to obtain `λ(H) = D *ᵥ λ(K)`.
  have key : hH.eigenvalues = D *ᵥ hK.eigenvalues := by
    funext k
    have hkk := congrFun (congrFun hstar k) k
    rw [Matrix.diagonal_apply_eq, Matrix.sum_apply, Function.comp_apply] at hkk
    simp only [Matrix.smul_apply, diag_mul_diagonal_mul_conjTranspose,
      RCLike.real_smul_eq_coe_mul, ← RCLike.ofReal_mul, ← RCLike.ofReal_sum] at hkk
    have hkk' := RCLike.ofReal_injective hkk
    have hmulvec : (D *ᵥ hK.eigenvalues) k
        = ∑ l, (∑ j, p j * ‖V j k l‖ ^ 2) * hK.eigenvalues l := by simp only [hD]; rfl
    rw [hkk', hmulvec]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring
  -- `D` is doubly stochastic, so `D *ᵥ λ(K) ≺ λ(K)`.
  have hDds : D ∈ doublyStochastic ℝ n := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun k l => ?_, fun k => ?_, fun l => ?_⟩
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (hp j) (sq_nonneg _)
    · simp only [hD]
      rw [Finset.sum_comm]
      have hrow : ∀ j, ∑ l, p j * ‖V j k l‖ ^ 2 = p j := fun j => by
        rw [← Finset.mul_sum, sum_sq_norm_row_of_mem_unitaryGroup (hVunit j) k, mul_one]
      simp_rw [hrow]; exact hp1
    · simp only [hD]
      rw [Finset.sum_comm]
      have hcol : ∀ j, ∑ k, p j * ‖V j k l‖ ^ 2 = p j := fun j => by
        rw [← Finset.mul_sum, sum_sq_norm_col_of_mem_unitaryGroup (hVunit j) l, mul_one]
      simp_rw [hcol]; exact hp1
  have hmaj := _root_.Majorize.of_mem_doublyStochastic hDds hK.eigenvalues
  rw [← key] at hmaj
  exact hmaj

/-- The "majorization implies mixture" direction of Nielsen–Chuang Theorem 12.13: if a Hermitian
matrix `H` is majorized by a Hermitian matrix `K` (`H ≺ K`), then `H` is a probabilistic mixture of
unitary conjugates of `K`, `H = ∑_σ pσ Uσ K Uσ†`.  The mixture is indexed by the permutations `σ`
of `n`: with `w` the convex weights of Proposition 12.11 (`majorize_iff_exists_sum_perm`) for the
eigenvalue majorization `λ(H) ≺ λ(K)`, the conjugating unitaries are `Uσ = P · Pσ · Q†`, where
`P`, `Q` diagonalise `H`, `K` and `Pσ` is the permutation matrix of `σ`. -/
theorem exists_eq_sum_smul_unitary_conj_of_majorize (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hHK : hH.Majorize hK) :
    ∃ (p : Equiv.Perm n → ℝ) (U : Equiv.Perm n → Matrix n n 𝕜),
      (∀ σ, 0 ≤ p σ) ∧ (∑ σ, p σ = 1) ∧ (∀ σ, U σ ∈ unitaryGroup n 𝕜) ∧
        H = ∑ σ, p σ • (U σ * K * (U σ)ᴴ) := by
  obtain ⟨w, hwpos, hwsum, hweq⟩ := majorize_iff_exists_sum_perm.mp hHK
  set P : Matrix n n 𝕜 := (hH.eigenvectorUnitary : Matrix n n 𝕜) with hP
  set Q : Matrix n n 𝕜 := (hK.eigenvectorUnitary : Matrix n n 𝕜) with hQ
  have hPmem : P ∈ unitaryGroup n 𝕜 := SetLike.coe_mem _
  have hQmem : Q ∈ unitaryGroup n 𝕜 := SetLike.coe_mem _
  have hQQ : star Q * Q = 1 := mem_unitaryGroup_iff'.mp hQmem
  have hc : ∀ X : Matrix n n 𝕜, star Q * (Q * X) = X := fun X => by rw [← mul_assoc, hQQ, one_mul]
  -- Spectral decompositions `H = P · Λ(H) · P†`, `K = Q · Λ(K) · Q†`.
  have hHspec : H = P * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star P := by
    simpa only [Unitary.conjStarAlgAut_apply, ← hP] using hH.spectral_theorem
  have hKspec : K = Q * diagonal (RCLike.ofReal ∘ hK.eigenvalues) * star Q := by
    simpa only [Unitary.conjStarAlgAut_apply, ← hQ] using hK.spectral_theorem
  -- Lift `λ(H) = ∑_σ wσ (λ(K) ∘ σ)` to the diagonal matrices.
  have hdiag : diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ hH.eigenvalues)
      = ∑ σ, w σ • diagonal (((RCLike.ofReal : ℝ → 𝕜) ∘ hK.eigenvalues) ∘ (σ : n → n)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.sum_apply, Matrix.smul_apply, diagonal_apply_eq, Function.comp_apply]
      have hi := congrFun hweq i
      rw [Finset.sum_apply] at hi
      simp only [Pi.smul_apply, permMatrix_mulVec, Function.comp_apply, smul_eq_mul] at hi
      rw [hi, RCLike.ofReal_sum]
      exact Finset.sum_congr rfl fun σ _ => by
        rw [RCLike.ofReal_mul, RCLike.real_smul_eq_coe_mul]
    · simp only [Matrix.sum_apply, Matrix.smul_apply, diagonal_apply_ne _ h, smul_zero,
        Finset.sum_const_zero]
  refine ⟨w, fun σ => P * σ.permMatrix 𝕜 * star Q, hwpos, hwsum, fun σ =>
    mul_mem (mul_mem hPmem (permMatrix_mem_unitaryGroup σ)) (Unitary.star_mem hQmem), ?_⟩
  -- Each mixture term collapses to `P · diagonal(λ(K) ∘ σ) · P†`.
  have hterm : ∀ σ : Equiv.Perm n,
      (P * σ.permMatrix 𝕜 * star Q) * K * (P * σ.permMatrix 𝕜 * star Q)ᴴ
        = P * diagonal ((RCLike.ofReal ∘ hK.eigenvalues) ∘ (σ : n → n)) * star P := by
    intro σ
    -- Substitute only the standalone `K` (not the `K` implicit in `hK.eigenvalues` on the right).
    conv_lhs => rw [hKspec]
    rw [← permMatrix_mul_diagonal_mul_conjTranspose σ ((RCLike.ofReal : ℝ → 𝕜) ∘ hK.eigenvalues)]
    simp only [← star_eq_conjTranspose, star_mul, star_star, mul_assoc]
    rw [hc, hc]
  calc H = P * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star P := hHspec
    _ = P * (∑ σ, w σ • diagonal ((RCLike.ofReal ∘ hK.eigenvalues) ∘ (σ : n → n))) * star P := by
        rw [hdiag]
    _ = ∑ σ, w σ • (P * diagonal ((RCLike.ofReal ∘ hK.eigenvalues) ∘ (σ : n → n)) * star P) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun σ _ => by rw [mul_smul_comm, smul_mul_assoc]
    _ = ∑ σ, w σ • ((P * σ.permMatrix 𝕜 * star Q) * K * (P * σ.permMatrix 𝕜 * star Q)ᴴ) :=
        Finset.sum_congr rfl fun σ _ => by rw [hterm]

/-- **Nielsen–Chuang Theorem 12.13** (Uhlmann's operator majorization theorem): for Hermitian
matrices `H`, `K`, the eigenvalues of `H` are majorized by those of `K` (`H ≺ K`) if and only if
`H` is a probabilistic mixture of unitary conjugates of `K`, `H = ∑ⱼ pⱼ Uⱼ K Uⱼ†` for some
probability distribution `pⱼ` and unitaries `Uⱼ`. -/
theorem majorize_iff_exists_sum_smul_unitary_conj (hH : H.IsHermitian) (hK : K.IsHermitian) :
    hH.Majorize hK ↔
      ∃ (m : ℕ) (p : Fin m → ℝ) (U : Fin m → Matrix n n 𝕜),
        (∀ j, 0 ≤ p j) ∧ (∑ j, p j = 1) ∧ (∀ j, U j ∈ unitaryGroup n 𝕜) ∧
          H = ∑ j, p j • (U j * K * (U j)ᴴ) := by
  refine ⟨fun hHK => ?_, ?_⟩
  · obtain ⟨p, U, hp, hp1, hU, hHK'⟩ := hH.exists_eq_sum_smul_unitary_conj_of_majorize hK hHK
    refine ⟨Fintype.card (Equiv.Perm n), p ∘ (Fintype.equivFin (Equiv.Perm n)).symm,
      U ∘ (Fintype.equivFin (Equiv.Perm n)).symm, fun j => hp _, ?_, fun j => hU _, ?_⟩
    · exact (Equiv.sum_comp (Fintype.equivFin (Equiv.Perm n)).symm p).trans hp1
    · rw [hHK']
      exact (Equiv.sum_comp (Fintype.equivFin (Equiv.Perm n)).symm
        (fun σ => p σ • (U σ * K * (U σ)ᴴ))).symm
  · rintro ⟨m, p, U, hp, hp1, hU, hHK⟩
    exact hH.majorize_of_eq_sum_smul_unitary_conj hK hp hp1 hU hHK

end IsHermitian

end Matrix
