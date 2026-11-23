/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.GroupTheory.Coset.Card

/-!
# Concrete: the coset density matrix `σ_K = |G|⁻¹ · [iK = jK]`

For a finite group `G` and a subgroup `K ≤ G`, this file defines the `|G| × |G|` complex matrix

`cosetDensity K i j = |G|⁻¹ · (if iK = jK then 1 else 0)`,

the **coset density matrix** `σ_K` of the hidden subgroup `K`. This is the single-copy reduced
state at the heart of Nielsen & Chuang, Problem 5.5 (the non-Abelian hidden subgroup problem):
starting from the query state `|G|^{-m/2} ∑_{g₁,…,gₘ} |g₁,…,gₘ⟩|f(g₁),…,f(gₘ)⟩` (eq. 5.80), where
`f` is constant and distinct on left cosets of `K`, tracing out the range register leaves the group
registers in the state `σ_K^{⊗m}`, because `f` reveals exactly which of the `gᵢ` share a coset.
Each per-copy factor is `σ_K`: writing `|C⟩ = |K|^{-1/2} ∑_{g ∈ C} |g⟩` for the normalized uniform
superposition over a coset `C`, one has `σ_K = (|K|/|G|) ∑_C |C⟩⟨C|`, whose matrix entries collapse
to `|G|⁻¹` on the coset-equivalence relation `iK = jK`.

It records the matrix-level facts that make `σ_K` a genuine density matrix:

* `cosetIncidence` — the `G × (G ⧸ K)` incidence matrix `P` with `P i q = [iK = q]`.
* `cosetIncidence_mul_conjTranspose_apply` — its Gram matrix is the coset-equivalence matrix:
  `(P Pᴴ) i j = [iK = jK]`.
* `cosetDensity` — the coset density matrix `σ_K = |G|⁻¹ (P Pᴴ)`.
* `cosetDensity_apply` — the explicit entry form `σ_K i j = |G|⁻¹ · [iK = jK]`.
* `cosetDensity_isHermitian` — `σ_K` is Hermitian.
* `cosetDensity_posSemidef` — `σ_K` is positive semidefinite (it is a nonnegative scalar times the
  Gram matrix `P Pᴴ`).
* `cosetDensity_trace_eq_one` — `tr σ_K = 1` (the `|G|` diagonal entries `|G|⁻¹` sum to one).

Together the last three exhibit `σ_K` as a density matrix (Hermitian, trace one, positive
semidefinite).

## Design notes

* Positivity is obtained for free from the Gram factorisation `σ_K = |G|⁻¹ (P Pᴴ)`: `P Pᴴ` is
  positive semidefinite (`Matrix.posSemidef_self_mul_conjTranspose`) and scaling by the nonnegative
  real `|G|⁻¹` preserves this (`Matrix.PosSemidef.smul`). This avoids any explicit quadratic-form /
  coset-grouping computation and any normalisation of coset states.
* The `|G|⁻¹` prefactor is written as a coerced real `((Fintype.card G : ℝ)⁻¹ : ℂ)` so the
  nonnegativity side goals reduce through `Complex.zero_le_real`, the same idiom as
  `AxQM.Concrete.blochMatrix`.
* The finite index set `G ⧸ K` gets its `Fintype`/`DecidableEq` instances from `[Fintype G]` and
  `[DecidablePred (· ∈ K)]`.
-/

namespace AxQM.Concrete

open Matrix
open scoped ComplexOrder

variable {G : Type*} [Group G] [Fintype G] (K : Subgroup G) [DecidablePred (· ∈ K)]

/-- The **coset incidence matrix** `P` of a subgroup `K ≤ G`: rows indexed by the group elements
`G`, columns by the left cosets `G ⧸ K`, with `P i q = 1` when `i` lies in coset `q` (i.e.
`iK = q`) and `0` otherwise. Its Gram matrix `P Pᴴ` is the coset-equivalence matrix `[iK = jK]`,
whose `|G|⁻¹`-scaling is the coset density matrix `cosetDensity`. -/
noncomputable def cosetIncidence : Matrix G (G ⧸ K) ℂ :=
  fun i q => if (↑i : G ⧸ K) = q then 1 else 0

/-- The Gram matrix of the coset incidence matrix is the **coset-equivalence matrix**:
`(P Pᴴ) i j = 1` when `i` and `j` lie in the same left coset (`iK = jK`) and `0` otherwise. Each
column `q` of `P` is the `0/1` indicator of coset `q`, so `(P Pᴴ) i j = ∑_q [iK = q][jK = q]`
counts the (single, if any) common coset of `i` and `j`. -/
theorem cosetIncidence_mul_conjTranspose_apply (i j : G) :
    (cosetIncidence K * (cosetIncidence K)ᴴ) i j =
      if (↑i : G ⧸ K) = (↑j : G ⧸ K) then 1 else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cosetIncidence,
    apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact if_congr eq_comm rfl rfl

/-- The **coset density matrix** `σ_K = |G|⁻¹ (P Pᴴ)` of a subgroup `K ≤ G`, where `P` is the coset
incidence matrix (`cosetIncidence`). Equivalently `σ_K = (|K|/|G|) ∑_C |C⟩⟨C|`, the uniform mixture
of the projectors onto the normalized coset states, with entries `σ_K i j = |G|⁻¹ · [iK = jK]`
(`cosetDensity_apply`). This is the single-copy reduced state of the Nielsen & Chuang Problem 5.5
query register (5.80) after the range register is traced out. -/
noncomputable def cosetDensity : Matrix G G ℂ :=
  ((Fintype.card G : ℝ)⁻¹ : ℂ) • (cosetIncidence K * (cosetIncidence K)ᴴ)

/-- **Explicit entry form** of the coset density matrix: `σ_K i j = |G|⁻¹` when `i` and `j` lie in
the same left coset (`iK = jK`) and `0` otherwise. -/
theorem cosetDensity_apply (i j : G) :
    cosetDensity K i j =
      if (↑i : G ⧸ K) = (↑j : G ⧸ K) then ((Fintype.card G : ℝ)⁻¹ : ℂ) else 0 := by
  rw [cosetDensity, Matrix.smul_apply, cosetIncidence_mul_conjTranspose_apply, smul_eq_mul]
  split_ifs <;> simp

/-- The diagonal entries of the coset density matrix are all `|G|⁻¹` (since `iK = iK`). -/
theorem cosetDensity_diag (i : G) :
    cosetDensity K i i = ((Fintype.card G : ℝ)⁻¹ : ℂ) := by
  rw [cosetDensity_apply, ite_eq_left rfl]

/-- **`σ_K` is positive semidefinite.** It is the nonnegative real scalar `|G|⁻¹` times the Gram
matrix `P Pᴴ`, which is positive semidefinite (`Matrix.posSemidef_self_mul_conjTranspose`). This is
the positivity half of "`σ_K` is a density matrix" (Nielsen & Chuang, Problem 5.5). -/
theorem cosetDensity_posSemidef : (cosetDensity K).PosSemidef :=
  (Matrix.posSemidef_self_mul_conjTranspose _).smul (by
    rw [← Complex.ofReal_inv, Complex.zero_le_real]; positivity)

/-- **`σ_K` is Hermitian**, immediate from positive semidefiniteness. This is the self-adjointness
half of "`σ_K` is a density matrix" (Nielsen & Chuang, Problem 5.5). -/
theorem cosetDensity_isHermitian : (cosetDensity K).IsHermitian :=
  (cosetDensity_posSemidef K).isHermitian

/-- **`tr σ_K = 1`**: the coset density matrix has trace one. Its `|G|` diagonal entries are each
`|G|⁻¹` (`cosetDensity_diag`), summing to one. This is the trace-one half of "`σ_K` is a density
matrix" (Nielsen & Chuang, Problem 5.5). -/
theorem cosetDensity_trace_eq_one : (cosetDensity K).trace = 1 := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [Matrix.trace, Matrix.diag_apply, cosetDensity_diag, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Complex.ofReal_natCast]
  exact mul_inv_cancel₀ hcard

end AxQM.Concrete
