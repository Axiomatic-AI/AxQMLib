/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CosetState
import ToMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Concrete: normalized coset states, their orthonormality, and the mixture form of `σ_K`

Building on `AxQM.Concrete.CosetState` (the coset density matrix
`σ_K = |G|⁻¹ · [iK = jK]`), this file records the **spectral picture** of `σ_K` in terms of the
normalized uniform superpositions over the individual cosets.

For a finite group `G`, a subgroup `K ≤ G`, and a left coset `q ∈ G ⧸ K`, the **normalized coset
state** is the unit vector

`|C_q⟩ = |K|^{-1/2} ∑_{g ∈ q} |g⟩ ∈ ℂ[G]`,   coordinates   `|C_q⟩ i = |K|^{-1/2} · [iK = q]`,

modelled here as an element of `EuclideanSpace ℂ G`. The file proves:

* `cosetState` — the normalized coset state `|C_q⟩`, with `cosetState_ofLp_apply` its coordinates.
* `cosetIncidence_col_inner` — the coset columns of the incidence matrix are orthogonal with squared
  norm `|K|`: `∑_{i} [iK = q][iK = q'] = |K| · [q = q']`. Each coset is a fiber of the quotient map
  `G → G ⧸ K`, which has exactly `|K|` elements (`card_coset_fiber`).
* `cosetState_orthonormal` — the family `(|C_q⟩)_{q ∈ G ⧸ K}` is orthonormal (Mathlib's
  `Orthonormal` predicate): distinct cosets are disjoint, and `|K|^{-1/2}` normalizes each state.
* `cosetDensity_eq_sum_cosetState` — the **mixture / spectral form**
  `σ_K = ∑_{q} (|K|/|G|) |C_q⟩⟨C_q|`. As `(|C_q⟩)_q` is orthonormal, this is exactly the
  eigendecomposition of `σ_K`: eigenvalue `|K|/|G|` on each `|C_q⟩`. It collapses to the entrywise
  form `σ_K i j = |G|⁻¹ · [iK = jK]` via the Gram identity `(P Pᴴ) i j = [iK = jK]`
  (`cosetIncidence_mul_conjTranspose_apply`).

This is an input to the Nielsen & Chuang Problem 5.5 development (the non-Abelian hidden subgroup
problem). The reduced state derived from the query state (5.80) builds on it.

## Design notes

* Coset states live in `EuclideanSpace ℂ G` and are built with `WithLp.toLp`, so
  `EuclideanSpace.inner_toLp_toLp` reduces `⟪|C_q⟩, |C_q'⟩⟫` directly to the coordinate dot product;
  orthonormality is then `orthonormal_iff_ite` plus the columns' inner product
  `cosetIncidence_col_inner`.
* The key combinatorial fact is that a coset `q` — the fiber of `G → G ⧸ K` over `q` — has exactly
  `|K|` elements (`card_coset_fiber`). This reuses Mathlib's coset bijection
  `Subgroup.leftCosetEquivSubgroup g : ↑(g • ↑K) ≃ ↥K` (in `Mathlib.GroupTheory.Coset.Basic`,
  already in the import surface transitively via `CosetState.lean`): identify the fiber
  `{x | ↑x = q}` with the coset `g • K` by `Equiv.subtypeEquivRight` (the predicate equivalence
  `↑x = ↑g ↔ x ∈ g • ↑K` is `QuotientGroup.eq`/`mem_leftCoset_iff`), then apply the bijection. The
  heavier Sylow-theory `QuotientGroup.card_preimage_mk` (which would need
  `Mathlib.GroupTheory.Sylow`) is genuinely outside the import surface and rightly avoided.
* The normalization `|K|^{-1/2}` is written `((Real.sqrt (Fintype.card K))⁻¹ : ℝ)` coerced to `ℂ`;
  `Real.mul_self_sqrt` gives `(|K|^{-1/2})² = |K|⁻¹`, and `|K| ≠ 0` (a subgroup contains `1`) closes
  the `|K|⁻¹ · |K| = 1` normalization and the `(|K|/|G|) · |K|⁻¹ = |G|⁻¹` mixture-weight arithmetic.
-/

namespace AxQM.Concrete

open Matrix
open scoped ComplexOrder

variable {G : Type*} [Group G] [Fintype G] (K : Subgroup G) [DecidablePred (· ∈ K)]

/-- **Coset fiber cardinality.** The set of group elements lying in a fixed left coset `q ∈ G ⧸ K`
— the fiber of the quotient map `G → G ⧸ K` over `q` — has exactly `|K|` elements. For a
representative `g` of `q` the fiber is the left coset `g • K`, so this is Mathlib's coset bijection
`Subgroup.leftCosetEquivSubgroup g` after identifying the fiber `{x | ↑x = q}` with `g • K`
(`Equiv.subtypeEquivRight`). -/
theorem card_coset_fiber (q : G ⧸ K) :
    Fintype.card {x : G // (↑x : G ⧸ K) = q} = Fintype.card K := by
  induction q using QuotientGroup.induction_on with
  | _ g =>
    apply Fintype.card_congr
    refine (Equiv.subtypeEquivRight fun x => ?_).trans (Subgroup.leftCosetEquivSubgroup g)
    rw [QuotientGroup.eq, mem_leftCoset_iff, ← K.inv_mem_iff, _root_.mul_inv_rev, inv_inv,
      SetLike.mem_coe]

omit [Fintype G] in
/-- The coset incidence matrix has real `{0,1}` entries, so each entry is fixed by conjugation. -/
theorem cosetIncidence_star (i : G) (q : G ⧸ K) :
    star (cosetIncidence K i q) = cosetIncidence K i q := by
  simp only [cosetIncidence]; split_ifs <;> simp

/-- **Coset columns are orthogonal with squared norm `|K|`.** Summing the pointwise product of the
`q`- and `q'`-columns of the coset incidence matrix over all group elements gives `|K|` when
`q = q'` (the coset `q` has `|K|` elements, `card_coset_fiber`) and `0` otherwise (an element lies
in at most one coset). This is the un-normalized orthonormality of the coset states. -/
theorem cosetIncidence_col_inner (q q' : G ⧸ K) :
    ∑ i : G, cosetIncidence K i q * cosetIncidence K i q' =
      if q = q' then (Fintype.card K : ℂ) else 0 := by
  simp only [cosetIncidence]
  by_cases hqq : q = q'
  · subst hqq
    rw [ite_eq_left rfl]
    have hmul : ∀ i : G, (if (↑i : G ⧸ K) = q then (1 : ℂ) else 0) *
        (if (↑i : G ⧸ K) = q then (1 : ℂ) else 0) = if (↑i : G ⧸ K) = q then 1 else 0 := by
      intro i; split_ifs <;> simp
    simp only [hmul, Finset.sum_boole]
    rw [← Fintype.card_subtype]
    exact_mod_cast card_coset_fiber K q
  · rw [ite_eq_right hqq]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : (↑i : G ⧸ K) = q
    · simp [hi, hqq]
    · simp [hi]

/-- The **normalized coset state** `|C_q⟩ = |K|^{-1/2} ∑_{g ∈ q} |g⟩ ∈ ℂ[G]`, modelled as an element
of `EuclideanSpace ℂ G`, with coordinates `|C_q⟩ i = |K|^{-1/2} · [iK = q]`
(`cosetState_ofLp_apply`). It is the normalized uniform superposition over the coset `q`; the
family `(|C_q⟩)_q` is
orthonormal (`cosetState_orthonormal`) and `σ_K` is their uniform mixture
(`cosetDensity_eq_sum_cosetState`). -/
noncomputable def cosetState (q : G ⧸ K) : EuclideanSpace ℂ G :=
  WithLp.toLp 2 (fun i => (((Real.sqrt (Fintype.card K))⁻¹ : ℝ) : ℂ) * cosetIncidence K i q)

/-- **Coordinates of the normalized coset state**: `|C_q⟩ i = |K|^{-1/2} · [iK = q]`. -/
theorem cosetState_ofLp_apply (q : G ⧸ K) (i : G) :
    (cosetState K q).ofLp i =
      (((Real.sqrt (Fintype.card K))⁻¹ : ℝ) : ℂ) * cosetIncidence K i q :=
  rfl

/-- **The normalized coset states form an orthonormal family.** For `q, q' ∈ G ⧸ K`,
`⟪|C_q⟩, |C_q'⟩⟫ = |K|⁻¹ · |K| · [q = q'] = [q = q']`: distinct cosets are disjoint, and the
`|K|^{-1/2}` factor normalizes each state (`cosetIncidence_col_inner`). -/
theorem cosetState_orthonormal : Orthonormal ℂ (cosetState K) := by
  have hK : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [orthonormal_iff_ite]
  intro q q'
  rw [cosetState, cosetState, EuclideanSpace.inner_toLp_toLp, dotProduct]
  simp only [Pi.star_apply]
  have key : ∑ i : G, (((Real.sqrt (Fintype.card K))⁻¹ : ℝ) : ℂ) * cosetIncidence K i q' *
      star ((((Real.sqrt (Fintype.card K))⁻¹ : ℝ) : ℂ) * cosetIncidence K i q) =
      (((Real.sqrt (Fintype.card K))⁻¹ : ℝ) : ℂ) ^ 2 *
        ∑ i : G, cosetIncidence K i q * cosetIncidence K i q' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_mul', cosetIncidence_star, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [key, cosetIncidence_col_inner]
  by_cases hqq : q = q'
  · rw [ite_eq_left hqq, ite_eq_left hqq, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_eq_one, inv_pow, Real.sq_sqrt (by positivity),
      inv_mul_cancel₀ hK]
  · rw [ite_eq_right hqq, ite_eq_right hqq, mul_zero]

/-- **The coset state is the normalized indicator sum over its coset**:
`∑_{g ∈ q} |g⟩ = √|K| · |C_q⟩`. Both sides are supported on the coset `q` with all coordinates
equal (`1` on the left, `√|K| · |K|^{-1/2} = 1` on the right); it re-expresses the normalized coset
state `|C_q⟩ = |K|^{-1/2} ∑_{g ∈ q} |g⟩` as a plain sum of computational basis vectors. -/
theorem sum_single_coset_eq_smul_cosetState [DecidableEq G] (q : G ⧸ K) :
    (∑ g ∈ Finset.univ.filter (fun g : G => (↑g : G ⧸ K) = q), EuclideanSpace.single g (1 : ℂ) :
        EuclideanSpace ℂ G)
      = ((Real.sqrt (Fintype.card K) : ℝ) : ℂ) • cosetState K q := by
  have hsqrt : Real.sqrt (Fintype.card K) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast Fintype.card_pos)
  ext i
  rw [show (∑ g ∈ Finset.univ.filter (fun g : G => (↑g : G ⧸ K) = q),
        EuclideanSpace.single g (1 : ℂ)).ofLp
      = ∑ g ∈ Finset.univ.filter (fun g : G => (↑g : G ⧸ K) = q),
        (EuclideanSpace.single g (1 : ℂ)).ofLp from
      map_sum (WithLp.linearEquiv 2 ℂ (G → ℂ)) _ _, Finset.sum_apply]
  simp only [PiLp.smul_apply, cosetState_ofLp_apply, smul_eq_mul,
    PiLp.single_apply, cosetIncidence]
  rw [Finset.sum_ite_eq (Finset.univ.filter (fun g : G => (↑g : G ⧸ K) = q)) i (fun _ => (1 : ℂ))]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with hi
  · rw [mul_one, ← Complex.ofReal_mul, mul_inv_cancel₀ hsqrt, Complex.ofReal_one]
  · simp

/-- **The coset density matrix is the uniform mixture of the coset-state projectors** (its spectral
decomposition): `σ_K = ∑_{q ∈ G ⧸ K} (|K|/|G|) |C_q⟩⟨C_q|`. Since `(|C_q⟩)_q` is orthonormal
(`cosetState_orthonormal`), this exhibits `σ_K` as diagonal with eigenvalue `|K|/|G|` on each
coset state. Entrywise the weighted outer products collapse to `σ_K i j = |G|⁻¹ · [iK = jK]` via the
Gram identity `(P Pᴴ) i j = [iK = jK]` (`cosetIncidence_mul_conjTranspose_apply`). -/
theorem cosetDensity_eq_sum_cosetState :
    cosetDensity K =
      ∑ q : G ⧸ K, ((Fintype.card K / Fintype.card G : ℝ) : ℂ) •
        Matrix.vecMulVec (cosetState K q).ofLp (star (cosetState K q).ofLp) := by
  have hKr : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext i j
  rw [cosetDensity_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    cosetState_ofLp_apply, smul_eq_mul]
  have hterm : ∀ q : G ⧸ K,
      ((Fintype.card K / Fintype.card G : ℝ) : ℂ) *
        ((((Real.sqrt (Fintype.card K))⁻¹ : ℝ) : ℂ) * cosetIncidence K i q *
          star ((((Real.sqrt (Fintype.card K))⁻¹ : ℝ) : ℂ) * cosetIncidence K j q)) =
      ((Fintype.card G : ℝ)⁻¹ : ℂ) * (cosetIncidence K i q * cosetIncidence K j q) := by
    intro q
    have hreal : (Fintype.card K / Fintype.card G : ℝ) * (Real.sqrt (Fintype.card K))⁻¹ *
        (Real.sqrt (Fintype.card K))⁻¹ = (Fintype.card G : ℝ)⁻¹ := by
      rw [mul_assoc, ← mul_inv, Real.mul_self_sqrt (by positivity), div_eq_mul_inv, mul_right_comm,
        mul_inv_cancel₀ hKr, one_mul]
    have hw : ((Fintype.card K / Fintype.card G : ℝ) : ℂ) *
        (((Real.sqrt (Fintype.card K))⁻¹ : ℝ) : ℂ) *
        (((Real.sqrt (Fintype.card K))⁻¹ : ℝ) : ℂ) = ((Fintype.card G : ℝ)⁻¹ : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hreal, Complex.ofReal_inv]
    rw [star_mul', cosetIncidence_star, Complex.star_def, Complex.conj_ofReal, ← hw]; ring
  have hPP : ∑ q : G ⧸ K, cosetIncidence K i q * cosetIncidence K j q =
      if (↑i : G ⧸ K) = ↑j then 1 else 0 := by
    have h := cosetIncidence_mul_conjTranspose_apply K i j
    rw [Matrix.mul_apply] at h
    simp only [Matrix.conjTranspose_apply, cosetIncidence_star] at h
    exact h
  rw [Finset.sum_congr rfl fun q _ => hterm q, ← Finset.mul_sum, hPP]
  split_ifs <;> simp

end AxQM.Concrete
