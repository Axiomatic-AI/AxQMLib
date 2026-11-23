/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSum
public import ToMathlib.Analysis.InnerProductSpace.RankOneSum

/-! # The entanglement fidelity of a quantum operation and its concentration in one element

For a finite family of operation elements `E : ι → (H →L[ℂ] H)` — the Kraus operators of a
trace-preserving quantum operation `E(ρ) = Σᵢ Eᵢ ρ Eᵢ†` — the **entanglement fidelity** of a state
`ρ` is the real number
`F(ρ, E) = Σᵢ |tr(ρ Eᵢ)|²`
(Nielsen–Chuang, *Quantum Computation and Quantum Information*, Eq. (9.135)). This is the
computational formula for the intrinsic entanglement fidelity `F(ρ, E) = ⟨RQ|(I ⊗ E)(|RQ⟩⟨RQ|)|RQ⟩`
(Eqs. (9.128)–(9.135)) obtained from any operator-sum representation of the operation.

This file records the quantity and the two facts about it that require the unitary-freedom theorem
(`ContinuousLinearMap.krausSumₗ_eq_iff_exists_mem_unitaryGroup`, N&C Theorem 8.2):

* `ContinuousLinearMap.entanglementFidelity` — the sum `Σᵢ |tr(ρ Eᵢ)|²`.
* `ContinuousLinearMap.entanglementFidelity_eq_of_krausSumₗ_eq` — **well-definedness**: the sum
  depends on the operation elements only through the operator-sum map `krausSumₗ E` they generate,
  so `F(ρ, E)` is genuinely a function of the operation `E` (not of the chosen elements). This is
  what licenses the notation `F(ρ, E)` on the intrinsic quantity in Eq. (9.135).
* `ContinuousLinearMap.exists_krausSumₗ_eq_entanglementFidelity_eq_normSq_trace` — **Nielsen &
  Chuang, Problem 9.2**: for each `ρ` there is a set of operation elements `F` *for the same
  operation* (`krausSumₗ F = krausSumₗ E`) in which the whole fidelity is carried by the first
  element — every other `tr(ρ Fᵢ)` vanishes and
  `F(ρ, E) = |tr(ρ F₀)|²`  (Eq. (9.146)).

## Method

Writing `vᵢ = tr(ρ Eᵢ)`, the fidelity is `‖v‖²` for the Euclidean vector `v ∈ ℂ^ι`. A change of
operation elements `Eᵢ = Σⱼ uᵢⱼ Fⱼ` by a unitary `u` (Theorem 8.2) transforms the trace vector by
the same unitary, and a unitary preserves the `ℓ²` norm — giving well-definedness
(`Matrix.sum_normSq_mulVec_eq_of_mem_unitaryGroup`). For Problem 9.2, choosing `u` to be a unitary
matrix whose zeroth row is the unit vector `conj v / ‖v‖` (built from a single unit vector by
`EuclideanSpace.exists_mem_unitaryGroup_row_zero_eq`) rotates all of `v`'s length into the zeroth
coordinate: `tr(ρ F₀) = ‖v‖` and `tr(ρ Fᵢ) = 0` for `i ≠ 0`, so `‖v‖² = |tr(ρ F₀)|²`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §9.3 (Eqs. (9.135), (9.146); Problem 9.2).
-/

open scoped InnerProductSpace ComplexConjugate

@[expose] public section

/-- **A unitary matrix acting on a vector preserves the `ℓ²` sum of squared norms:**
`Σᵢ |Σⱼ uᵢⱼ wⱼ|² = Σⱼ |wⱼ|²` for `u ∈ Matrix.unitaryGroup ι ℂ`. The row `i ↦ Σⱼ uᵢⱼ wⱼ` is
`u.mulVec w i`; the identity is the coordinate form of the fact that a unitary matrix is an
isometry of `EuclideanSpace ℂ ι`. The proof casts to `ℂ`, expands each squared norm as `conj · ·`,
and collapses the double sum through the unitarity relation `Σᵢ conj(uᵢⱼ) uᵢₖ = (u⋆u)ⱼₖ = δⱼₖ`. -/
theorem Matrix.sum_normSq_mulVec_eq_of_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : Matrix ι ι ℂ} (hu : u ∈ Matrix.unitaryGroup ι ℂ) (w : ι → ℂ) :
    ∑ i, ‖∑ j, u i j * w j‖ ^ 2 = ∑ j, ‖w j‖ ^ 2 := by
  have key : ∀ j k : ι, (∑ i, conj (u i j) * u i k) = if j = k then (1 : ℂ) else 0 := by
    intro j k
    have h1 : (star u * u : Matrix ι ι ℂ) = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
    have h2 := congrFun (congrFun h1 j) k
    rw [Matrix.mul_apply, Matrix.one_apply] at h2
    rw [← h2]
    simp only [Matrix.star_apply, starRingEnd_apply]
  apply Complex.ofReal_injective
  push_cast
  have hL : ∀ i, ((‖∑ j, u i j * w j‖ : ℝ) : ℂ) ^ 2
      = ∑ j, ∑ k, conj (u i j) * u i k * (conj (w j) * w k) := by
    intro i
    have e1 : conj (∑ j, u i j * w j) * (∑ j, u i j * w j)
        = ((‖∑ j, u i j * w j‖ : ℝ) : ℂ) ^ 2 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    rw [← e1, map_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
      rw [map_mul]; ring
  rw [Finset.sum_congr rfl (fun i _ => hL i), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, key]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

namespace ContinuousLinearMap

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

/-- The **entanglement fidelity** `F(ρ, E) = Σᵢ |tr(ρ Eᵢ)|²` of a state `ρ` under the
trace-preserving quantum operation with operation elements `E : ι → (H →L[ℂ] H)`, i.e.
`E(ρ) = Σᵢ Eᵢ ρ Eᵢ†` (Nielsen & Chuang, Eq. (9.135)). It is a function of `ρ` and the operation
only — see `entanglementFidelity_eq_of_krausSumₗ_eq`. -/
noncomputable def entanglementFidelity (ρ : H →L[ℂ] H) (E : ι → H →L[ℂ] H) : ℝ :=
  ∑ i, ‖LinearMap.trace ℂ H ((ρ * E i : H →L[ℂ] H) : H →ₗ[ℂ] H)‖ ^ 2

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- The entanglement fidelity `F(ρ, E) = Σᵢ |tr(ρ Eᵢ)|²` is nonnegative, being a sum of squared
norms. -/
theorem entanglementFidelity_nonneg (ρ : H →L[ℂ] H) (E : ι → H →L[ℂ] H) :
    0 ≤ entanglementFidelity ρ E :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- Linearity of the trace in the operation-element argument:
`tr(ρ · Σⱼ uⱼ Eⱼ) = Σⱼ uⱼ tr(ρ Eⱼ)`. -/
theorem trace_mul_sum_smul (ρ : H →L[ℂ] H) (u : ι → ℂ) (E : ι → H →L[ℂ] H) :
    LinearMap.trace ℂ H ((ρ * (∑ j, u j • E j) : H →L[ℂ] H) : H →ₗ[ℂ] H)
      = ∑ j, u j * LinearMap.trace ℂ H ((ρ * E j : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  rw [Finset.mul_sum, ContinuousLinearMap.toLinearMap_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]

/-- **The entanglement fidelity depends only on the operation, not on the choice of operation
elements** (well-definedness of Nielsen & Chuang Eq. (9.135)). If two families `E`, `F` generate
the same operator-sum map, `krausSumₗ E = krausSumₗ F`, then `F(ρ, E) = F(ρ, F)`. By unitary
freedom (Theorem 8.2) the elements are related by a unitary coefficient matrix, which acts on the
trace vector `i ↦ tr(ρ Eᵢ)`; a unitary preserves its `ℓ²` norm
(`Matrix.sum_normSq_mulVec_eq_of_mem_unitaryGroup`). -/
theorem entanglementFidelity_eq_of_krausSumₗ_eq (ρ : H →L[ℂ] H) {E F : ι → H →L[ℂ] H}
    (h : krausSumₗ E = krausSumₗ F) : entanglementFidelity ρ E = entanglementFidelity ρ F := by
  classical
  obtain ⟨u, hu, hEF⟩ := krausSumₗ_eq_iff_exists_mem_unitaryGroup.mp h
  have htr : ∀ i, LinearMap.trace ℂ H ((ρ * E i : H →L[ℂ] H) : H →ₗ[ℂ] H)
      = ∑ j, u i j * LinearMap.trace ℂ H ((ρ * F j : H →L[ℂ] H) : H →ₗ[ℂ] H) := fun i => by
    rw [hEF i]; exact trace_mul_sum_smul ρ (u i) F
  simp only [entanglementFidelity]
  simp only [htr]
  exact Matrix.sum_normSq_mulVec_eq_of_mem_unitaryGroup hu _

omit [FiniteDimensional ℂ H] in
/-- **Nielsen & Chuang, Problem 9.2.** For every state `ρ` and every trace-preserving quantum
operation — presented by operation elements `E : Fin n → (H →L[ℂ] H)` — there is a set of operation
elements `F` *for the same operation* (`krausSumₗ F = krausSumₗ E`) in which all the entanglement
fidelity is carried by the first element: `tr(ρ Fᵢ) = 0` for every `i ≠ 0`, and
`F(ρ, E) = |tr(ρ F₀)|²`  (Eq. (9.146)).

Let `vᵢ = tr(ρ Eᵢ)`, so `F(ρ, E) = ‖v‖²`. If `v = 0` the original elements already work. Otherwise
`EuclideanSpace.exists_mem_unitaryGroup_row_zero_eq` gives a unitary matrix `u` whose zeroth row is
the unit vector `conj v / ‖v‖`; setting `Fᵢ = Σⱼ uᵢⱼ Eⱼ` keeps the operation fixed (unitary freedom,
Theorem 8.2) while `tr(ρ Fᵢ) = Σⱼ uᵢⱼ vⱼ` rotates `v` into its zeroth coordinate — `tr(ρ F₀) = ‖v‖`
and, by orthonormality of the rows of `u`, `tr(ρ Fᵢ) = 0` for `i ≠ 0`. -/
theorem exists_krausSumₗ_eq_entanglementFidelity_eq_normSq_trace
    {n : ℕ} [NeZero n] (ρ : H →L[ℂ] H) (E : Fin n → H →L[ℂ] H) :
    ∃ F : Fin n → H →L[ℂ] H, krausSumₗ F = krausSumₗ E ∧
      (∀ i, i ≠ 0 → LinearMap.trace ℂ H ((ρ * F i : H →L[ℂ] H) : H →ₗ[ℂ] H) = 0) ∧
      entanglementFidelity ρ E
        = ‖LinearMap.trace ℂ H ((ρ * F 0 : H →L[ℂ] H) : H →ₗ[ℂ] H)‖ ^ 2 := by
  set trc : Fin n → ℂ := fun i => LinearMap.trace ℂ H ((ρ * E i : H →L[ℂ] H) : H →ₗ[ℂ] H)
    with htrc
  have hentE : entanglementFidelity ρ E = ∑ i, ‖trc i‖ ^ 2 := rfl
  by_cases hS : entanglementFidelity ρ E = 0
  · -- `v = 0`: the original operation elements already carry no fidelity.
    have hz : ∀ i, trc i = 0 := by
      rw [hentE] at hS
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hS
      intro i
      have h2 : ‖trc i‖ ^ 2 = 0 := h i (Finset.mem_univ i)
      simpa using h2
    refine ⟨E, rfl, fun i _ => hz i, ?_⟩
    rw [hS, show LinearMap.trace ℂ H ((ρ * E 0 : H →L[ℂ] H) : H →ₗ[ℂ] H) = trc 0 from rfl, hz 0]
    simp
  · -- `v ≠ 0`: rotate all of `v`'s length into the zeroth coordinate.
    have hSnonneg : 0 ≤ entanglementFidelity ρ E := by
      rw [hentE]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hSpos : 0 < entanglementFidelity ρ E := lt_of_le_of_ne hSnonneg (Ne.symm hS)
    set N : ℝ := Real.sqrt (entanglementFidelity ρ E) with hNdef
    have hNpos : 0 < N := Real.sqrt_pos.mpr hSpos
    have hNsq : N ^ 2 = entanglementFidelity ρ E := Real.sq_sqrt hSnonneg
    have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
    -- the unit vector `conj v / ‖v‖`
    set w' : EuclideanSpace ℂ (Fin n) :=
      (WithLp.equiv 2 (Fin n → ℂ)).symm (fun j => conj (trc j) / (N : ℂ)) with hw'
    have hw'coord : ∀ j, w'.ofLp j = conj (trc j) / (N : ℂ) := fun j => rfl
    have hw'norm : ‖w'‖ = 1 := by
      have hsq : ‖w'‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq]
        have hterm : ∀ j, ‖w'.ofLp j‖ ^ 2 = ‖trc j‖ ^ 2 / N ^ 2 := fun j => by
          rw [hw'coord j, norm_div, Complex.norm_conj, Complex.norm_real,
            Real.norm_of_nonneg hNpos.le, div_pow]
        rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_div, ← hentE, hNsq,
          div_self hS]
      rw [← Real.sqrt_sq (norm_nonneg w'), hsq, Real.sqrt_one]
    obtain ⟨u, hu, hurow⟩ := EuclideanSpace.exists_mem_unitaryGroup_row_zero_eq w' hw'norm
    have hu0 : ∀ j, u 0 j = conj (trc j) / (N : ℂ) := fun j => by rw [hurow j, hw'coord j]
    have hstar : ∀ j, (star u) j 0 = trc j / (N : ℂ) := fun j => by
      rw [Matrix.star_apply, hu0 j, star_div₀, starRingEnd_apply, star_star, Complex.star_def,
        Complex.conj_ofReal]
    set F : Fin n → H →L[ℂ] H := fun i => ∑ j, u i j • E j with hF
    have hFtr : ∀ i, LinearMap.trace ℂ H ((ρ * F i : H →L[ℂ] H) : H →ₗ[ℂ] H)
        = ∑ j, u i j * trc j := fun i => trace_mul_sum_smul ρ (u i) E
    refine ⟨F, krausSumₗ_eq_of_mem_unitaryGroup hu (fun i => rfl), ?_, ?_⟩
    · -- off-diagonal traces vanish: `(u · uᴴ)ᵢ₀ = 0` for `i ≠ 0`
      intro i hi
      rw [hFtr i]
      have hmul : ∑ j, u i j * (star u) j 0 = 0 := by
        have h2 := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hu) i) 0
        rwa [Matrix.mul_apply, Matrix.one_apply, ite_eq_right hi] at h2
      simp only [hstar, ← mul_div_assoc] at hmul
      rw [← Finset.sum_div] at hmul
      exact (div_eq_zero_iff.mp hmul).resolve_right hNC
    · -- the zeroth element carries the whole fidelity: `tr(ρ F₀) = ‖v‖`
      rw [hFtr 0]
      have hval : ∑ j, u 0 j * trc j = (N : ℂ) := by
        have hterm : ∀ j, u 0 j * trc j = conj (trc j) * trc j / (N : ℂ) := fun j => by
          rw [hu0 j]; ring
        rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_div]
        have hsum : ∑ j, conj (trc j) * trc j = ((entanglementFidelity ρ E : ℝ) : ℂ) := by
          rw [hentE, Complex.ofReal_sum]
          exact Finset.sum_congr rfl fun j _ => by
            rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [hsum, ← hNsq]
        push_cast
        rw [sq, mul_div_assoc, div_self hNC, mul_one]
      rw [hval, Complex.norm_real, Real.norm_of_nonneg hNpos.le, hNsq]

end ContinuousLinearMap
