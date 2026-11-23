/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import ToMathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import ToMathlib.Data.Real.Sqrt

/-!
# Concrete: search oracle, algorithm states, and the deviation bound `Dₖ ≤ 4k²`

This file formalises the **first half** of Nielsen & Chuang's optimality proof for quantum search
(§6.6, the argument leading to Exercise 6.16). It is linear algebra on a generic
complex inner-product space `H`, with an orthonormal family `e : Fin N → H` (the marked basis `|x⟩`)
and unitary steps modelled as linear isometric equivalences `U : ℕ → (H ≃ₗᵢ[ℂ] H)`. The final
query-complexity statement for `QSystem`/`PureState`/`Evolution` is in
`AxQM/NC/Ch6/Exercise6_16.lean`.

## The N&C setup

For a single-solution search the oracle is the reflection `Oₓ = I − 2|x⟩⟨x|` (eq. before 6.38). An
algorithm making `k` oracle queries, interleaved with arbitrary unitaries `U₁,…,U_k`, produces

* `ψˣ_k = U_k Oₓ U_{k−1} Oₓ ⋯ U₁ Oₓ ψ` — the state **with** the oracle (eq. 6.38);
* `ψ_k  = U_k U_{k−1} ⋯ U₁ ψ` — the state that would result **without** the oracle (eq. 6.39).

The **deviation** `Dₖ = ∑ₓ ‖ψˣ_k − ψ_k‖²` (eq. 6.40) measures how far the oracle can move the state
after `k` queries; a small `Dₖ` means the `ψˣ_k` are nearly independent of `x`, so the solution
cannot be identified. The key upper bound (eqs. 6.41–6.46) is `Dₖ ≤ 4k²`.

## Main declarations

* `searchOracle v` — the reflection `Oₓ = I − 2|v⟩⟨v|`, taken (for a unit `v`) to be Mathlib's
  reflection across the hyperplane `(ℂ ∙ v)ᗮ` (`Submodule.reflection`), a `LinearIsometryEquiv`.
  `searchOracle_apply` gives its action `w ↦ w − 2⟪v,w⟫•v` and `norm_searchOracle_apply` its
  norm-preservation (free, as a linear isometry).
* `searchQueryState` / `searchNoQueryState` — the states `ψˣ_k` and `ψ_k`, by recursion on `k`.
* `searchDeviation` — the deviation `Dₖ`.
* `searchDeviation_le_four_mul_sq` — **`Dₖ ≤ 4k²`**, by induction. The induction step
  (`sum_norm_searchOracle_sub_sq_le`) drops `U_{k+1}` by unitary invariance, splits
  `Oₓψˣ_k − ψ_k = Oₓ(ψˣ_k − ψ_k) + (Oₓ − I)ψ_k` with `(Oₓ − I)ψ_k = −2⟪x,ψ_k⟫|x⟩`, and bounds the
  cross term by `4√Dₖ` (Cauchy–Schwarz for finite sums, `Finset.sum_mul_sq_le_sq_mul_sq`) and the
  quadratic term by `4` (Bessel's inequality, `Orthonormal.sum_inner_products_le`), giving
  `Dₖ₊₁ ≤ Dₖ + 4√Dₖ + 4 ≤ 4(k+1)²`.

## Faithfulness

Only Bessel's inequality (`∑ₓ |⟪x,ψ_k⟫|² ≤ ‖ψ_k‖² = 1`) is used for the marked family, so `e` need
only be an orthonormal **family**, not a basis — the natural generality, not a weakening. The
`U`'s appear only through norm-preservation and linearity, so the bound holds for any choice of
unitary steps: `searchDeviation_le_four_mul_sq` quantifies over all of them.
-/

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {N : ℕ}

/-- The **search oracle** `Oₓ = I − 2|v⟩⟨v|`, the reflection that phase-flips the marked vector `v`.
For a unit `v` this is exactly Mathlib's reflection across the hyperplane `(ℂ ∙ v)ᗮ`
(`Submodule.reflection`), a `LinearIsometryEquiv` — so it is automatically norm-preserving
(unitary), the self-adjoint unitary `Oₓ` of Nielsen & Chuang §6.6. The `HasOrthogonalProjection`
instance comes from `ℂ ∙ v` being finite-dimensional, so no completeness of `H` is needed. -/
noncomputable def searchOracle (v : H) : H ≃ₗᵢ[ℂ] H := Submodule.reflection (ℂ ∙ v)ᗮ

/-- The action of the search oracle on a **unit** marked vector: `Oₓ w = w − 2⟪v,w⟫•v` (for
`‖v‖ = 1`). It unfolds via `Submodule.reflection_orthogonal_apply` (reflection in `Kᗮ` is `−`
reflection in `K`) and `Submodule.reflection_singleton_apply`, whose `/‖v‖²` factor is `1` here. -/
theorem searchOracle_apply {v : H} (hv : ‖v‖ = 1) (w : H) :
    searchOracle v w = w - (2 * inner ℂ v w) • v := by
  simp only [searchOracle, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, hv]
  module

/-- The search oracle is **norm-preserving** (unitary): `‖Oₓ w‖ = ‖w‖`, immediate since `Oₓ` is a
`LinearIsometryEquiv`. -/
theorem norm_searchOracle_apply (v w : H) : ‖searchOracle v w‖ = ‖w‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- The **with-oracle** state `ψˣ_k = U_k Oₓ U_{k−1} Oₓ ⋯ U₁ Oₓ ψ` after `k` oracle queries against
the marked vector `v`, with interleaved unitary steps `U`. Defined by recursion on `k`
(N&C eq. 6.38). -/
noncomputable def searchQueryState (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ v : H) : ℕ → H
  | 0 => ψ
  | j + 1 => U j (searchOracle v (searchQueryState U ψ v j))

/-- The **no-oracle** state `ψ_k = U_k U_{k−1} ⋯ U₁ ψ`: the same unitary schedule with every oracle
query replaced by the identity (N&C eq. 6.39). -/
noncomputable def searchNoQueryState (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ : H) : ℕ → H
  | 0 => ψ
  | j + 1 => U j (searchNoQueryState U ψ j)

/-- The no-oracle state stays normalized: `‖ψ_k‖ = ‖ψ‖`, since each `U j` is an isometry. -/
theorem norm_searchNoQueryState (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ : H) (k : ℕ) :
    ‖searchNoQueryState U ψ k‖ = ‖ψ‖ := by
  induction k with
  | zero => rfl
  | succ j ih => rw [searchNoQueryState, LinearIsometryEquiv.norm_map, ih]

/-- The **deviation** `Dₖ = ∑ₓ ‖ψˣ_k − ψ_k‖²` after `k` queries, over the marked family `e`
(N&C eq. 6.40): a measure of how much the oracle can perturb the algorithm's state. -/
noncomputable def searchDeviation (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ : H) (e : Fin N → H) (k : ℕ) : ℝ :=
  ∑ x, ‖searchQueryState U ψ (e x) k - searchNoQueryState U ψ k‖ ^ 2

/-- Unrolling `Dₖ₊₁`: the outer unitary `U_k` is common to both states and norm-preserving, so it
drops out and `Dₖ₊₁ = ∑ₓ ‖Oₓ ψˣ_k − ψ_k‖²` (N&C eq. 6.41). -/
theorem searchDeviation_succ (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ : H) (e : Fin N → H) (k : ℕ) :
    searchDeviation U ψ e (k + 1)
      = ∑ x, ‖searchOracle (e x) (searchQueryState U ψ (e x) k)
          - searchNoQueryState U ψ k‖ ^ 2 := by
  simp only [searchDeviation, searchQueryState, searchNoQueryState]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← map_sub, LinearIsometryEquiv.norm_map]

/-- The **inductive step** for `Dₖ ≤ 4k²` (N&C eqs. 6.42–6.45). For an orthonormal family `e`, any
vectors `a x` (the states `ψˣ_k`) and a unit vector `p` (the state `ψ_k`),
`∑ₓ ‖Oₓ (a x) − p‖² ≤ ∑ₓ ‖a x − p‖² + 4·√(∑ₓ ‖a x − p‖²) + 4`.

Termwise `Oₓ(a x) − p = Oₓ(a x − p) + (Oₓ p − p)`, and `‖Oₓ(a x − p)‖ = ‖a x − p‖`,
`‖Oₓ p − p‖ = 2‖⟪e x, p⟫‖`; the triangle inequality then bounds each summand by
`(‖a x − p‖ + 2‖⟪e x, p⟫‖)²`. Summing, the cross term is bounded via the finite Cauchy–Schwarz
inequality and the quadratic term via Bessel's inequality `∑ₓ ‖⟪e x, p⟫‖² ≤ ‖p‖² = 1`. -/
theorem sum_norm_searchOracle_sub_sq_le {e : Fin N → H} (he : Orthonormal ℂ e) (a : Fin N → H)
    {p : H} (hp : ‖p‖ = 1) :
    ∑ x, ‖searchOracle (e x) (a x) - p‖ ^ 2
      ≤ (∑ x, ‖a x - p‖ ^ 2) + 4 * Real.sqrt (∑ x, ‖a x - p‖ ^ 2) + 4 := by
  have hpt : ∀ x, ‖searchOracle (e x) (a x) - p‖ ^ 2
      ≤ ‖a x - p‖ ^ 2 + 4 * (‖a x - p‖ * ‖inner ℂ (e x) p‖) + 4 * ‖inner ℂ (e x) p‖ ^ 2 := by
    intro x
    have hsplit : searchOracle (e x) (a x) - p
        = searchOracle (e x) (a x - p) + (searchOracle (e x) p - p) := by
      rw [map_sub]; abel
    have hb : ‖searchOracle (e x) (a x - p)‖ = ‖a x - p‖ := norm_searchOracle_apply _ _
    have hc : ‖searchOracle (e x) p - p‖ = 2 * ‖inner ℂ (e x) p‖ := by
      rw [searchOracle_apply (he.norm_eq_one x), sub_sub_cancel_left,
        norm_neg, norm_smul, norm_mul, he.norm_eq_one x, mul_one]
      norm_num
    have htri : ‖searchOracle (e x) (a x) - p‖ ≤ ‖a x - p‖ + 2 * ‖inner ℂ (e x) p‖ := by
      rw [hsplit]
      calc ‖searchOracle (e x) (a x - p) + (searchOracle (e x) p - p)‖
          ≤ ‖searchOracle (e x) (a x - p)‖ + ‖searchOracle (e x) p - p‖ := norm_add_le _ _
        _ = ‖a x - p‖ + 2 * ‖inner ℂ (e x) p‖ := by rw [hb, hc]
    calc ‖searchOracle (e x) (a x) - p‖ ^ 2
        ≤ (‖a x - p‖ + 2 * ‖inner ℂ (e x) p‖) ^ 2 := by gcongr
      _ = ‖a x - p‖ ^ 2 + 4 * (‖a x - p‖ * ‖inner ℂ (e x) p‖) + 4 * ‖inner ℂ (e x) p‖ ^ 2 := by ring
  have hsum : ∑ x, ‖searchOracle (e x) (a x) - p‖ ^ 2
      ≤ (∑ x, ‖a x - p‖ ^ 2) + 4 * (∑ x, ‖a x - p‖ * ‖inner ℂ (e x) p‖)
        + 4 * ∑ x, ‖inner ℂ (e x) p‖ ^ 2 := by
    calc ∑ x, ‖searchOracle (e x) (a x) - p‖ ^ 2
        ≤ ∑ x, (‖a x - p‖ ^ 2 + 4 * (‖a x - p‖ * ‖inner ℂ (e x) p‖) + 4 * ‖inner ℂ (e x) p‖ ^ 2) :=
          Finset.sum_le_sum (fun x _ => hpt x)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hSA2nonneg : (0 : ℝ) ≤ ∑ x, ‖a x - p‖ ^ 2 := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hSB2 : ∑ x, ‖inner ℂ (e x) p‖ ^ 2 ≤ 1 := by
    have h := he.sum_inner_products_le (s := Finset.univ) p
    rw [hp] at h; simpa using h
  have hSABnonneg : (0 : ℝ) ≤ ∑ x, ‖a x - p‖ * ‖inner ℂ (e x) p‖ :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hCS : (∑ x, ‖a x - p‖ * ‖inner ℂ (e x) p‖) ^ 2
      ≤ (∑ x, ‖a x - p‖ ^ 2) * ∑ x, ‖inner ℂ (e x) p‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hSAB : ∑ x, ‖a x - p‖ * ‖inner ℂ (e x) p‖ ≤ Real.sqrt (∑ x, ‖a x - p‖ ^ 2) :=
    (Real.le_sqrt hSABnonneg hSA2nonneg).2 (by nlinarith [hCS, hSB2, hSA2nonneg])
  linarith [hsum, hSAB, hSB2]

/-- **Nielsen & Chuang §6.6, `Dₖ ≤ 4k²`** (eqs. 6.41–6.46): the deviation caused by `k` oracle
queries grows at most quadratically. Proved by induction on `k`: `D₀ = 0`, and the step
`Dₖ₊₁ ≤ Dₖ + 4√Dₖ + 4` (`sum_norm_searchOracle_sub_sq_le`, using `‖ψ_k‖ = 1`) combined with the
hypothesis `Dₖ ≤ 4k²` gives `Dₖ₊₁ ≤ 4k² + 8k + 4 = 4(k+1)²`. -/
theorem searchDeviation_le_four_mul_sq (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ : H) {e : Fin N → H}
    (he : Orthonormal ℂ e) (hψ : ‖ψ‖ = 1) (k : ℕ) :
    searchDeviation U ψ e k ≤ 4 * (k : ℝ) ^ 2 := by
  induction k with
  | zero => simp [searchDeviation, searchQueryState, searchNoQueryState]
  | succ j ih =>
    have hns1 : ‖searchNoQueryState U ψ j‖ = 1 := (norm_searchNoQueryState U ψ j).trans hψ
    have hstep : searchDeviation U ψ e (j + 1)
        ≤ searchDeviation U ψ e j + 4 * Real.sqrt (searchDeviation U ψ e j) + 4 := by
      rw [searchDeviation_succ]
      have h := sum_norm_searchOracle_sub_sq_le he (fun x => searchQueryState U ψ (e x) j) hns1
      simpa only [searchDeviation] using h
    have hsqrt : Real.sqrt (searchDeviation U ψ e j) ≤ 2 * j :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [ih]⟩
    push_cast
    nlinarith [hstep, ih, hsqrt, Real.sqrt_nonneg (searchDeviation U ψ e j)]

end AxQM.Concrete
