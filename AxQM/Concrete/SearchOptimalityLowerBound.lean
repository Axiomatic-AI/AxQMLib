/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SearchOptimalityDeviation
import ToMathlib.Analysis.InnerProductSpace.OrthonormalDistanceSum

/-!
# Concrete: the averaged-error search optimality lower bound (N&C Exercise 6.16)

This file formalises the **second half** of Nielsen & Chuang's optimality proof for quantum search
(§6.6) together with the **average-case strengthening** asked for in Exercise 6.16. It continues the
linear algebra of `AxQM/Concrete/SearchOptimalityDeviation.lean` (a generic complex inner-product
space `H`, an orthonormal marked family `e : Fin N → H`, unitary steps `U : ℕ → (H ≃ₗᵢ[ℂ] H)`).
The statement for `QSystem`/`PureState`/`Evolution` is in `AxQM/NC/Ch6/Exercise6_16.lean`.

## The N&C argument (§6.6, eqs. 6.47–6.52) and the Exercise 6.16 delta

Write `ψˣ_k` for the with-oracle state and `ψ_k` for the no-oracle state after `k` queries, and
`Dₖ = ∑ₓ ‖ψˣ_k − ψ_k‖²` for the deviation (all from `SearchOptimalityDeviation.lean`, which also
proves `Dₖ ≤ 4k²`). The lower bound half runs:

* **Deviation lower bound (eqs. 6.48–6.51).** For *any* target family `e'ₓ`, writing
  `Eₖ = ∑ₓ ‖ψˣ_k − e'ₓ‖²` and `Fₖ = ∑ₓ ‖e'ₓ − ψ_k‖²`, the reverse triangle inequality plus
  Cauchy–Schwarz give `Dₖ ≥ (√Fₖ − √Eₖ)²` (`sq_sqrt_sum_sub_sqrt_sum_le_sum_norm_sub_sq`).
* **Phase alignment (eq. 6.47).** Replacing `|x⟩` by `eⁱᶿ|x⟩` leaves the oracle `Oₓ = I − 2|x⟩⟨x|`
  and hence `Dₖ` unchanged. Choosing the phase of `⟨eₓ, ψˣ_k⟩` gives an orthonormal target family
  `e'ₓ` with `‖ψˣ_k − e'ₓ‖² = 2 − 2|⟨eₓ, ψˣ_k⟩|` (`exists_orthonormal_norm_sub_sq_eq`).
* **Averaged error (the Exercise 6.16 delta).** N&C's `for all x` bound `|⟨x|ψˣ_k⟩|² ≥ 1/2` gives
  `Eₖ ≤ (2 − √2)N`. Here we only assume the **uniform average** success `(1/N)∑ₓ qₓ ≥ 1/2` with
  `qₓ = |⟨eₓ, ψˣ_k⟩|²`. Since `qₓ ∈ [0,1]`, `√qₓ ≥ qₓ`, so
  `Eₖ = ∑ₓ (2 − 2√qₓ) ≤ 2N − 2∑ₓ qₓ ≤ N` — a weaker but still sufficient bound.
* **Assembly (eq. 6.52).** With `Fₖ ≥ 2N − 2√N` (Exercise 6.15, supplied by
  `Orthonormal.two_mul_card_sub_two_mul_sqrt_card_le_sum_norm_sub_sq`) and `Eₖ ≤ N`, the deviation
  bound and `Dₖ ≤ 4k²` yield `√(2N − 2√N) − √N ≤ 2k` (`searchQueries_ge_of_averaged_success`), and
  hence the explicit `k ≥ √N/8` for `N ≥ 21` (`searchQueries_ge_sqrt_div_eight`) — i.e. `Ω(√N)`
  oracle calls are still required.

## Faithfulness

No weakening: the statements quantify over an arbitrary `k`-query algorithm (any initial unit state
`ψ`, any unitary schedule `U`, any orthonormal marked family `e`) and the averaged hypothesis, and
conclude `k = Ω(√N)`. The averaged criterion is genuinely weaker than N&C's `for all x` criterion,
exactly as Exercise 6.16 asks; the constant `1/8` and threshold `N ≥ 21` are an explicit
realisation of `Ω(√N)`.
-/

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {N : ℕ}

/-- The with-oracle state stays normalized: `‖ψˣ_k‖ = ‖ψ‖`, since each `U j` and each oracle
reflection is a linear isometry. -/
theorem norm_searchQueryState (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ v : H) (k : ℕ) :
    ‖searchQueryState U ψ v k‖ = ‖ψ‖ := by
  induction k with
  | zero => rfl
  | succ j ih =>
    rw [searchQueryState, LinearIsometryEquiv.norm_map, norm_searchOracle_apply, ih]

/-- **Deviation lower bound** (N&C eqs. 6.48–6.51): for any families `a`, `b : Fin N → H` and any
vector `p`, writing `E = ∑ₓ ‖a x − b x‖²`, `F = ∑ₓ ‖b x − p‖²`, `D = ∑ₓ ‖a x − p‖²`, one has
`(√F − √E)² ≤ D`. Applied with `a x = ψˣ_k`, `b x = e'ₓ` (aligned targets), `p = ψ_k`, and `D` the
deviation `Dₖ`, this is `Dₖ ≥ (√Fₖ − √Eₖ)²`.

Termwise `a x − p = (a x − b x) + (b x − p)`, so
`‖a x − p‖² = ‖a x − b x‖² + 2·Re⟪a x − b x, b x − p⟫ + ‖b x − p‖²`. Summing, the cross term is
bounded below by `−∑ₓ ‖a x − b x‖‖b x − p‖ ≥ −√E·√F` (Cauchy–Schwarz for finite sums,
`Finset.sum_mul_sq_le_sq_mul_sq`), giving `D ≥ E + F − 2√E√F = (√F − √E)²`. -/
theorem sq_sqrt_sum_sub_sqrt_sum_le_sum_norm_sub_sq (a b : Fin N → H) (p : H) :
    (Real.sqrt (∑ x, ‖b x - p‖ ^ 2) - Real.sqrt (∑ x, ‖a x - b x‖ ^ 2)) ^ 2
      ≤ ∑ x, ‖a x - p‖ ^ 2 := by
  set E := ∑ x, ‖a x - b x‖ ^ 2 with hE
  set F := ∑ x, ‖b x - p‖ ^ 2 with hF
  set S := ∑ x, RCLike.re (inner ℂ (a x - b x) (b x - p)) with hS
  have hEnn : 0 ≤ E := Finset.sum_nonneg fun x _ => by positivity
  have hFnn : 0 ≤ F := Finset.sum_nonneg fun x _ => by positivity
  -- Expand each summand of `D` via `‖u + v‖²`.
  have hexp : ∑ x, ‖a x - p‖ ^ 2
      = ∑ x, (‖a x - b x‖ ^ 2 + 2 * RCLike.re (inner ℂ (a x - b x) (b x - p)) + ‖b x - p‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [show a x - p = (a x - b x) + (b x - p) from (sub_add_sub_cancel _ _ _).symm,
      norm_add_pow_two (𝕜 := ℂ)]
  have hsum_eq : ∑ x, (‖a x - b x‖ ^ 2 + 2 * RCLike.re (inner ℂ (a x - b x) (b x - p))
      + ‖b x - p‖ ^ 2) = E + 2 * S + F := by
    rw [hE, hF, hS, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- Cross term: `S ≥ −√E·√F`.
  have hcross : - (Real.sqrt E * Real.sqrt F) ≤ S := by
    have hpt : ∀ x, - (‖a x - b x‖ * ‖b x - p‖)
        ≤ RCLike.re (inner ℂ (a x - b x) (b x - p)) := by
      intro x
      have hre : - ‖inner ℂ (a x - b x) (b x - p)‖
          ≤ RCLike.re (inner ℂ (a x - b x) (b x - p)) := (abs_le.mp (RCLike.abs_re_le_norm _)).1
      have hcs : ‖inner ℂ (a x - b x) (b x - p)‖ ≤ ‖a x - b x‖ * ‖b x - p‖ := norm_inner_le_norm _ _
      linarith
    have hsum_nn : 0 ≤ ∑ x, ‖a x - b x‖ * ‖b x - p‖ :=
      Finset.sum_nonneg fun x _ => by positivity
    have hcs2 : (∑ x, ‖a x - b x‖ * ‖b x - p‖) ^ 2 ≤ E * F := by
      rw [hE, hF]; exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hle : ∑ x, ‖a x - b x‖ * ‖b x - p‖ ≤ Real.sqrt E * Real.sqrt F := by
      rw [← Real.sqrt_mul hEnn]
      calc ∑ x, ‖a x - b x‖ * ‖b x - p‖
          = Real.sqrt ((∑ x, ‖a x - b x‖ * ‖b x - p‖) ^ 2) := (Real.sqrt_sq hsum_nn).symm
        _ ≤ Real.sqrt (E * F) := Real.sqrt_le_sqrt hcs2
    have hstep : - (∑ x, ‖a x - b x‖ * ‖b x - p‖) ≤ S := by
      rw [hS, ← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun x _ => hpt x
    linarith
  have hsq : (Real.sqrt F - Real.sqrt E) ^ 2 = F - 2 * (Real.sqrt E * Real.sqrt F) + E := by
    rw [sub_sq, Real.sq_sqrt hFnn, Real.sq_sqrt hEnn]; ring
  rw [hexp, hsum_eq]
  linarith [hcross, hsq]

/-- The unit-modulus **phase alignment** scalar of a complex number: `z / ‖z‖` (or `1` when
`z = 0`), the complex number `c` with `‖c‖ = 1` and `conj c · z = ‖z‖` used to rotate a marked
basis vector so that `⟨e'ₓ, ψˣ_k⟩` is real and nonnegative (N&C eq. 6.47, replacing `|x⟩` by
`eⁱᶿ|x⟩`). -/
noncomputable def alignPhase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

/-- The phase-alignment scalar has unit modulus. -/
theorem norm_alignPhase (z : ℂ) : ‖alignPhase z‖ = 1 := by
  unfold alignPhase
  split
  · simp
  · rename_i h
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z),
      div_self (norm_ne_zero_iff.mpr h)]

/-- The defining property of the phase-alignment scalar: `conj (alignPhase z) · z = ‖z‖` (a
nonnegative real). -/
theorem conj_alignPhase_mul (z : ℂ) : (starRingEnd ℂ) (alignPhase z) * z = (‖z‖ : ℂ) := by
  unfold alignPhase
  split
  · rename_i h; subst h; simp
  · rename_i h
    have hz : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
    rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm ((starRingEnd ℂ) z) z,
      Complex.mul_conj', div_eq_iff hz]
    ring

/-- **Phase alignment** (N&C eq. 6.47): for an orthonormal family `e` and any family of unit
vectors `a` (the states `ψˣ_k`), there is an orthonormal target family `b` (the rotated basis
`e'ₓ`) with `‖a x − b x‖² = 2 − 2|⟨eₓ, a x⟩|`. Concretely `b x = alignPhase ⟨eₓ, a x⟩ • eₓ`, which
is orthonormal since `‖alignPhase _‖ = 1`, and for which `Re⟨a x, b x⟩ = |⟨eₓ, a x⟩|`. -/
theorem exists_orthonormal_norm_sub_sq_eq {e : Fin N → H} (he : Orthonormal ℂ e)
    {a : Fin N → H} (ha : ∀ x, ‖a x‖ = 1) :
    ∃ b : Fin N → H, Orthonormal ℂ b ∧
      ∀ x, ‖a x - b x‖ ^ 2 = 2 - 2 * ‖inner ℂ (e x) (a x)‖ := by
  classical
  refine ⟨fun x => alignPhase (inner ℂ (e x) (a x)) • e x, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    rw [inner_smul_left, inner_smul_right, (orthonormal_iff_ite.mp he) i j]
    split_ifs with hij
    · subst hij
      rw [mul_one, RCLike.conj_mul, norm_alignPhase]
      norm_num
    · rw [mul_zero, mul_zero]
  · intro x
    set z := inner ℂ (e x) (a x) with hz
    have hin : inner ℂ (a x) (alignPhase z • e x) = (‖z‖ : ℂ) := by
      rw [inner_smul_right, ← inner_conj_symm]
      have h1 := congrArg (starRingEnd ℂ) (conj_alignPhase_mul z)
      simpa only [map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm] using h1
    rw [norm_sub_pow_two (𝕜 := ℂ), ha x, hin, norm_smul, norm_alignPhase, he.norm_eq_one x]
    norm_num [RCLike.ofReal_re]
    ring

/-- **Nielsen & Chuang Exercise 6.16, the query bound** (§6.6, eqs. 6.47–6.52). For a `k`-query
search algorithm — initial unit state `ψ`, unitary schedule `U`, orthonormal marked family `e` — if
the **uniformly averaged** success probability is at least `1/2`, i.e. `N/2 ≤ ∑ₓ |⟨eₓ, ψˣ_k⟩|²`,
then `√(2N − 2√N) − √N ≤ 2k`.

Proof: phase-align to an orthonormal target family `b` with `Eₖ := ∑ₓ ‖ψˣ_k − b x‖² = ∑ₓ (2 − 2√qₓ)`
where `qₓ = |⟨eₓ, ψˣ_k⟩|² ∈ [0,1]`. Since `√qₓ ≥ qₓ` and `N/2 ≤ ∑ₓ qₓ`, we get `Eₖ ≤ N`. Exercise
6.15 gives `Fₖ := ∑ₓ ‖b x − ψ_k‖² ≥ 2N − 2√N`, and the ℓ² reverse triangle inequality
`sq_sqrt_sum_sub_sqrt_sum_le_sum_norm_sub_sq` gives `(√Fₖ − √Eₖ)² ≤ Dₖ ≤ 4k²`
(`searchDeviation_le_four_mul_sq`). Taking square roots and using
`√Fₖ ≥ √(2N − 2√N)`, `√Eₖ ≤ √N` yields the claim. -/
theorem searchQueries_ge_of_averaged_success (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ : H) {e : Fin N → H}
    (he : Orthonormal ℂ e) (hψ : ‖ψ‖ = 1) (k : ℕ)
    (havg : (N : ℝ) / 2 ≤ ∑ x, ‖inner ℂ (e x) (searchQueryState U ψ (e x) k)‖ ^ 2) :
    Real.sqrt (2 * (N : ℝ) - 2 * Real.sqrt N) - Real.sqrt N ≤ 2 * k := by
  classical
  -- Name the algorithm states.
  set a : Fin N → H := fun x => searchQueryState U ψ (e x) k with ha_def
  set p : H := searchNoQueryState U ψ k with hp_def
  have hanorm : ∀ x, ‖a x‖ = 1 := fun x => (norm_searchQueryState U ψ (e x) k).trans hψ
  have hpnorm : ‖p‖ = 1 := (norm_searchNoQueryState U ψ k).trans hψ
  -- Aligned orthonormal target family `b`.
  obtain ⟨b, hb_on, hb_val⟩ := exists_orthonormal_norm_sub_sq_eq he hanorm
  set q : Fin N → ℝ := fun x => ‖inner ℂ (e x) (a x)‖ ^ 2 with hq_def
  have hq_nonneg : ∀ x, 0 ≤ q x := fun x => by rw [hq_def]; positivity
  have hq_le_one : ∀ x, q x ≤ 1 := by
    intro x
    have hcs := norm_inner_le_norm (𝕜 := ℂ) (e x) (a x)
    rw [he.norm_eq_one x, hanorm x, mul_one] at hcs
    rw [hq_def]
    nlinarith [norm_nonneg (inner ℂ (e x) (a x)), hcs]
  -- `Eₖ = ∑ (2 − 2√qₓ)`.
  have hEval : ∑ x, ‖a x - b x‖ ^ 2 = ∑ x, (2 - 2 * Real.sqrt (q x)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [hb_val x, hq_def, Real.sqrt_sq (norm_nonneg _)]
  -- `Eₖ ≤ N`.
  have hsqrt_ge : ∀ x, q x ≤ Real.sqrt (q x) := by
    intro x
    rw [Real.le_sqrt (hq_nonneg x) (hq_nonneg x)]
    nlinarith [hq_le_one x, hq_nonneg x]
  have hE_le : ∑ x, ‖a x - b x‖ ^ 2 ≤ N := by
    rw [hEval]
    have hsplit : ∑ x, (2 - 2 * Real.sqrt (q x))
        = 2 * (N : ℝ) - 2 * ∑ x, Real.sqrt (q x) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hqle : ∑ x, q x ≤ ∑ x, Real.sqrt (q x) := Finset.sum_le_sum fun x _ => hsqrt_ge x
    rw [hsplit]
    linarith [havg, hqle]
  -- `Fₖ ≥ 2N − 2√N` (Exercise 6.15).
  have hF_ge : 2 * (N : ℝ) - 2 * Real.sqrt N ≤ ∑ x, ‖b x - p‖ ^ 2 := by
    have h615 := hb_on.two_mul_card_sub_two_mul_sqrt_card_le_sum_norm_sub_sq hpnorm
    rw [Fintype.card_fin] at h615
    refine h615.trans_eq (Finset.sum_congr rfl fun x _ => ?_)
    rw [norm_sub_rev]
  -- Deviation bound `(√Fₖ − √Eₖ)² ≤ Dₖ ≤ 4k²`.
  have hDdef : searchDeviation U ψ e k = ∑ x, ‖a x - p‖ ^ 2 := rfl
  have hDev_ge : (Real.sqrt (∑ x, ‖b x - p‖ ^ 2) - Real.sqrt (∑ x, ‖a x - b x‖ ^ 2)) ^ 2
      ≤ searchDeviation U ψ e k := by
    rw [hDdef]; exact sq_sqrt_sum_sub_sqrt_sum_le_sum_norm_sub_sq a b p
  have hDk_le : searchDeviation U ψ e k ≤ 4 * (k : ℝ) ^ 2 :=
    searchDeviation_le_four_mul_sq U ψ he hψ k
  -- `L² ≤ (2k)²`, hence `L ≤ 2k`.
  set L := Real.sqrt (∑ x, ‖b x - p‖ ^ 2) - Real.sqrt (∑ x, ‖a x - b x‖ ^ 2) with hL
  have hLsq : L ^ 2 ≤ (2 * (k : ℝ)) ^ 2 := by
    refine hDev_ge.trans (hDk_le.trans_eq ?_); ring
  have hL_le : L ≤ 2 * (k : ℝ) := by
    calc L ≤ |L| := le_abs_self L
      _ = Real.sqrt (L ^ 2) := (Real.sqrt_sq_eq_abs L).symm
      _ ≤ Real.sqrt ((2 * (k : ℝ)) ^ 2) := Real.sqrt_le_sqrt hLsq
      _ = 2 * k := by rw [Real.sqrt_sq (by positivity)]
  -- `M ≤ L`: `√Fₖ ≥ √(2N−2√N)` and `√Eₖ ≤ √N`.
  have hFge : Real.sqrt (2 * (N : ℝ) - 2 * Real.sqrt N) ≤ Real.sqrt (∑ x, ‖b x - p‖ ^ 2) :=
    Real.sqrt_le_sqrt hF_ge
  have hEle : Real.sqrt (∑ x, ‖a x - b x‖ ^ 2) ≤ Real.sqrt N :=
    Real.sqrt_le_sqrt hE_le
  rw [hL] at hL_le
  linarith [hFge, hEle, hL_le]

/-- **Nielsen & Chuang Exercise 6.16** (the `Ω(√N)` conclusion). Under the uniformly averaged
success criterion `N/2 ≤ ∑ₓ |⟨eₓ, ψˣ_k⟩|²`, a `k`-query search algorithm needs `k ≥ √N/8` for
`N ≥ 21`:
`O(√N)` oracle calls are still required. This is the clean explicit realisation of the query bound
`√(2N − 2√N) − √N ≤ 2k`; for `N ≥ 21` one has `√(2N − 2√N) − √N ≥ √N/4`, whence `√N/8 ≤ k`. -/
theorem searchQueries_ge_sqrt_div_eight (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ : H) {e : Fin N → H}
    (he : Orthonormal ℂ e) (hψ : ‖ψ‖ = 1) (k : ℕ) (hN : 21 ≤ N)
    (havg : (N : ℝ) / 2 ≤ ∑ x, ‖inner ℂ (e x) (searchQueryState U ψ (e x) k)‖ ^ 2) :
    Real.sqrt N / 8 ≤ (k : ℝ) := by
  have hmain := searchQueries_ge_of_averaged_success U ψ he hψ k havg
  have hNr : (21 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN_pos : (0 : ℝ) < N := by linarith
  have hsqN_sq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN_pos.le
  have hsqN_nonneg : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  -- `√N ≥ 32/7` (since `(32/7)² = 1024/49 ≤ 21 ≤ N`).
  have hsqN_ge : (32 : ℝ) / 7 ≤ Real.sqrt N := by
    rw [show (32 : ℝ) / 7 = Real.sqrt ((32 / 7) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [hNr]
  -- `2N − 2√N ≥ (25/16)N ≥ 0`.
  have hkey : (25 : ℝ) / 16 * N ≤ 2 * N - 2 * Real.sqrt N := by
    nlinarith [hsqN_sq, hsqN_ge, hsqN_nonneg]
  have hInner_nonneg : 0 ≤ 2 * (N : ℝ) - 2 * Real.sqrt N := by nlinarith [hkey, hN_pos]
  -- `√(2N − 2√N) ≥ (5/4)√N`, so `√(2N − 2√N) − √N ≥ √N/4`.
  have h54 : 5 / 4 * Real.sqrt N ≤ Real.sqrt (2 * N - 2 * Real.sqrt N) := by
    rw [Real.le_sqrt (by positivity) hInner_nonneg]
    nlinarith [hsqN_sq, hkey]
  linarith [hmain, h54]

end AxQM.Concrete
