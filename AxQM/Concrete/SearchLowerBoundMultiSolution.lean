/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib
import ToMathlib.Analysis.InnerProductSpace.RankOneProjector
import ToMathlib.Analysis.InnerProductSpace.EntanglementFidelityBound

/-!
# The multiple-solution quantum search lower bound: query model and marked-weight identity

*(Supports Nielsen & Chuang, Exercise 6.17 — "Optimality for multiple solutions", N&C p. 271.)*

N&C §6.6 ("Optimality of the search algorithm") proves that any quantum algorithm needs
`Ω(√N)` oracle calls to find the *single* solution of a search problem. Exercise 6.17 asks for the
`M`-solution generalisation: when the search problem has `M` solutions, `Ω(√(N/M))` oracle
applications are still required to find one. Both are instances of the Bennett–Bernstein–Brassard–
Vazirani (BBBV) hybrid argument, here generalised to mark an arbitrary size-`M` set of items.

This file lays the foundation, entirely as linear algebra on a complex
inner-product space `H` with an orthonormal basis `b : OrthonormalBasis (Fin N) ℂ H` (the search
basis `{|x⟩}`).

## The query model

For a marked set `s : Finset (Fin N)` of solutions:

* `markedProj b s = orthonormalProjector ℂ b s` — the orthogonal projection `P_s` onto the span of
  the marked basis vectors, **reused** from `ToMathlib.Analysis.InnerProductSpace.RankOneProjector`
  (Nielsen & Chuang eq. (2.35)). Its API supplies self-adjointness and idempotence for free;
  `inner_markedProj` (`⟪v, P_s v⟫ = ‖P_s v‖²`) is derived from those, and `markedProj_norm_sq`
  (`‖P_s v‖² = ∑_{y∈s} ‖⟪b y, v⟫‖²`) from the projector's explicit value.
* `markedOracle b s = 1 − 2 • P_s` — the search oracle `O_s = I − 2 P_s`, the reflection that
  phase-flips exactly the marked items, as a continuous linear map. It preserves norm
  (`markedOracle_norm`) and `‖O_s v − v‖ = 2‖P_s v‖` (`markedOracle_sub_self_norm`); linearity is
  the built-in `map_sub`.
* `markedRun`/`markedRunFree` — the state after `k` steps of a `k`-query algorithm given by a
  family of unitaries `U : ℕ → (H ≃ₗᵢ[ℂ] H)`, run **with** the oracle `O_s` interleaved
  (`ψˢ_k = U_{k-1} O_s ⋯ U_0 O_s ψ`) and **without** it (`ψ_k = U_{k-1} ⋯ U_0 ψ`). Both preserve
  norm (`markedRun_norm`, `markedRunFree_norm`).

## The marked-weight identity (headline)

`sum_markedProj_normSq_eq`: for a **unit** vector `v` and `1 ≤ M`,
`∑_{|s| = M} ‖P_s v‖² = C(N−1, M−1)`. This is the per-step "marked query weight" summed over all
`C(N, M)` size-`M` worlds; it is the ingredient the hybrid induction (`Dₖ ≤ 4k²·C(N−1,M−1)`,
below) contracts against. The proof double-counts using the general lemma
`Finset.card_filter_mem_powersetCard` (each item lies in `C(N−1,M−1)` of the size-`M` subsets), and
`∑_y ‖⟪b y, v⟫‖² = ‖v‖² = 1` (Parseval).

## Part (a): the sensitivity bound `Dₖ ≤ 4k²·C(N−1,M−1)`

The **deviation** `markedDeviation` aggregates the oracle's perturbation over every size-`M` world,
`Dₖ = ∑_{|s|=M} ‖ψˢ_k − ψ_k‖²` (the `M`-solution analogue of N&C eq. 6.40). Its **sensitivity
bound** `markedDeviation_le`,
`Dₖ ≤ 4k²·C(N−1,M−1)`,
is the `M`-solution analogue of N&C's `Dₖ ≤ 4k²` (eqs. 6.41–6.46). The induction step
(`sum_norm_markedOracle_sub_sq_le`) drops the outer unitary by norm-preservation, splits
`O_s ψˢ_k − ψ_k = O_s(ψˢ_k − ψ_k) + (O_s − I)ψ_k`, and bounds the cross term by the finite
Cauchy–Schwarz inequality and the quadratic term `∑_{|s|=M} ‖P_s ψ_k‖²` by the marked-weight
identity `C(N−1,M−1)` (exactly, replacing N&C's single-solution Bessel bound `≤ 1`). This yields
`Dₖ₊₁ ≤ (√Dₖ + 2√C(N−1,M−1))²`, whence `√Dₖ ≤ 2k·√C(N−1,M−1)` and the stated bound. It is the
"grows no faster than `O(k²)`" half of the sandwich.

## Part (b): the success lower bound, and the assembly to `k ≥ Ω(√(N/M))`

The other half of the sandwich, `markedDeviation_ge`: if the algorithm **succeeds** — for every
size-`M` world `s`, measuring the final state `ψˢ_k` returns a solution with probability
`‖P_s ψˢ_k‖² ≥ 1/2` — then
`√(C(N,M)/2) ≤ √Dₖ + √C(N−1,M−1)`.
This is the `M`-solution analogue of N&C's `Dₖ ≥ (√Fₖ − √Eₖ)²` (eqs. 6.48–6.51), reorganised to
avoid a per-world target vector: it is the ℓ²-triangle (Minkowski) inequality
(`Real.sqrt_sum_sq_le_sqrt_sum_sub_sq_add`, a `Real.sqrt`-form corollary of Mathlib's
`Real.Lp_add_le`, in `ToMathlib/`) over the worlds, applied to `u_s = ‖P_s ψˢ_k‖`
and `w_s = ‖P_s ψ_k‖`. `P_s` is a contraction (`markedProj_norm_le`),
so `∑_s (u_s − w_s)² ≤ Dₖ`; success gives `∑_s u_s² ≥ C(N,M)/2`; and the marked-weight identity
gives `∑_s w_s² = C(N−1,M−1)`.

The **headline** `search_lower_bound_multi_solution` sandwiches the two bounds:
`√(C(N,M)/2) ≤ √Dₖ + √C(N−1,M−1) ≤ (2k+1)·√C(N−1,M−1)`, so `C(N,M)/2 ≤ (2k+1)²·C(N−1,M−1)`. The
combinatorial identity `N·C(N−1,M−1) = M·C(N,M)` (`Nat.add_one_mul_choose_eq`) collapses this to
`N/(2M) ≤ (2k+1)²` (cancelling `C(N−1,M−1) > 0`, using `M ≤ N`), giving
`k ≥ ½·(√(N/2M) − 1) = Ω(√(N/M))` — the multiple-solution optimality bound of Exercise 6.17. Its
physical (Born-rule) statement is the main theorem of `AxQM/NC/Ch6/Exercise6_17.lean`.
-/

open scoped BigOperators InnerProductSpace
open Finset InnerProductSpace

namespace AxQM.Concrete

noncomputable section

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The marked projection `P_s`: the orthogonal projection onto the span of the marked basis vectors
`{b y : y ∈ s}`, reused from Mathlib's `orthonormalProjector` (N&C eq. (2.35)). -/
def markedProj (b : OrthonormalBasis (Fin N) ℂ H) (s : Finset (Fin N)) : H →L[ℂ] H :=
  orthonormalProjector ℂ (⇑b) s

/-- `P_s v = ∑_{y ∈ s} ⟪b y, v⟫ • b y` (the projector's explicit value on the orthonormal basis). -/
lemma markedProj_apply (b : OrthonormalBasis (Fin N) ℂ H) (s : Finset (Fin N)) (v : H) :
    markedProj b s v = ∑ y ∈ s, (inner ℂ (b y) v : ℂ) • b y := by
  rw [markedProj, orthonormalProjector_apply]

/-- **The marked projection fixes each marked basis vector:** `P_s (b y) = b y` for `y ∈ s` — the
eigenvalue-`1` action of the orthogonal projector on a basis vector it spans. Only the marked
summand `y` survives the explicit sum `∑_{z∈s} ⟪b z, b y⟫ • b z`, since `⟪b z, b y⟫ = δ_{zy}` by
orthonormality. -/
lemma markedProj_apply_mem (b : OrthonormalBasis (Fin N) ℂ H) {s : Finset (Fin N)} {y : Fin N}
    (hy : y ∈ s) : markedProj b s (b y) = b y := by
  rw [markedProj_apply, Finset.sum_eq_single y]
  · rw [orthonormal_iff_ite.mp b.orthonormal y y]; simp
  · intro z _ hzy
    rw [orthonormal_iff_ite.mp b.orthonormal z y, ite_eq_right hzy, zero_smul]
  · intro hy'; exact absurd hy hy'

/-- Pythagoras for the marked projection: `‖P_s v‖² = ∑_{y ∈ s} ‖⟪b y, v⟫‖²`. -/
lemma markedProj_norm_sq (b : OrthonormalBasis (Fin N) ℂ H) (s : Finset (Fin N)) (v : H) :
    ‖markedProj b s v‖ ^ 2 = ∑ y ∈ s, ‖(inner ℂ (b y) v : ℂ)‖ ^ 2 := by
  rw [markedProj_apply, @norm_sq_eq_re_inner ℂ, sum_inner]
  have hb : ∀ y i : Fin N, (inner ℂ (b y) (b i)) = if y = i then (1 : ℂ) else 0 :=
    fun y i => (orthonormal_iff_ite.mp b.orthonormal) y i
  simp only [inner_sum, inner_smul_left, inner_smul_right, hb, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq]
  rw [Finset.sum_ite_of_true (by intro x hx; simpa using hx), ← RCLike.reLm_coe, map_sum,
    RCLike.reLm_coe]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [RCLike.mul_conj]
  norm_cast

/-- `⟪v, P_s v⟫ = ‖P_s v‖²` (real): a free consequence of the projector being self-adjoint and
idempotent (`⟪v, P v⟫ = ⟪v, P (P v)⟫ = ⟪P v, P v⟫ = ‖P v‖²`). -/
lemma inner_markedProj (b : OrthonormalBasis (Fin N) ℂ H) (s : Finset (Fin N)) (v : H) :
    (inner ℂ v (markedProj b s v) : ℂ) = (‖markedProj b s v‖ ^ 2 : ℝ) := by
  have : FiniteDimensional ℂ H := Module.Basis.finiteDimensional_of_finite b.toBasis
  have hsa : IsSelfAdjoint (markedProj b s) := isSelfAdjoint_orthonormalProjector (𝕜 := ℂ) (⇑b) s
  have hid : IsIdempotentElem (markedProj b s) :=
    isIdempotentElem_orthonormalProjector b.orthonormal s
  exact inner_self_of_isSelfAdjoint_of_isIdempotent hsa hid v

/-- The search oracle `O_s = I − 2 P_s`: the reflection phase-flipping the marked items, as a
continuous linear map. -/
def markedOracle (b : OrthonormalBasis (Fin N) ℂ H) (s : Finset (Fin N)) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - (2 : ℂ) • markedProj b s

/-- `O_s v = v − 2 • P_s v`. -/
lemma markedOracle_apply (b : OrthonormalBasis (Fin N) ℂ H) (s : Finset (Fin N)) (v : H) :
    markedOracle b s v = v - (2 : ℂ) • markedProj b s v := by
  simp [markedOracle]

/-- The search oracle preserves norm: `‖O_s v‖ = ‖v‖` (it is a reflection, hence unitary). -/
lemma markedOracle_norm (b : OrthonormalBasis (Fin N) ℂ H) (s : Finset (Fin N)) (v : H) :
    ‖markedOracle b s v‖ = ‖v‖ := by
  have h2 : ‖markedOracle b s v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [markedOracle_apply, @norm_sub_sq ℂ, inner_smul_right, inner_markedProj, norm_smul]
    simp [-Complex.ofReal_pow]; ring
  nlinarith [norm_nonneg v, norm_nonneg (markedOracle b s v), h2]

/-- `O_s v − v = −2 • P_s v`, so `‖O_s v − v‖ = 2 ‖P_s v‖`: the oracle's deviation from the identity
is twice the marked projection. -/
lemma markedOracle_sub_self_norm (b : OrthonormalBasis (Fin N) ℂ H) (s : Finset (Fin N)) (v : H) :
    ‖markedOracle b s v - v‖ = 2 * ‖markedProj b s v‖ := by
  have hrw : markedOracle b s v - v = -((2 : ℂ) • markedProj b s v) := by
    rw [markedOracle_apply]; abel
  rw [hrw, norm_neg, norm_smul]
  norm_num

/-- The state after `t` steps of the `k`-query algorithm `(ψ, U)` run **with** the oracle `O_s`:
`ψˢ_t = U_{t-1} O_s ⋯ U_0 O_s ψ` (each step applies `O_s` then the unitary `U`). -/
def markedRun (b : OrthonormalBasis (Fin N) ℂ H) (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ : H)
    (s : Finset (Fin N)) : ℕ → H
  | 0 => ψ
  | t + 1 => U t (markedOracle b s (markedRun b U ψ s t))

/-- The state after `t` steps of the `k`-query algorithm `(ψ, U)` run **without** the oracle:
`ψ_t = U_{t-1} ⋯ U_0 ψ` (the "reference" evolution the oracle perturbs). -/
def markedRunFree (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ : H) : ℕ → H
  | 0 => ψ
  | t + 1 => U t (markedRunFree U ψ t)

/-- The oracle-free run preserves norm (each `U t` is a linear isometry). -/
lemma markedRunFree_norm (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ : H) (t : ℕ) :
    ‖markedRunFree U ψ t‖ = ‖ψ‖ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [markedRunFree, LinearIsometryEquiv.norm_map, ih]

/-- The oracle run preserves norm (the oracle is a reflection and each `U t` a linear isometry). -/
lemma markedRun_norm (b : OrthonormalBasis (Fin N) ℂ H) (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ : H)
    (s : Finset (Fin N)) (t : ℕ) : ‖markedRun b U ψ s t‖ = ‖ψ‖ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [markedRun, LinearIsometryEquiv.norm_map, markedOracle_norm, ih]

/-- **The marked-weight identity.** For a unit vector `v` and `1 ≤ M`, the total marked projection
weight summed over all size-`M` worlds equals `C(N−1, M−1)`:
`∑_{|s| = M} ‖P_s v‖² = C(N−1, M−1)`.

Each item `y` lies in `C(N−1, M−1)` of the size-`M` subsets (`Finset.card_filter_mem_powersetCard`),
so the double sum `∑_{|s|=M} ∑_{y∈s} ‖⟪b y, v⟫‖²` telescopes to `C(N−1,M−1) · ∑_y ‖⟪b y, v⟫‖²`, and
Parseval gives `∑_y ‖⟪b y, v⟫‖² = ‖v‖² = 1`. -/
theorem sum_markedProj_normSq_eq (b : OrthonormalBasis (Fin N) ℂ H) {M : ℕ}
    (hM : 1 ≤ M) {v : H} (hv : ‖v‖ = 1) :
    ∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ‖markedProj b s v‖ ^ 2
      = ((N - 1).choose (M - 1) : ℝ) := by
  classical
  set g : Fin N → ℝ := fun y => ‖(inner ℂ (b y) v : ℂ)‖ ^ 2 with hg
  rw [Finset.sum_congr rfl (fun s _ => markedProj_norm_sq b s v)]
  -- double-count: `∑_{s} ∑_{y ∈ s} g y = ∑_y g y · #{s : y ∈ s}`
  have hswap : ∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ∑ y ∈ s, g y
      = ∑ y : Fin N, g y *
          ((((univ : Finset (Fin N)).powersetCard M).filter (fun s => y ∈ s)).card : ℝ) := by
    have e1 : ∀ s ∈ (univ : Finset (Fin N)).powersetCard M,
        ∑ y ∈ s, g y = ∑ y : Fin N, (if y ∈ s then g y else 0) := by
      intro s _; rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hswap]
  have hcount : ∀ y : Fin N,
      (((univ : Finset (Fin N)).powersetCard M).filter (fun s => y ∈ s)).card
        = (N - 1).choose (M - 1) := by
    intro y
    have := Finset.card_filter_powersetCard_subset ({y} : Finset (Fin N))
      (univ : Finset (Fin N)) M (Finset.subset_univ _) (by simpa using hM)
    simp only [Finset.singleton_subset_iff, Finset.card_singleton, Finset.card_univ,
      Fintype.card_fin] at this
    exact this
  simp_rw [hcount]
  rw [← Finset.sum_mul]
  have hpar : ∑ y : Fin N, g y = 1 := by
    rw [hg, OrthonormalBasis.sum_sq_norm_inner_right b v, hv]; norm_num
  rw [hpar, one_mul]

/-! ## Part (a): the deviation `Dₖ` and its sensitivity bound `Dₖ ≤ 4k²·C(N−1,M−1)` -/

/-- The **deviation** `Dₖ = ∑_{|s|=M} ‖ψˢ_k − ψ_k‖²` after `k` queries, summed over all size-`M`
marked worlds `s` (the `M`-solution analogue of N&C eq. 6.40): a measure of how far the oracle
`O_s` can perturb the algorithm's state, aggregated over every possible solution set. -/
def markedDeviation (b : OrthonormalBasis (Fin N) ℂ H) (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ : H)
    (M k : ℕ) : ℝ :=
  ∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ‖markedRun b U ψ s k - markedRunFree U ψ k‖ ^ 2

/-- Unrolling `Dₖ₊₁`: the outer unitary `U_k` is common to both runs and norm-preserving, so it
drops out and `Dₖ₊₁ = ∑_{|s|=M} ‖O_s ψˢ_k − ψ_k‖²` (the `M`-solution analogue of N&C eq. 6.41). -/
theorem markedDeviation_succ (b : OrthonormalBasis (Fin N) ℂ H) (U : ℕ → (H ≃ₗᵢ[ℂ] H)) (ψ : H)
    (M k : ℕ) :
    markedDeviation b U ψ M (k + 1)
      = ∑ s ∈ (univ : Finset (Fin N)).powersetCard M,
          ‖markedOracle b s (markedRun b U ψ s k) - markedRunFree U ψ k‖ ^ 2 := by
  simp only [markedDeviation, markedRun, markedRunFree]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← map_sub, LinearIsometryEquiv.norm_map]

/-- **The inductive step for `Dₖ ≤ 4k²·C(N−1,M−1)`** (the `M`-solution analogue of N&C eqs.
6.42–6.45). For a **unit** vector `p` (the oracle-free state `ψ_k`) and any family `a` of vectors
(the with-oracle states `ψˢ_k`), writing `S = ∑_{|s|=M} ‖a_s − p‖²`,
`∑_{|s|=M} ‖O_s a_s − p‖² ≤ S + 4·√S·√C(N−1,M−1) + 4·C(N−1,M−1)`.

Termwise `O_s a_s − p = O_s(a_s − p) + (O_s − I)p` with `‖O_s(a_s − p)‖ = ‖a_s − p‖`
(`markedOracle_norm`) and `‖(O_s − I)p‖ = 2‖P_s p‖` (`markedOracle_sub_self_norm`), so the triangle
inequality bounds each summand by `(‖a_s − p‖ + 2‖P_s p‖)²`. Summing, the cross term is bounded by
the sqrt-form finite Cauchy–Schwarz inequality (`Real.sum_mul_le_sqrt_mul_sqrt`) and the quadratic
term `∑_{|s|=M} ‖P_s p‖²` is `C(N−1,M−1)` exactly, by the marked-weight identity
`sum_markedProj_normSq_eq` (the multi-solution replacement for N&C's single-solution Bessel bound
`∑ₓ |⟪x,p⟫|² ≤ 1`). -/
theorem sum_norm_markedOracle_sub_sq_le (b : OrthonormalBasis (Fin N) ℂ H) {M : ℕ} (hM : 1 ≤ M)
    (a : Finset (Fin N) → H) {p : H} (hp : ‖p‖ = 1) :
    ∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ‖markedOracle b s (a s) - p‖ ^ 2
      ≤ (∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ‖a s - p‖ ^ 2)
        + 4 * Real.sqrt (∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ‖a s - p‖ ^ 2)
            * Real.sqrt ((N - 1).choose (M - 1) : ℝ)
        + 4 * ((N - 1).choose (M - 1) : ℝ) := by
  -- termwise triangle bound `‖O_s a_s − p‖² ≤ ‖a_s − p‖² + 4‖a_s − p‖‖P_s p‖ + 4‖P_s p‖²`
  have hpt : ∀ s ∈ (univ : Finset (Fin N)).powersetCard M,
      ‖markedOracle b s (a s) - p‖ ^ 2
        ≤ ‖a s - p‖ ^ 2 + 4 * (‖a s - p‖ * ‖markedProj b s p‖) + 4 * ‖markedProj b s p‖ ^ 2 := by
    intro s _
    have hsplit : markedOracle b s (a s) - p
        = markedOracle b s (a s - p) + (markedOracle b s p - p) := by
      rw [map_sub]; abel
    have hb : ‖markedOracle b s (a s - p)‖ = ‖a s - p‖ := markedOracle_norm b s _
    have hc : ‖markedOracle b s p - p‖ = 2 * ‖markedProj b s p‖ := markedOracle_sub_self_norm b s p
    have htri : ‖markedOracle b s (a s) - p‖ ≤ ‖a s - p‖ + 2 * ‖markedProj b s p‖ := by
      rw [hsplit]
      calc ‖markedOracle b s (a s - p) + (markedOracle b s p - p)‖
          ≤ ‖markedOracle b s (a s - p)‖ + ‖markedOracle b s p - p‖ := norm_add_le _ _
        _ = ‖a s - p‖ + 2 * ‖markedProj b s p‖ := by rw [hb, hc]
    calc ‖markedOracle b s (a s) - p‖ ^ 2
        ≤ (‖a s - p‖ + 2 * ‖markedProj b s p‖) ^ 2 := by gcongr
      _ = ‖a s - p‖ ^ 2 + 4 * (‖a s - p‖ * ‖markedProj b s p‖) + 4 * ‖markedProj b s p‖ ^ 2 := by
          ring
  -- sum the termwise bound
  have hsum : ∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ‖markedOracle b s (a s) - p‖ ^ 2
      ≤ (∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ‖a s - p‖ ^ 2)
        + 4 * (∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ‖a s - p‖ * ‖markedProj b s p‖)
        + 4 * ∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ‖markedProj b s p‖ ^ 2 := by
    calc ∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ‖markedOracle b s (a s) - p‖ ^ 2
        ≤ ∑ s ∈ (univ : Finset (Fin N)).powersetCard M,
            (‖a s - p‖ ^ 2 + 4 * (‖a s - p‖ * ‖markedProj b s p‖)
              + 4 * ‖markedProj b s p‖ ^ 2) := Finset.sum_le_sum hpt
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the marked-weight identity: `∑_s ‖P_s p‖² = C(N−1,M−1)`
  have hB : ∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ‖markedProj b s p‖ ^ 2
      = ((N - 1).choose (M - 1) : ℝ) := sum_markedProj_normSq_eq b hM hp
  -- Cauchy–Schwarz on the cross term, in sqrt form (Mathlib's `Real.sum_mul_le_sqrt_mul_sqrt`)
  have hcross_le :
      ∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ‖a s - p‖ * ‖markedProj b s p‖
        ≤ Real.sqrt (∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ‖a s - p‖ ^ 2)
            * Real.sqrt (∑ s ∈ (univ : Finset (Fin N)).powersetCard M, ‖markedProj b s p‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ (fun s => ‖a s - p‖) (fun s => ‖markedProj b s p‖)
  rw [hB] at hsum hcross_le
  nlinarith [hsum, hcross_le]

/-- **Nielsen & Chuang, Exercise 6.17 — part (a), the sensitivity bound `Dₖ ≤ 4k²·C(N−1,M−1)`.**
For a **unit** initial state `ψ` and `1 ≤ M`, the deviation caused by `k` oracle queries, summed
over all size-`M` marked worlds, grows at most quadratically in `k`:
`markedDeviation b U ψ M k ≤ 4·k²·C(N−1,M−1)`.

Proved by induction on `k`. `D₀ = 0`, and the step (`markedDeviation_succ` followed by
`sum_norm_markedOracle_sub_sq_le`, using `‖ψ_k‖ = 1` from `markedRunFree_norm`) gives
`Dₖ₊₁ ≤ Dₖ + 4·√Dₖ·√C(N−1,M−1) + 4·C(N−1,M−1)`. With `√Dₖ ≤ 2k·√C(N−1,M−1)` (the induction
hypothesis, square-rooted) this collapses to `Dₖ₊₁ ≤ 4(k+1)²·C(N−1,M−1)`. This is the `M`-solution
analogue of N&C's single-solution `Dₖ ≤ 4k²`, with the marked-weight constant `C(N−1,M−1)`
replacing the single-solution `1`; it is the upper half of the sandwich that forces
`k ≥ Ω(√(N/M))`. -/
theorem markedDeviation_le (b : OrthonormalBasis (Fin N) ℂ H) (U : ℕ → (H ≃ₗᵢ[ℂ] H)) {ψ : H}
    (hψ : ‖ψ‖ = 1) {M : ℕ} (hM : 1 ≤ M) (k : ℕ) :
    markedDeviation b U ψ M k ≤ 4 * (k : ℝ) ^ 2 * ((N - 1).choose (M - 1) : ℝ) := by
  set B := ((N - 1).choose (M - 1) : ℝ) with hBdef
  clear_value B
  have hBnonneg : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
  induction k with
  | zero => simp [markedDeviation, markedRun, markedRunFree]
  | succ j ih =>
    have hns1 : ‖markedRunFree U ψ j‖ = 1 := (markedRunFree_norm U ψ j).trans hψ
    have hstep : markedDeviation b U ψ M (j + 1)
        ≤ markedDeviation b U ψ M j
          + 4 * Real.sqrt (markedDeviation b U ψ M j) * Real.sqrt B + 4 * B := by
      rw [markedDeviation_succ]
      have h := sum_norm_markedOracle_sub_sq_le b hM (fun s => markedRun b U ψ s j) hns1
      rw [← hBdef] at h
      simpa only [markedDeviation] using h
    have h4 : markedDeviation b U ψ M j ≤ (2 * (j : ℝ) * Real.sqrt B) ^ 2 := by
      have hexp : (2 * (j : ℝ) * Real.sqrt B) ^ 2 = 4 * (j : ℝ) ^ 2 * B := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hBnonneg]; ring
      rw [hexp]; exact ih
    have hsqrt : Real.sqrt (markedDeviation b U ψ M j) ≤ 2 * (j : ℝ) * Real.sqrt B :=
      calc Real.sqrt (markedDeviation b U ψ M j)
          ≤ Real.sqrt ((2 * (j : ℝ) * Real.sqrt B) ^ 2) := Real.sqrt_le_sqrt h4
        _ = 2 * (j : ℝ) * Real.sqrt B := Real.sqrt_sq (by positivity)
    push_cast
    nlinarith [hstep, ih, hsqrt, Real.sqrt_nonneg (markedDeviation b U ψ M j),
      Real.sqrt_nonneg B, Real.sq_sqrt hBnonneg, hBnonneg]

/-! ## Part (b): the success lower bound `Dₖ ≥ (√(C(N,M)/2) − √C(N−1,M−1))²`, and the assembly -/

/-- **The marked projection is a contraction:** `‖P_s v‖ ≤ ‖v‖`. Since
`‖P_s v‖² = ∑_{y∈s} ‖⟪b y, v⟫‖²` is a *partial* Parseval sum over the marked items `s ⊆ univ`, it is
at most the full Parseval sum `∑_y ‖⟪b y, v⟫‖² = ‖v‖²` (`OrthonormalBasis.sum_sq_norm_inner_right`);
taking square roots gives the claim. This is the geometric fact — `P_s` never lengthens a vector —
that drives the reverse-triangle step of part (b). -/
lemma markedProj_norm_le (b : OrthonormalBasis (Fin N) ℂ H) (s : Finset (Fin N)) (v : H) :
    ‖markedProj b s v‖ ≤ ‖v‖ := by
  have hsq : ‖markedProj b s v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [markedProj_norm_sq]
    calc ∑ y ∈ s, ‖(inner ℂ (b y) v : ℂ)‖ ^ 2
        ≤ ∑ y : Fin N, ‖(inner ℂ (b y) v : ℂ)‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _ => by positivity)
      _ = ‖v‖ ^ 2 := OrthonormalBasis.sum_sq_norm_inner_right b v
  calc ‖markedProj b s v‖
      = Real.sqrt (‖markedProj b s v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖v‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖v‖ := Real.sqrt_sq (norm_nonneg _)

/-- The `ℓ²`-triangle inequality over a finite index set: `√(∑ u²) ≤ √(∑ (u−w)²) + √(∑ w²)`.
A `Real.sqrt`-form corollary of the Minkowski inequality `Real.Lp_add_le` at `p = 2`, applied to
`w` and `u − w` (whose sum is `u`). -/
theorem sqrt_sum_sq_le_sqrt_sum_sub_sq_add {ι : Type*} (s : Finset ι) (u w : ι → ℝ) :
    Real.sqrt (∑ i ∈ s, u i ^ 2)
      ≤ Real.sqrt (∑ i ∈ s, (u i - w i) ^ 2) + Real.sqrt (∑ i ∈ s, w i ^ 2) := by
  have hp : (1 : ℝ) ≤ 2 := by norm_num
  have h := Real.Lp_add_le s w (fun i => u i - w i) hp
  have heq2 : ∀ i, w i + (u i - w i) = u i := fun i => by ring
  simp_rw [heq2, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] at h
  linarith [h]

/-- **Nielsen & Chuang, Exercise 6.17 — part (b), the success lower bound.** If the `k`-query
algorithm *succeeds* — for every size-`M` marked world `s`, measuring the final state `ψˢ_k` yields
a solution with probability at least `1/2`, i.e. `‖P_s ψˢ_k‖² ≥ 1/2` — then the deviation is bounded
below:
`√(C(N,M)/2) ≤ √Dₖ + √C(N−1,M−1)`.

This is the `M`-solution analogue of N&C's `Dₖ ≥ (√Fₖ − √Eₖ)²` (eqs. 6.48–6.51), reorganised to
avoid a per-world target vector. Its proof is purely the ℓ²-triangle inequality over the `C(N,M)`
worlds (`Real.sqrt_sum_sq_le_sqrt_sum_sub_sq_add`, from `ToMathlib/`) applied to
`u_s = ‖P_s ψˢ_k‖` and `w_s = ‖P_s ψ_k‖`:
since `P_s` is a contraction (`markedProj_norm_le`), the reverse triangle inequality gives
`|u_s − w_s| ≤ ‖ψˢ_k − ψ_k‖`, so `∑_s (u_s − w_s)² ≤ Dₖ`; the success hypothesis gives
`∑_s u_s² ≥ C(N,M)/2`; and the marked-weight identity `sum_markedProj_normSq_eq` (at `‖ψ_k‖ = 1`)
gives `∑_s w_s² = C(N−1,M−1)` exactly. -/
theorem markedDeviation_ge (b : OrthonormalBasis (Fin N) ℂ H) (U : ℕ → (H ≃ₗᵢ[ℂ] H)) {ψ : H}
    (hψ : ‖ψ‖ = 1) {M : ℕ} (hM : 1 ≤ M) (k : ℕ)
    (hsucc : ∀ s ∈ (univ : Finset (Fin N)).powersetCard M,
        (1 : ℝ) / 2 ≤ ‖markedProj b s (markedRun b U ψ s k)‖ ^ 2) :
    Real.sqrt ((N.choose M : ℝ) / 2)
      ≤ Real.sqrt (markedDeviation b U ψ M k) + Real.sqrt ((N - 1).choose (M - 1) : ℝ) := by
  classical
  -- the ℓ²-triangle bound applied to the marked projections of the with-/without-oracle runs
  have hmink := sqrt_sum_sq_le_sqrt_sum_sub_sq_add ((univ : Finset (Fin N)).powersetCard M)
    (fun s => ‖markedProj b s (markedRun b U ψ s k)‖)
    (fun s => ‖markedProj b s (markedRunFree U ψ k)‖)
  -- (1) marked-weight identity `∑_s ‖P_s ψ_k‖² = C(N−1,M−1)` (the no-oracle run is a unit vector)
  have hns1 : ‖markedRunFree U ψ k‖ = 1 := (markedRunFree_norm U ψ k).trans hψ
  have hQ : ∑ s ∈ (univ : Finset (Fin N)).powersetCard M,
      ‖markedProj b s (markedRunFree U ψ k)‖ ^ 2 = ((N - 1).choose (M - 1) : ℝ) :=
    sum_markedProj_normSq_eq b hM hns1
  -- (2) contraction + reverse triangle, termwise: `∑_s (‖P_s ψˢ_k‖ − ‖P_s ψ_k‖)² ≤ Dₖ`
  have hPD : ∑ s ∈ (univ : Finset (Fin N)).powersetCard M,
      (‖markedProj b s (markedRun b U ψ s k)‖ - ‖markedProj b s (markedRunFree U ψ k)‖) ^ 2
      ≤ markedDeviation b U ψ M k := by
    simp only [markedDeviation]
    refine Finset.sum_le_sum fun s _ => ?_
    have h1 : |‖markedProj b s (markedRun b U ψ s k)‖ - ‖markedProj b s (markedRunFree U ψ k)‖|
        ≤ ‖markedProj b s (markedRun b U ψ s k) - markedProj b s (markedRunFree U ψ k)‖ :=
      abs_norm_sub_norm_le _ _
    have h2 : ‖markedProj b s (markedRun b U ψ s k) - markedProj b s (markedRunFree U ψ k)‖
        ≤ ‖markedRun b U ψ s k - markedRunFree U ψ k‖ := by
      rw [← map_sub]; exact markedProj_norm_le b s _
    calc (‖markedProj b s (markedRun b U ψ s k)‖ - ‖markedProj b s (markedRunFree U ψ k)‖) ^ 2
        = |‖markedProj b s (markedRun b U ψ s k)‖
            - ‖markedProj b s (markedRunFree U ψ k)‖| ^ 2 := (sq_abs _).symm
      _ ≤ ‖markedRun b U ψ s k - markedRunFree U ψ k‖ ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
  -- (3) the success hypothesis: `∑_s ‖P_s ψˢ_k‖² ≥ C(N,M)/2`
  have hSucc : (N.choose M : ℝ) / 2
      ≤ ∑ s ∈ (univ : Finset (Fin N)).powersetCard M,
          ‖markedProj b s (markedRun b U ψ s k)‖ ^ 2 := by
    have hcard : (((univ : Finset (Fin N)).powersetCard M).card : ℝ) = (N.choose M : ℝ) := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    calc (N.choose M : ℝ) / 2
        = ∑ _s ∈ (univ : Finset (Fin N)).powersetCard M, (1 : ℝ) / 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
      _ ≤ ∑ s ∈ (univ : Finset (Fin N)).powersetCard M,
            ‖markedProj b s (markedRun b U ψ s k)‖ ^ 2 := Finset.sum_le_sum hsucc
  -- combine: `√(T/2) ≤ √(∑ u²) ≤ √(∑ (u−w)²) + √(∑ w²) ≤ √Dₖ + √C(N−1,M−1)`
  calc Real.sqrt ((N.choose M : ℝ) / 2)
      ≤ Real.sqrt (∑ s ∈ (univ : Finset (Fin N)).powersetCard M,
          ‖markedProj b s (markedRun b U ψ s k)‖ ^ 2) := Real.sqrt_le_sqrt hSucc
    _ ≤ Real.sqrt (∑ s ∈ (univ : Finset (Fin N)).powersetCard M,
          (‖markedProj b s (markedRun b U ψ s k)‖ - ‖markedProj b s (markedRunFree U ψ k)‖) ^ 2)
        + Real.sqrt (∑ s ∈ (univ : Finset (Fin N)).powersetCard M,
          ‖markedProj b s (markedRunFree U ψ k)‖ ^ 2) := hmink
    _ ≤ Real.sqrt (markedDeviation b U ψ M k) + Real.sqrt ((N - 1).choose (M - 1) : ℝ) := by
        rw [hQ]; linarith [Real.sqrt_le_sqrt hPD]

/-- **Nielsen & Chuang, Exercise 6.17 — `Ω(√(N/M))` oracle applications are required.** For a
`k`-query search algorithm `(ψ, U)` on a search register with orthonormal basis `b`, unit initial
state `ψ`, `1 ≤ M ≤ N` solutions, whose success is guaranteed for *every* size-`M` marked world
`s` — measuring the final state `ψˢ_k` yields a solution with probability at least `1/2`,
`‖P_s ψˢ_k‖² ≥ 1/2` — the number of oracle queries satisfies
`k ≥ ½·(√(N/2M) − 1) = Ω(√(N/M))`.

This is the multiple-solution optimality bound: `M` solutions still need `Ω(√(N/M))` queries, a
quadratic improvement over the classical `Θ(N/M)`. It combines the two halves of the sandwich on
the deviation `Dₖ = ∑_{|s|=M} ‖ψˢ_k − ψ_k‖²`:

* part (a) `markedDeviation_le`, `Dₖ ≤ 4k²·C(N−1,M−1)`, hence `√Dₖ ≤ 2k·√C(N−1,M−1)`;
* part (b) `markedDeviation_ge`, `√(C(N,M)/2) ≤ √Dₖ + √C(N−1,M−1)`.

Chaining gives `√(C(N,M)/2) ≤ (2k+1)·√C(N−1,M−1)`, so `C(N,M)/2 ≤ (2k+1)²·C(N−1,M−1)`. The
combinatorial identity `N·C(N−1,M−1) = M·C(N,M)` (`Nat.add_one_mul_choose_eq`) turns this into
`N/(2M) ≤ (2k+1)²` (cancelling `C(N−1,M−1) > 0`, which needs `M ≤ N`), whence
`√(N/2M) ≤ 2k+1` and the stated bound. The `1/2` success threshold and the `Ω(√(N/M))` order match
N&C's §6.6 argument (Exercise 6.17 asks only for the order, not a specific constant). -/
theorem search_lower_bound_multi_solution (b : OrthonormalBasis (Fin N) ℂ H)
    (U : ℕ → (H ≃ₗᵢ[ℂ] H)) {ψ : H} (hψ : ‖ψ‖ = 1) {M : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) (k : ℕ)
    (hsucc : ∀ s ∈ (univ : Finset (Fin N)).powersetCard M,
        (1 : ℝ) / 2 ≤ ‖markedProj b s (markedRun b U ψ s k)‖ ^ 2) :
    (1 / 2 : ℝ) * (Real.sqrt ((N : ℝ) / (2 * M)) - 1) ≤ (k : ℝ) := by
  have hN1 : 1 ≤ N := le_trans hM hMN
  have hMpos : 0 < M := hM
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  set a : ℝ := ((N - 1).choose (M - 1) : ℝ) with hadef
  -- `a = C(N−1,M−1) > 0` since `M ≤ N`
  have hapos : (0 : ℝ) < a := by
    rw [hadef]; exact_mod_cast Nat.choose_pos (Nat.sub_le_sub_right hMN 1)
  -- part (b), and part (a) square-rooted to `√Dₖ ≤ 2k·√a`
  have hb := markedDeviation_ge b U hψ hM k hsucc
  rw [← hadef] at hb
  have ha := markedDeviation_le b U hψ hM k
  rw [← hadef] at ha
  have hsqrtD : Real.sqrt (markedDeviation b U ψ M k) ≤ 2 * (k : ℝ) * Real.sqrt a := by
    have hrw : 4 * (k : ℝ) ^ 2 * a = (2 * (k : ℝ) * Real.sqrt a) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hapos.le]; ring
    calc Real.sqrt (markedDeviation b U ψ M k)
        ≤ Real.sqrt (4 * (k : ℝ) ^ 2 * a) := Real.sqrt_le_sqrt ha
      _ = 2 * (k : ℝ) * Real.sqrt a := by rw [hrw, Real.sqrt_sq (by positivity)]
  -- chain: `√(C(N,M)/2) ≤ (2k+1)·√a`
  have hcomb : Real.sqrt ((N.choose M : ℝ) / 2) ≤ (2 * (k : ℝ) + 1) * Real.sqrt a :=
    calc Real.sqrt ((N.choose M : ℝ) / 2)
        ≤ Real.sqrt (markedDeviation b U ψ M k) + Real.sqrt a := hb
      _ ≤ 2 * (k : ℝ) * Real.sqrt a + Real.sqrt a := by linarith [hsqrtD]
      _ = (2 * (k : ℝ) + 1) * Real.sqrt a := by ring
  -- square: `C(N,M)/2 ≤ (2k+1)²·a`
  have hTsq : (N.choose M : ℝ) / 2 ≤ (2 * (k : ℝ) + 1) ^ 2 * a := by
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hcomb 2
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (N.choose M : ℝ) / 2), mul_pow,
      Real.sq_sqrt hapos.le] at hsq
    exact hsq
  -- combinatorial identity `N·C(N−1,M−1) = C(N,M)·M`, cast to ℝ
  have hkeyNat : N * (N - 1).choose (M - 1) = N.choose M * M := by
    have h := Nat.add_one_mul_choose_eq (N - 1) (M - 1)
    simpa only [Nat.sub_add_cancel hN1, Nat.sub_add_cancel hM] using h
  have hkey : (N : ℝ) * a = (N.choose M : ℝ) * (M : ℝ) := by
    rw [hadef]; exact_mod_cast hkeyNat
  -- `T ≤ 2·(2k+1)²·a`, multiply by `M`, use `N·a = T·M`, cancel `a`
  have hT2 : (N.choose M : ℝ) ≤ 2 * (2 * (k : ℝ) + 1) ^ 2 * a := by linarith [hTsq]
  have hcancel : (N : ℝ) * a ≤ (2 * (2 * (k : ℝ) + 1) ^ 2 * M) * a :=
    calc (N : ℝ) * a = (N.choose M : ℝ) * (M : ℝ) := hkey
      _ ≤ (2 * (2 * (k : ℝ) + 1) ^ 2 * a) * (M : ℝ) := mul_le_mul_of_nonneg_right hT2 hM0.le
      _ = (2 * (2 * (k : ℝ) + 1) ^ 2 * M) * a := by ring
  have hNle : (N : ℝ) ≤ 2 * (2 * (k : ℝ) + 1) ^ 2 * M := le_of_mul_le_mul_right hcancel hapos
  -- `N/(2M) ≤ (2k+1)²`, so `√(N/2M) ≤ 2k+1`
  have hfrac : (N : ℝ) / (2 * M) ≤ (2 * (k : ℝ) + 1) ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (M : ℝ))]
    nlinarith [hNle]
  have hsqrtfrac : Real.sqrt ((N : ℝ) / (2 * M)) ≤ 2 * (k : ℝ) + 1 :=
    calc Real.sqrt ((N : ℝ) / (2 * M))
        ≤ Real.sqrt ((2 * (k : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt hfrac
      _ = 2 * (k : ℝ) + 1 := Real.sqrt_sq (by positivity)
  linarith [hsqrtfrac]

end

end AxQM.Concrete
