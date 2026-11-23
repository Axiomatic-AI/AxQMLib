/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.EntanglementFidelity
public import ToMathlib.Analysis.InnerProductSpace.RankOneTrace

/-! # The entanglement infidelity as a sum of operation-element variances

For a trace-preserving quantum operation with operation elements `E : ι → (H →L[ℂ] H)` (the Kraus
operators, `E(ρ) = Σᵢ Eᵢ ρ Eᵢ†`, `Σᵢ Eᵢ† Eᵢ = 1`), the entanglement fidelity is
`F(ρ, E) = Σᵢ |tr(ρ Eᵢ)|²` (`ContinuousLinearMap.entanglementFidelity`; Nielsen–Chuang, *Quantum
Computation and Quantum Information*, Eq. (9.135)). This file records the exact **variance
decomposition of the infidelity** `1 − F(ρ, E)`, the reduction step at the heart of Nielsen &
Chuang's *Problem 9.3* (fact (5): if `⟨ψ|E(|ψ⟩⟨ψ|)|ψ⟩ ≥ 1 − η` on the support of `ρ` then
`F(ρ, E) ≥ 1 − 3η/2`).

Writing `⟨A⟩_ρ = tr(ρ A)`, the **operator variance** of an operation element `E` in the state `ρ`
is `Var_ρ(E) = ⟨E† E⟩_ρ − |⟨E⟩_ρ|²` (`ContinuousLinearMap.opVariance`; a Cauchy–Schwarz-nonnegative
quantity). The two identities below say that the entanglement infidelity is the *total* operator
variance of the Kraus family, in the two forms Problem 9.3 needs — the mixed-state form and the
pure-state form:

* `ContinuousLinearMap.one_sub_entanglementFidelity_eq_sum_opVariance` — for a trace-preserving
  family (`Σᵢ Eᵢ† Eᵢ = 1`) and a unit-trace `ρ`,
  `1 − F(ρ, E) = Σᵢ Var_ρ(Eᵢ)`. Purely the linearity of the trace and the completeness relation;
  no positivity is used, so it holds for any unit-trace `ρ`.
* `ContinuousLinearMap.re_inner_krausSumₗ_rankOne_self` — the **physical reading** of the pure-state
  hypothesis: `⟨ψ| E(|ψ⟩⟨ψ|) |ψ⟩ = Σᵢ |⟨ψ, Eᵢ ψ⟩|²`, so the fidelity of the pure input `|ψ⟩⟨ψ|` is
  computed from the operation elements exactly as Eq. (9.135) prescribes.
* `ContinuousLinearMap.one_sub_sum_normSq_inner_eq_sum` — the pure-state form of the decomposition:
  for a unit vector `ψ` and a trace-preserving family,
  `1 − Σᵢ |⟨ψ, Eᵢ ψ⟩|² = Σᵢ (‖Eᵢ ψ‖² − |⟨ψ, Eᵢ ψ⟩|²)`, each summand `≥ 0`
  (`ContinuousLinearMap.normSq_inner_le_normSq_apply`). This is `Σᵢ Var_{|ψ⟩⟨ψ|}(Eᵢ)`, so combined
  with the physical reading it says `1 − ⟨ψ|E(|ψ⟩⟨ψ|)|ψ⟩ = Σᵢ Var_{|ψ⟩⟨ψ|}(Eᵢ)`.

This file also records the elementary combinatorial bound behind the *tight* `3η/2` constant of
fact (5), `weighted_offDiag_sum_le_half`: for a probability vector `p` and a nonnegative array `M`
whose every column has off-diagonal total `≤ η`, the doubly `p`-weighted off-diagonal sum is
`≤ η / 2`. Instantiated at `M a b = Σᵢ ‖⟨a, Eᵢ b⟩‖²` over an eigenbasis of `ρ`, this bounds the
off-diagonal "coherence" term of the entanglement infidelity; the `η / 2` (rather than `η`) is what
separates the true `F(ρ, E) ≥ 1 − 3η/2` from the weaker `1 − 2η`.

Finally, this file assembles the two **eigenbasis ingredients** of fact (5) — the pieces that a
state `ρ = Σₐ pₐ |eₐ⟩⟨eₐ|` in a spectral eigenbasis contributes to the entanglement infidelity:

* `ContinuousLinearMap.entanglementFidelity_sum_rankOne` — the *diagonal* ingredient:
  `F(ρ, E) = Σⱼ |Σₐ pₐ ⟨eₐ, Eⱼ eₐ⟩|²`, i.e. the entanglement fidelity reads off the diagonal matrix
  elements `⟨eₐ, Eⱼ eₐ⟩` (linearity of the trace + `trace_rankOne_self_comp`).
* `ContinuousLinearMap.offDiagCoherenceSum` and `ContinuousLinearMap.offDiagCoherenceSum_le` — the
  *off-diagonal* ingredient: the coherence sum `S_off = Σ_{a≠b} pₐ p_b Σⱼ |⟨eₐ, Eⱼ e_b⟩|²`, and the
  bound `S_off ≤ η / 2` obtained by feeding the per-column budget `sum_offDiag_normSq_inner_le`
  (Parseval + completeness + the pure-state deficit at each eigenvector) into
  `weighted_offDiag_sum_le_half`.

Combined with the phase-diagonal-twirl reduction `1 − F(ρ, E) ≤ η + S_off` (a subsequent step),
these give fact (5): `F(ρ, E) ≥ 1 − η − S_off ≥ 1 − 3η/2`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §9.3 (Eq. (9.135); Problem 9.3, fact (5)).
-/

open scoped InnerProductSpace ComplexConjugate

open InnerProductSpace

@[expose] public section

/-- **Diagonal of a self-adjoint idempotent operator (an orthogonal projector).** For a
self-adjoint idempotent continuous linear operator `P` — a star projection — and any vector `x`, the
diagonal inner product `⟪x, P x⟫` is the squared norm of the projection, a nonnegative real:
`⟪x, P x⟫ = ‖P x‖²`. Indeed `⟪x, P x⟫ = ⟪x, P (P x)⟫ = ⟪P x, P x⟫ = ‖P x‖²`, using idempotence
(`P ∘ P = P`) and self-adjointness (`P† = P`).

A general Hilbert-space fact reused by the projection–reset compression channel's fidelity bound
(Nielsen & Chuang Exercise 12.8) and the Grover marked-projection lower bound. -/
theorem inner_self_of_isSelfAdjoint_of_isIdempotent {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {P : E →L[𝕜] E}
    (hsa : IsSelfAdjoint P) (hidem : IsIdempotentElem P) (x : E) :
    inner 𝕜 x (P x) = ((‖P x‖ ^ 2 : ℝ) : 𝕜) := by
  have hPP : P (P x) = P x := by
    have := DFunLike.congr_fun hidem x
    simpa [mul_apply_eq_comp] using this
  have h := ContinuousLinearMap.adjoint_inner_right P x (P x)
  rw [hsa.adjoint_eq, hPP] at h
  rw [h, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **Weighted off-diagonal sum bound.** Let `p` be a probability vector on a finite type
(`0 ≤ p`, `∑ p = 1`) and `M ≥ 0` a nonnegative "coherence" array whose every column has bounded
off-diagonal total, `∑_{a ≠ b} M a b ≤ η`. Then the doubly `p`-weighted off-diagonal sum obeys
`∑_{a ≠ b} p a * p b * M a b ≤ η / 2`.

This is the combinatorial heart of the tight `3η/2` constant in Nielsen & Chuang's *Problem 9.3*
(fact (5)): taking `M a b = ∑ᵢ ‖⟨a, Eᵢ b⟩‖²` over an eigenbasis of `ρ = ∑ₐ pₐ |a⟩⟨a|`, each column
budget is the pure-state variance deficit `∑ᵢ Var_{|b⟩}(Eᵢ) ≤ η` at the eigenvector `|b⟩`, and the
weighted off-diagonal sum is exactly the off-diagonal "coherence" term of the entanglement
infidelity. The constant `η / 2` — not `η`, and decisive for reaching `1 − 3η/2` rather than the
weaker `1 − 2η` — is the extremal value of `2 m (1 - m)` at `m = maxₐ pₐ`, attained by the balanced
two-point distribution: bounding each column by its largest weight and treating the maximizing
index separately gives `∑_b p_b · maxₐ_{≠b} pₐ ≤ 2 m (1 - m) ≤ 1/2`. -/
theorem weighted_offDiag_sum_le_half {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    {M : ι → ι → ℝ} (hM : ∀ a b, 0 ≤ M a b) {η : ℝ}
    (hcol : ∀ b, ∑ a ∈ Finset.univ.erase b, M a b ≤ η) :
    ∑ b, ∑ a ∈ Finset.univ.erase b, p a * p b * M a b ≤ η / 2 := by
  classical
  have hNE : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hp1
    exact absurd hp1 (by norm_num)
  obtain ⟨as, hmax⟩ := Finite.exists_max p
  set m := p as with hm_def
  have hm0 : 0 ≤ m := hp as
  have hm1 : m ≤ 1 := by
    calc m = p as := hm_def
      _ ≤ ∑ i, p i := Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ as)
      _ = 1 := hp1
  have hη0 : 0 ≤ η := le_trans (Finset.sum_nonneg (fun a _ => hM a as)) (hcol as)
  have hp_erase : ∀ a ∈ Finset.univ.erase as, p a ≤ 1 - m := by
    intro a ha
    calc p a ≤ ∑ i ∈ Finset.univ.erase as, p i := Finset.single_le_sum (fun i _ => hp i) ha
      _ = 1 - m := by rw [Finset.sum_erase_eq_sub (Finset.mem_univ as), hp1, hm_def]
  have hrw : ∀ b, ∑ a ∈ Finset.univ.erase b, p a * p b * M a b
      = p b * ∑ a ∈ Finset.univ.erase b, p a * M a b := by
    intro b; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
  -- Each column's `p`-weighted sum is bounded by any uniform bound `c` on its weights, times `η`:
  -- pointwise `p a ≤ c`, then `mul_sum`, then the column budget `hcol`. The asymmetric bounds
  -- `c = 1 - m` (at `as`) and `c = m` (elsewhere) are what deliver `2 m (1 - m) ≤ 1/2` below.
  have key : ∀ (b : ι) (c : ℝ), 0 ≤ c → (∀ a ∈ Finset.univ.erase b, p a ≤ c) →
      ∑ a ∈ Finset.univ.erase b, p a * M a b ≤ c * η := by
    intro b c hc0 hc
    calc ∑ a ∈ Finset.univ.erase b, p a * M a b
        ≤ ∑ a ∈ Finset.univ.erase b, c * M a b :=
          Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_right (hc a ha) (hM a b))
      _ = c * ∑ a ∈ Finset.univ.erase b, M a b := by rw [Finset.mul_sum]
      _ ≤ c * η := mul_le_mul_of_nonneg_left (hcol b) hc0
  have h_inner_as := key as (1 - m) (by linarith) hp_erase
  have h_inner_gen : ∀ b, (∑ a ∈ Finset.univ.erase b, p a * M a b) ≤ m * η :=
    fun b => key b m hm0 (fun a _ => hmax a)
  have hsum_erase : ∑ b ∈ Finset.univ.erase as, p b = 1 - m := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ as), hp1, hm_def]
  have hS : ∑ b, ∑ a ∈ Finset.univ.erase b, p a * p b * M a b
      = p as * (∑ a ∈ Finset.univ.erase as, p a * M a as)
        + ∑ b ∈ Finset.univ.erase as, p b * (∑ a ∈ Finset.univ.erase b, p a * M a b) := by
    simp_rw [hrw]
    exact (Finset.add_sum_erase Finset.univ
      (fun b => p b * ∑ a ∈ Finset.univ.erase b, p a * M a b) (Finset.mem_univ as)).symm
  rw [hS]
  have hb1 : p as * (∑ a ∈ Finset.univ.erase as, p a * M a as) ≤ m * ((1 - m) * η) := by
    rw [hm_def]; exact mul_le_mul_of_nonneg_left h_inner_as (hp as)
  have hb2 : ∑ b ∈ Finset.univ.erase as, p b * (∑ a ∈ Finset.univ.erase b, p a * M a b)
      ≤ (1 - m) * (m * η) := by
    calc ∑ b ∈ Finset.univ.erase as, p b * (∑ a ∈ Finset.univ.erase b, p a * M a b)
        ≤ ∑ b ∈ Finset.univ.erase as, p b * (m * η) :=
          Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (h_inner_gen b) (hp b))
      _ = (1 - m) * (m * η) := by rw [← Finset.sum_mul, hsum_erase]
  nlinarith [hb1, hb2, mul_nonneg hη0 (sq_nonneg (2 * m - 1))]

namespace ContinuousLinearMap

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

/-- The **operator variance** `Var_ρ(E) = tr(ρ E† E) − |tr(ρ E)|²` of an operator `E` in a state
`ρ` — the second moment of `E` minus its squared mean, both taken in the (generally mixed) state
`ρ`. For a density operator `ρ` this is `≥ 0` by the Cauchy–Schwarz inequality for the
`ρ`-weighted form `⟨X, Y⟩_ρ = tr(ρ X† Y)`. The entanglement infidelity `1 − F(ρ, E)` is the total
operator variance of the Kraus family (`one_sub_entanglementFidelity_eq_sum_opVariance`). -/
noncomputable def opVariance (ρ E : H →L[ℂ] H) : ℝ :=
  RCLike.re (LinearMap.trace ℂ H ((ρ * (adjoint E * E) : H →L[ℂ] H) : H →ₗ[ℂ] H))
    - ‖LinearMap.trace ℂ H ((ρ * E : H →L[ℂ] H) : H →ₗ[ℂ] H)‖ ^ 2

omit [FiniteDimensional ℂ H] in
/-- **The entanglement infidelity is the total operator variance of the Kraus family.** For a
trace-preserving family of operation elements (`Σᵢ Eᵢ† Eᵢ = 1`) and any unit-trace operator `ρ`,
`1 − F(ρ, E) = Σᵢ Var_ρ(Eᵢ)` (Nielsen & Chuang, Eq. (9.135); the reduction underlying Problem 9.3).

The proof uses only linearity of the trace and the completeness relation: `Σᵢ tr(ρ Eᵢ† Eᵢ)
= tr(ρ · Σᵢ Eᵢ† Eᵢ) = tr ρ = 1`, so `Σᵢ re tr(ρ Eᵢ† Eᵢ) = 1`, and `F(ρ, E) = Σᵢ |tr(ρ Eᵢ)|²`
by definition. No positivity of `ρ` is needed. -/
theorem one_sub_entanglementFidelity_eq_sum_opVariance
    (ρ : H →L[ℂ] H) (E : ι → H →L[ℂ] H)
    (hE : ∑ i, adjoint (E i) * E i = 1)
    (htr : LinearMap.trace ℂ H (ρ : H →ₗ[ℂ] H) = 1) :
    1 - entanglementFidelity ρ E = ∑ i, opVariance ρ (E i) := by
  -- `Σᵢ tr(ρ Eᵢ† Eᵢ) = tr(ρ · Σᵢ Eᵢ† Eᵢ) = tr(ρ · 1) = tr ρ = 1`.
  have hq : ∑ i, LinearMap.trace ℂ H
      ((ρ * (adjoint (E i) * E i) : H →L[ℂ] H) : H →ₗ[ℂ] H) = 1 := by
    rw [← htr, ← map_sum, ← ContinuousLinearMap.toLinearMap_sum, ← Finset.mul_sum, hE, mul_one]
  -- take real parts: `Σᵢ re tr(ρ Eᵢ† Eᵢ) = re 1 = 1`.
  have hre : ∑ i, RCLike.re (LinearMap.trace ℂ H
      ((ρ * (adjoint (E i) * E i) : H →L[ℂ] H) : H →ₗ[ℂ] H)) = 1 := by
    have h := congrArg RCLike.re hq
    rwa [map_sum, RCLike.one_re] at h
  simp only [entanglementFidelity, opVariance]
  rw [Finset.sum_sub_distrib, hre]

omit [FiniteDimensional ℂ H] in
/-- **The physical reading of the pure-state fidelity.** For a pure input `|ψ⟩⟨ψ|` and any family of
operation elements `E`, the "diagonal matrix element" of the output equals the sum of squared
overlaps of the operation elements:
`⟨ψ| E(|ψ⟩⟨ψ|) |ψ⟩ = Σᵢ |⟨ψ, Eᵢ ψ⟩|²`, here recorded as the complex equation
`⟨ψ, (krausSumₗ E |ψ⟩⟨ψ|) ψ⟩ = ↑(Σᵢ ‖⟨ψ, Eᵢ ψ⟩‖²)` (Nielsen & Chuang, Eq. (9.135) for the pure
input `|ψ⟩⟨ψ|`, whose only purification is itself; the value is real, as the coercion makes clear).
Each summand `⟨ψ, Eᵢ (|ψ⟩⟨ψ| Eᵢ† ψ)⟩ = ⟨E_i ψ, ψ⟩ ⟨ψ, Eᵢ ψ⟩ = |⟨ψ, Eᵢ ψ⟩|²`. -/
theorem inner_krausSumₗ_rankOne_self (ψ : H) (E : ι → H →L[ℂ] H) :
    inner ℂ ψ ((krausSumₗ E (rankOne ℂ ψ ψ)) ψ) = ((∑ i, ‖inner ℂ ψ (E i ψ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [krausSumₗ_apply]
  simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply, inner_sum,
    rankOne_apply, ContinuousLinearMap.map_smul, inner_smul_right, adjoint_inner_right]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  -- summand: `⟪E i ψ, ψ⟫ * ⟪ψ, E i ψ⟫ = (↑‖⟪ψ, E i ψ⟫‖)²`
  rw [← inner_conj_symm (E i ψ) ψ, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  ring

omit [FiniteDimensional ℂ H] in
/-- The **pure-state fidelity is real and equals the sum of squared overlaps** — the `re` form of
`inner_krausSumₗ_rankOne_self`: `re ⟨ψ| E(|ψ⟩⟨ψ|) |ψ⟩ = Σᵢ |⟨ψ, Eᵢ ψ⟩|²`. -/
theorem re_inner_krausSumₗ_rankOne_self (ψ : H) (E : ι → H →L[ℂ] H) :
    RCLike.re (inner ℂ ψ ((krausSumₗ E (rankOne ℂ ψ ψ)) ψ)) = ∑ i, ‖inner ℂ ψ (E i ψ)‖ ^ 2 := by
  rw [inner_krausSumₗ_rankOne_self]
  exact Complex.ofReal_re _

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **The Cauchy–Schwarz bound for a single operation element on a unit vector:**
`|⟨ψ, Eᵢ ψ⟩|² ≤ ‖Eᵢ ψ‖²` when `‖ψ‖ = 1`. Each pure-state operator-variance summand is `≥ 0`. -/
theorem normSq_inner_le_normSq_apply {ψ : H} (hψ : ‖ψ‖ = 1) (E : H →L[ℂ] H) :
    ‖inner ℂ ψ (E ψ)‖ ^ 2 ≤ ‖E ψ‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) ψ (E ψ)
  rw [hψ, one_mul] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

omit [FiniteDimensional ℂ H] in
/-- **The pure-state form of the variance decomposition.** For a unit vector `ψ` and a
trace-preserving family of operation elements (`Σᵢ Eᵢ† Eᵢ = 1`),
`1 − Σᵢ |⟨ψ, Eᵢ ψ⟩|² = Σᵢ (‖Eᵢ ψ‖² − |⟨ψ, Eᵢ ψ⟩|²)`, each summand `≥ 0`
(`normSq_inner_le_normSq_apply`). Combined with `re_inner_krausSumₗ_rankOne_self` this is
`1 − ⟨ψ|E(|ψ⟩⟨ψ|)|ψ⟩ = Σᵢ Var_{|ψ⟩⟨ψ|}(Eᵢ)`. The `1` comes from completeness:
`Σᵢ ‖Eᵢ ψ‖² = ⟨ψ, (Σᵢ Eᵢ† Eᵢ) ψ⟩ = ‖ψ‖² = 1`. -/
theorem one_sub_sum_normSq_inner_eq_sum {ψ : H} (hψ : ‖ψ‖ = 1) (E : ι → H →L[ℂ] H)
    (hE : ∑ i, adjoint (E i) * E i = 1) :
    1 - ∑ i, ‖inner ℂ ψ (E i ψ)‖ ^ 2 = ∑ i, (‖E i ψ‖ ^ 2 - ‖inner ℂ ψ (E i ψ)‖ ^ 2) := by
  have hsum : ∑ i, ‖E i ψ‖ ^ 2 = 1 := by
    rw [sum_normSq_apply_of_sum_adjoint_mul_self_eq_one E hE, hψ, one_pow]
  rw [Finset.sum_sub_distrib, hsum]

omit [FiniteDimensional ℂ H] in
/-- **The pure-state fidelity of a unit vector is at most `1`:** for a unit vector `ψ` and a
trace-preserving family of operation elements (`Σᵢ Eᵢ† Eᵢ = 1`),
`Σᵢ |⟨ψ, Eᵢ ψ⟩|² ≤ 1`. Each summand is bounded by `‖Eᵢ ψ‖²` (`normSq_inner_le_normSq_apply`) and
completeness collapses `Σᵢ ‖Eᵢ ψ‖² = ‖ψ‖² = 1`. In particular the deficit `η` in a fidelity bound
`1 − η ≤ Σᵢ |⟨ψ, Eᵢ ψ⟩|²` is nonnegative. -/
theorem sum_normSq_inner_self_le_one {ψ : H} (hψ : ‖ψ‖ = 1) (E : ι → H →L[ℂ] H)
    (hE : ∑ i, adjoint (E i) * E i = 1) :
    ∑ i, ‖inner ℂ ψ (E i ψ)‖ ^ 2 ≤ 1 := by
  calc ∑ i, ‖inner ℂ ψ (E i ψ)‖ ^ 2
      ≤ ∑ i, ‖E i ψ‖ ^ 2 := Finset.sum_le_sum fun i _ => normSq_inner_le_normSq_apply hψ (E i)
    _ = 1 := by rw [sum_normSq_apply_of_sum_adjoint_mul_self_eq_one E hE, hψ, one_pow]

end ContinuousLinearMap

namespace ContinuousLinearMap

section Eigenbasis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]

omit [CompleteSpace H] [DecidableEq ι] in
/-- **The entanglement fidelity in a spectral eigenbasis.** For a state written in an eigenbasis
`ρ = Σₐ pₐ |eₐ⟩⟨eₐ|` (`e : ι → H`, real weights `p`), the entanglement fidelity is computed from the
*diagonal* matrix elements of the operation elements,
`F(ρ, E) = Σⱼ |Σₐ pₐ ⟨eₐ, Eⱼ eₐ⟩|²` (Nielsen & Chuang, Eq. (9.135), via
`tr(ρ Eⱼ) = Σₐ pₐ ⟨eₐ, Eⱼ eₐ⟩`).

Each `tr(ρ Eⱼ) = Σₐ pₐ tr(|eₐ⟩⟨eₐ| Eⱼ) = Σₐ pₐ ⟨eₐ, Eⱼ eₐ⟩` by linearity of the trace and
`InnerProductSpace.trace_rankOne_self_comp`; neither orthonormality of `e` nor normalisation of `p`
is used. This is the diagonal ingredient of Nielsen & Chuang's *Problem 9.3* (fact (5)). -/
theorem entanglementFidelity_sum_rankOne (e : ι → H) (p : ι → ℝ) (E : κ → H →L[ℂ] H) :
    entanglementFidelity (∑ a, (p a : ℂ) • rankOne ℂ (e a) (e a)) E
      = ∑ j, ‖∑ a, (p a : ℂ) * inner ℂ (e a) (E j (e a))‖ ^ 2 := by
  simp only [entanglementFidelity]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : (LinearMap.trace ℂ H) ↑((∑ a, (p a : ℂ) • rankOne ℂ (e a) (e a)) * E j)
      = ∑ a, (p a : ℂ) * inner ℂ (e a) (E j (e a)) := by
    rw [Finset.sum_mul, ContinuousLinearMap.toLinearMap_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_mul_assoc, ContinuousLinearMap.toLinearMap_smul, map_smul,
      ContinuousLinearMap.mul_def,
      InnerProductSpace.trace_rankOne_self_comp, smul_eq_mul]
  rw [h]

omit [DecidableEq ι] in
/-- **The entanglement fidelity of a pure-state mixture is at most `1`** (unit-vector form). For any
probability mixture of pure states `ρ = Σₐ pₐ |eₐ⟩⟨eₐ|` — a family `e : ι → H` of **unit vectors**
(`‖eₐ‖ = 1`, *not* required orthonormal) weighted by a probability vector `p` (`0 ≤ p`, `Σ p = 1`) —
and any trace-preserving family of operation elements (`Σⱼ Eⱼ† Eⱼ = 1`), the entanglement fidelity
satisfies `F(ρ, E) ≤ 1`.

By `entanglementFidelity_sum_rankOne` the fidelity reads off the diagonal matrix elements,
`F(ρ, E) = Σⱼ |Σₐ pₐ ⟨eₐ, Eⱼ eₐ⟩|²`. The probability-weighted Jensen bound
`‖Σₐ pₐ wₐ‖² ≤ Σₐ pₐ ‖wₐ‖²` (triangle inequality followed by the Cauchy–Schwarz sum inequality,
using `Σ pₐ = 1`) moves the weights inside each squared modulus, and swapping the order of summation
leaves `Σₐ pₐ (Σⱼ |⟨eₐ, Eⱼ eₐ⟩|²) ≤ Σₐ pₐ · 1 = 1`, the inner bound being the pure-state fidelity
bound `sum_normSq_inner_self_le_one` at the unit vector `eₐ` (only `‖eₐ‖ = 1` is used, not
orthogonality). This is the upper half of the `0 ≤ F(ρ, E) ≤ 1` range of the entanglement fidelity
(Nielsen & Chuang, §9.3). -/
theorem entanglementFidelity_le_one_of_sum_rankOne (e : ι → H) (he : ∀ a, ‖e a‖ = 1) (p : ι → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (E : κ → H →L[ℂ] H)
    (hE : ∑ j, adjoint (E j) * E j = 1) :
    entanglementFidelity (∑ a, (p a : ℂ) • rankOne ℂ (e a) (e a)) E ≤ 1 := by
  -- Probability-weighted Jensen: `‖Σₐ pₐ wₐ‖² ≤ Σₐ pₐ ‖wₐ‖²`.
  have jensen : ∀ w : ι → ℂ, ‖∑ a, (p a : ℂ) * w a‖ ^ 2 ≤ ∑ a, p a * ‖w a‖ ^ 2 := by
    intro w
    have h1 : ‖∑ a, (p a : ℂ) * w a‖ ≤ ∑ a, p a * ‖w a‖ :=
      (norm_sum_le _ _).trans <| le_of_eq <| Finset.sum_congr rfl fun a _ => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp0 a)]
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun a => Real.sqrt (p a)) (fun a => Real.sqrt (p a) * ‖w a‖)
    have e1 : (∑ a, Real.sqrt (p a) * (Real.sqrt (p a) * ‖w a‖)) = ∑ a, p a * ‖w a‖ :=
      Finset.sum_congr rfl fun a _ => by rw [← mul_assoc, Real.mul_self_sqrt (hp0 a)]
    have e2 : (∑ a, Real.sqrt (p a) ^ 2) = 1 := by
      rw [Finset.sum_congr rfl fun a _ => Real.sq_sqrt (hp0 a), hp1]
    have e3 : (∑ a, (Real.sqrt (p a) * ‖w a‖) ^ 2) = ∑ a, p a * ‖w a‖ ^ 2 :=
      Finset.sum_congr rfl fun a _ => by rw [mul_pow, Real.sq_sqrt (hp0 a)]
    rw [e1, e2, e3, one_mul] at hCS
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans hCS
  rw [entanglementFidelity_sum_rankOne]
  calc ∑ j, ‖∑ a, (p a : ℂ) * inner ℂ (e a) (E j (e a))‖ ^ 2
      ≤ ∑ j, ∑ a, p a * ‖inner ℂ (e a) (E j (e a))‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => jensen _
    _ = ∑ a, p a * ∑ j, ‖inner ℂ (e a) (E j (e a))‖ ^ 2 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ a, p a * 1 :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (sum_normSq_inner_self_le_one (he a) E hE) (hp0 a)
    _ = 1 := by simp only [mul_one]; exact hp1

/-- **The entanglement fidelity of a density operator is at most `1`** (Nielsen & Chuang, §9.3): for
any density operator `ρ` (`ρ.IsDensityOp`, i.e. positive with `tr ρ = 1`) and any trace-preserving
family of operation elements (`Σⱼ Eⱼ† Eⱼ = 1`), `F(ρ, E) ≤ 1`.

Together with `entanglementFidelity_nonneg` this places the entanglement fidelity in `[0, 1]`. The
proof is the spectral theorem plus the pure-state-mixture bound
`entanglementFidelity_le_one_of_sum_rankOne`:
writing `ρ = Σᵢ λᵢ |eᵢ⟩⟨eᵢ|` in its orthonormal eigenbasis (`IsSelfAdjoint.spectral_sum`), the
eigenvectors are unit vectors and the eigenvalues `λᵢ` are a probability vector
(`IsDensityOp.eigenvalues_nonneg` / `IsDensityOp.eigenvalues_sum_eq_one`), so that bound applies. -/
theorem entanglementFidelity_le_one {ρ : H →L[ℂ] H} (hρ : ρ.IsDensityOp) (E : κ → H →L[ℂ] H)
    (hE : ∑ j, adjoint (E j) * E j = 1) : entanglementFidelity ρ E ≤ 1 := by
  have hsa : IsSelfAdjoint ρ := hρ.isPositive.isSelfAdjoint
  rw [hsa.spectral_sum (rfl : Module.finrank ℂ H = Module.finrank ℂ H)]
  exact entanglementFidelity_le_one_of_sum_rankOne _
    (fun a => (hsa.isSymmetric.eigenvectorBasis rfl).orthonormal.1 a) _
    (fun a => hρ.eigenvalues_nonneg rfl a) (hρ.eigenvalues_sum_eq_one rfl) E hE

/-- **The off-diagonal coherence sum** `S_off = Σ_{a≠b} pₐ p_b Σⱼ |⟨eₐ, Eⱼ e_b⟩|²` of a family of
operation elements `E` in the eigenbasis `{eₐ}` weighted by `p`. This is the off-diagonal
("coherence") part of the entanglement infidelity `1 − F(ρ, E)` for `ρ = Σₐ pₐ |eₐ⟩⟨eₐ|` — the term
the phase-diagonal twirl isolates in Nielsen & Chuang's *Problem 9.3* (fact (5)). It is bounded by
`η / 2` (`offDiagCoherenceSum_le`), the estimate separating the tight `F ≥ 1 − 3η/2` from the weaker
`1 − 2η`. The summation order matches `weighted_offDiag_sum_le_half`: outer over the column `b`,
inner over the off-diagonal rows `a ≠ b`. -/
noncomputable def offDiagCoherenceSum (e : ι → H) (p : ι → ℝ) (E : κ → H →L[ℂ] H) : ℝ :=
  ∑ y, ∑ x ∈ Finset.univ.erase y, p x * p y * ∑ j, ‖inner ℂ (e x) (E j (e y))‖ ^ 2

omit [FiniteDimensional ℂ H] in
/-- **The per-column coherence budget.** In an orthonormal basis `b`, the off-diagonal weight of the
`i₀`-th column, `Σ_{a≠i₀} Σⱼ |⟨bₐ, Eⱼ b_{i₀}⟩|²`, is at most `η` whenever the pure-state fidelity of
the eigenvector `b_{i₀}` is at least `1 − η` (`1 − η ≤ Σⱼ |⟨b_{i₀}, Eⱼ b_{i₀}⟩|²`) and the family is
trace preserving (`Σⱼ Eⱼ† Eⱼ = 1`).

By Parseval (`OrthonormalBasis.sum_sq_norm_inner_right`) `Σₐ |⟨bₐ, Eⱼ b_{i₀}⟩|² = ‖Eⱼ b_{i₀}‖²`, and
by completeness `Σⱼ ‖Eⱼ b_{i₀}‖² = ‖b_{i₀}‖² = 1`, so the off-diagonal weight equals the pure-state
variance deficit `1 − Σⱼ |⟨b_{i₀}, Eⱼ b_{i₀}⟩|² ≤ η` (cf. `one_sub_sum_normSq_inner_eq_sum`). This
is the column budget consumed by `weighted_offDiag_sum_le_half` in `offDiagCoherenceSum_le`. -/
theorem sum_offDiag_normSq_inner_le (b : OrthonormalBasis ι ℂ H) (E : κ → H →L[ℂ] H)
    (hE : ∑ j, adjoint (E j) * E j = 1) {η : ℝ} (i₀ : ι)
    (hfid : 1 - η ≤ ∑ j, ‖inner ℂ (b i₀) (E j (b i₀))‖ ^ 2) :
    ∑ a ∈ Finset.univ.erase i₀, ∑ j, ‖inner ℂ (b a) (E j (b i₀))‖ ^ 2 ≤ η := by
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_erase_eq_sub (Finset.mem_univ i₀), b.sum_sq_norm_inner_right]
  rw [Finset.sum_sub_distrib,
    ContinuousLinearMap.sum_normSq_apply_of_sum_adjoint_mul_self_eq_one E hE (b i₀),
    b.orthonormal.1 i₀, one_pow]
  linarith [hfid]

omit [FiniteDimensional ℂ H] in
/-- **The off-diagonal coherence is at most `η / 2` — support-aware form.** If `ρ = Σₐ pₐ |bₐ⟩⟨bₐ|`
is a density operator in the orthonormal eigenbasis `b` (`p` a probability vector) and every
*positive-weight* eigenvector `bₐ` (`0 < pₐ`, hence `bₐ ∈ supp ρ`) has pure-state fidelity `≥ 1 − η`
under the trace-preserving family `E`, then `offDiagCoherenceSum b p E ≤ η / 2`.

Unlike `offDiagCoherenceSum_le`, only columns with `pₐ > 0` need a fidelity budget: the doubly
`p`-weighted off-diagonal sum `S_off = Σ_{a≠c} pₐ p_c Σⱼ |⟨bₐ, Eⱼ b_c⟩|²` annihilates every column
with `p_c = 0`. Formally, `S_off` is unchanged if the coherence array is *capped* to `0` on
zero-weight columns, and the capped array meets the per-column budget of
`weighted_offDiag_sum_le_half` — `≤ η` on positive columns (`sum_offDiag_normSq_inner_le`) and `≤ η`
trivially (`= 0 ≤ η`) on the capped ones. This is the shape Nielsen & Chuang's *Problem 9.3* support
hypothesis supplies, since eigenvectors with `pₐ = 0` are outside `supp ρ`. -/
theorem offDiagCoherenceSum_le_of_pos (b : OrthonormalBasis ι ℂ H) (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (E : κ → H →L[ℂ] H)
    (hE : ∑ j, adjoint (E j) * E j = 1) {η : ℝ} (hη : 0 ≤ η)
    (hfid : ∀ i, 0 < p i → 1 - η ≤ ∑ j, ‖inner ℂ (b i) (E j (b i))‖ ^ 2) :
    offDiagCoherenceSum (⇑b) p E ≤ η / 2 := by
  classical
  -- Cap the coherence array to `0` on zero-weight columns; `S_off` is unchanged.
  have heq : offDiagCoherenceSum (⇑b) p E
      = ∑ c, ∑ a ∈ Finset.univ.erase c, p a * p c *
          (if 0 < p c then ∑ j, ‖inner ℂ (b a) (E j (b c))‖ ^ 2 else 0) := by
    rw [offDiagCoherenceSum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    by_cases hpc : 0 < p c
    · rw [ite_eq_left hpc]
    · rw [ite_eq_right hpc, le_antisymm (not_lt.mp hpc) (hp0 c)]; ring
  rw [heq]
  refine weighted_offDiag_sum_le_half hp0 hp1 (fun a c => ?_) (fun c => ?_)
  · by_cases hpc : 0 < p c
    · simp only [ite_eq_left hpc]; positivity
    · simp only [ite_eq_right hpc, le_refl]
  · by_cases hpc : 0 < p c
    · simp only [ite_eq_left hpc]
      exact sum_offDiag_normSq_inner_le b E hE c (hfid c hpc)
    · simp only [ite_eq_right hpc, Finset.sum_const_zero]; exact hη

omit [FiniteDimensional ℂ H] in
/-- **The off-diagonal coherence is at most `η / 2`.** If `ρ = Σₐ pₐ |bₐ⟩⟨bₐ|` is a density operator
in the orthonormal eigenbasis `b` (`p` a probability vector: `0 ≤ p`, `Σ p = 1`) whose every
eigenvector has pure-state fidelity `≥ 1 − η` under the trace-preserving family `E`, then
`offDiagCoherenceSum b p E ≤ η / 2`.

The all-columns corollary of `offDiagCoherenceSum_le_of_pos` (which needs a budget only on the
positive-weight columns): every column meets the hypothesis, and `η ≥ 0` follows because a
pure-state fidelity is `≤ 1` (`sum_normSq_inner_self_le_one`, at any eigenvector — `ι` is nonempty
as `∑ p = 1`). The `η / 2` — rather than `η` — is the estimate that yields Nielsen & Chuang's tight
`F(ρ, E) ≥ 1 − 3η/2` for *Problem 9.3* (fact (5)). -/
theorem offDiagCoherenceSum_le (b : OrthonormalBasis ι ℂ H) (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (E : κ → H →L[ℂ] H)
    (hE : ∑ j, adjoint (E j) * E j = 1) {η : ℝ}
    (hfid : ∀ i, 1 - η ≤ ∑ j, ‖inner ℂ (b i) (E j (b i))‖ ^ 2) :
    offDiagCoherenceSum (⇑b) p E ≤ η / 2 := by
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hp1
    exact absurd hp1 (by norm_num)
  refine offDiagCoherenceSum_le_of_pos b p hp0 hp1 E hE ?_ (fun i _ => hfid i)
  linarith [hfid i₀, sum_normSq_inner_self_le_one (b.orthonormal.1 i₀) E hE]

end Eigenbasis

end ContinuousLinearMap
