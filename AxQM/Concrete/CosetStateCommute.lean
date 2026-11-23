/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CosetState

/-!
# Concrete: coset density matrices of an abelian group commute

For a **commutative** finite group
`H` and two subgroups `K₁, K₂ ≤ H`, the coset density matrices `σ_{K₁}, σ_{K₂}` (`cosetDensity`,
entries `σ_K i j = |H|⁻¹ · [iK = jK]`, see `AxQM.Concrete.CosetState`) **commute**:

`σ_{K₁} · σ_{K₂} = σ_{K₂} · σ_{K₁}`   (`cosetDensity_commute`).

`σ_K` is the convolution operator by the normalized indicator `|H|⁻¹ · 𝟙_K` (its `(i, j)` entry
depends only on `i⁻¹ j`), and convolution on an abelian group is commutative — equivalently the
`σ_K` are simultaneously diagonal in the character basis. The proof here is entirely elementary and
avoids Fourier analysis: it computes the two product entries as sums over the group and matches them
by an **involution** on the summation index. The `(i, j)` entry of `σ_{K₁} σ_{K₂}` is

`|H|⁻² · #{k : i⁻¹k ∈ K₁ ∧ k⁻¹j ∈ K₂}`

and that of `σ_{K₂} σ_{K₁}` is `|H|⁻² · #{k : i⁻¹k ∈ K₂ ∧ k⁻¹j ∈ K₁}`. The map `k ↦ i · k⁻¹ · j`
is an involution of `H` (using commutativity) that carries the first index set onto the second —
`i⁻¹(i k⁻¹ j) = k⁻¹ j` (swaps the `K₂` condition, no commutativity needed) and
`(i k⁻¹ j)⁻¹ j = i⁻¹ k` (swaps the `K₁` condition, using commutativity) — so the two sums agree.

This is the group-theoretic input to the piece-(i)(a) **paired-trace inequality** for the abelian
hidden-subgroup problem (Nielsen & Chuang, Problem 5.5): when the candidate reduced states pairwise
commute, the paired-trace bound holds unconditionally (`State.pairedTraceBound_of_commute`), so this
commutation makes the identification headline fully unconditional for abelian `G`. -/

namespace AxQM.Concrete

variable {H : Type*} [CommGroup H] [Fintype H]

/-- **The coset density matrices of an abelian group commute** (Nielsen & Chuang, Problem 5.5). For
a commutative finite group `H` and two subgroups `K₁, K₂ ≤ H`, `σ_{K₁} · σ_{K₂} = σ_{K₂} · σ_{K₁}`.

`σ_K` is a convolution operator (`σ_K i j = |H|⁻¹ · [iK = jK]` depends only on `i⁻¹ j`), and
convolution on an abelian group is commutative. Concretely, the `(i, j)` entry of `σ_{K₁} σ_{K₂}`
counts `k` with `i⁻¹k ∈ K₁` and `k⁻¹j ∈ K₂`, that of `σ_{K₂} σ_{K₁}` counts `k` with `i⁻¹k ∈ K₂`
and `k⁻¹j ∈ K₁`; the involution `k ↦ i · k⁻¹ · j` (an equivalence of `H` since `H` is abelian)
matches the two — `i⁻¹(i k⁻¹ j) = k⁻¹ j` and `(i k⁻¹ j)⁻¹ j = i⁻¹ k` swap the two membership
conditions. This is the group-theoretic core of the piece-(i)(a) paired-trace inequality for the
abelian hidden-subgroup problem. -/
theorem cosetDensity_commute (K₁ K₂ : Subgroup H)
    [DecidablePred (· ∈ K₁)] [DecidablePred (· ∈ K₂)] :
    Commute (cosetDensity K₁) (cosetDensity K₂) := by
  classical
  change cosetDensity K₁ * cosetDensity K₂ = cosetDensity K₂ * cosetDensity K₁
  ext i j
  simp only [Matrix.mul_apply, cosetDensity_apply]
  -- Reindex the second sum by the involution `ψ k = i * k⁻¹ * j`; it swaps the two membership
  -- conditions, so the summands agree termwise (up to the commutativity of `ℂ`-multiplication).
  let ψ : H ≃ H := (Equiv.inv H).trans ((Equiv.mulLeft i).trans (Equiv.mulRight j))
  refine Fintype.sum_bijective ψ ψ.bijective _ _ (fun k => ?_)
  have hA : ((↑i : H ⧸ K₁) = (↑k : H ⧸ K₁)) ↔ ((↑(ψ k) : H ⧸ K₁) = (↑j : H ⧸ K₁)) := by
    rw [QuotientGroup.eq, QuotientGroup.eq]
    have hel : (ψ k)⁻¹ * j = i⁻¹ * k := by
      change (i * k⁻¹ * j)⁻¹ * j = i⁻¹ * k
      rw [mul_inv, mul_inv, inv_inv]; group
    rw [hel]
  have hB : ((↑k : H ⧸ K₂) = (↑j : H ⧸ K₂)) ↔ ((↑i : H ⧸ K₂) = (↑(ψ k) : H ⧸ K₂)) := by
    rw [QuotientGroup.eq, QuotientGroup.eq]
    have hel : i⁻¹ * (ψ k) = k⁻¹ * j := by
      change i⁻¹ * (i * k⁻¹ * j) = k⁻¹ * j
      group
    rw [hel]
  rw [if_congr hA rfl rfl, if_congr hB rfl rfl, mul_comm]

end AxQM.Concrete
