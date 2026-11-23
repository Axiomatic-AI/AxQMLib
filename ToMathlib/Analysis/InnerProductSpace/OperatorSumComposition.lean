/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSumCP

/-!
# Composition of operator-sum (Kraus) maps — Nielsen–Chuang Exercise 8.6

The **composition** of two quantum operations is again a quantum operation. Concretely, if `E`
has operator-sum (Kraus) representation `E(ρ) = Σᵢ Eᵢ ρ Eᵢ†` and `F` has representation
`F(σ) = Σⱼ Fⱼ σ Fⱼ†`, then the composite `(F ∘ E)(ρ) = Σⱼ Σᵢ Fⱼ Eᵢ ρ Eᵢ† Fⱼ†` is itself an
operator-sum map, with operation elements the products `{Fⱼ Eᵢ}`. This is Nielsen–Chuang
*Quantum Computation and Quantum Information*, **Exercise 8.6** (§8.2, p. 362).

The input and output spaces need not agree: `E` maps operators on `H` to operators on `G`, `F`
maps operators on `G` to operators on `K`, and the composite maps operators on `H` to operators on
`K`, with operation elements `Fⱼ Eᵢ : H →L[ℂ] K`. This is the space-changing extension the exercise
asks for; the "same quantum system" case is the specialisation `H = G = K`.

## Main results

* `ContinuousLinearMap.krausSumₗ_comp` — the composite of two operator-sum maps is the operator-sum
  map of the product family: `(krausSumₗ F).comp (krausSumₗ E) = krausSumₗ (fun (j, i) ↦ Fⱼ ∘ Eᵢ)`.
* `ContinuousLinearMap.sum_adjoint_comp_comp_le_one` — the composite family inherits the trace
  condition: if `Σᵢ Eᵢ† Eᵢ ≤ 1` and `Σⱼ Fⱼ† Fⱼ ≤ 1` then `Σ_{j,i} (Fⱼ Eᵢ)† (Fⱼ Eᵢ) ≤ 1`.
* `ContinuousLinearMap.IsOperatorSum.comp` — **Exercise 8.6:** if `Φ` and `Ψ` have operator-sum
  representations (`IsOperatorSum E Φ`, `IsOperatorSum F Ψ`) then the composite `Ψ ∘ Φ` has the
  operator-sum representation given by the product family `{Fⱼ Eᵢ}`.
* `ContinuousLinearMap.IsOperatorSum.comp_satisfiesAxioms` — the composite is therefore a quantum
  operation: `SatisfiesOperationAxioms (Ψ ∘ Φ)` (via the forward direction of N&C Theorem 8.1,
  `IsOperatorSum.satisfiesAxioms`).

## Design notes

The algebraic identity `krausSumₗ_comp` reindexes the double sum by the product type `κ × ι`, so the
composite operation elements are literally `fun p : κ × ι => (F p.1).comp (E p.2)`; the reindexing
freedom of the representation (`krausSumₗ_comp_equiv`) means any bijection with `κ × ι` gives the
same map, so this choice of index is immaterial. The trace-condition inheritance factors the double
sum as `Σᵢ Eᵢ† (Σⱼ Fⱼ† Fⱼ) Eᵢ` and bounds the inner conjugation by monotonicity of `X ↦ Eᵢ† X Eᵢ`
in the Loewner order (from `IsPositive.conj_adjoint`): with `B := Σⱼ Fⱼ† Fⱼ ≤ 1`, each summand is
`≤ Eᵢ† Eᵢ`, so the total is `≤ Σᵢ Eᵢ† Eᵢ ≤ 1`.

This mirrors the algebraic level of Nielsen–Chuang §8.2 (Theorems 8.1–8.3), whose formal content is
operator/Hilbert-space linear algebra over `H →L[ℂ] G`; compare `OperatorSum.lean` (Theorem 8.2)
and `MinimalOperatorSum.lean` (Theorem 8.3). The statement of Exercise 8.6 is in
`AxQM/NC/Ch8/Exercise8_6.lean`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §8.2 (Exercise 8.6).
-/

@[expose] public section

namespace ContinuousLinearMap

section

variable {H G K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The composite of two operator-sum (Kraus) maps is the operator-sum map of the product family**
(Nielsen–Chuang Exercise 8.6). For families `E : ι → (H →L[ℂ] G)` and `F : κ → (G →L[ℂ] K)`, the
composition of the operator-sum maps `krausSumₗ E : ρ ↦ Σᵢ Eᵢ ρ Eᵢ†` and `krausSumₗ F : σ ↦ Σⱼ Fⱼ σ
Fⱼ†` equals the single operator-sum map of the product family `(j, i) ↦ Fⱼ ∘ Eᵢ`:
`(krausSumₗ F) ∘ (krausSumₗ E) = krausSumₗ (fun p : κ × ι => Fₚ₁ ∘ Eₚ₂)`.
Expanding the composition gives `Σⱼ Σᵢ Fⱼ (Eᵢ ρ Eᵢ†) Fⱼ†`, and `adjoint (Fⱼ ∘ Eᵢ) = Eᵢ† ∘ Fⱼ†` with
associativity recasts each summand as `(Fⱼ Eᵢ) ρ (Fⱼ Eᵢ)†`; reindexing the double sum by `κ × ι`
completes the identity. -/
theorem krausSumₗ_comp (E : ι → H →L[ℂ] G) (F : κ → G →L[ℂ] K) :
    (krausSumₗ F).comp (krausSumₗ E)
      = krausSumₗ (fun p : κ × ι => (F p.1).comp (E p.2)) := by
  refine LinearMap.ext fun ρ => ?_
  rw [LinearMap.comp_apply, krausSumₗ_apply E, map_sum]
  rw [krausSumₗ_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [adjoint_comp, comp_assoc]

/-- **Factorization of the composite-family completeness sum** (Nielsen–Chuang Exercise 8.6). For
families `E : ι → (H →L[ℂ] G)` and `F : κ → (G →L[ℂ] K)`, the completeness sum of the product family
`(j, i) ↦ Fⱼ ∘ Eᵢ` reassociates as `Σ_{j,i} (Fⱼ Eᵢ)† (Fⱼ Eᵢ) = Σᵢ Eᵢ† (Σⱼ Fⱼ† Fⱼ) Eᵢ`: summing over
`κ` first and using `adjoint (Fⱼ Eᵢ) = Eᵢ† Fⱼ†` with associativity pulls the inner block `Σⱼ Fⱼ† Fⱼ`
between `Eᵢ†` and `Eᵢ`. This is the shared algebraic core of both the `≤ 1` and `= 1` composite
trace conditions (`sum_adjoint_comp_comp_le_one`, `sum_adjoint_comp_comp_eq_one`). -/
theorem sum_adjoint_comp_comp_eq_sum (E : ι → H →L[ℂ] G) (F : κ → G →L[ℂ] K) :
    ∑ p : κ × ι, adjoint ((F p.1).comp (E p.2)) ∘L (F p.1).comp (E p.2)
      = ∑ i, adjoint (E i) ∘L (∑ j, adjoint (F j) ∘L F j) ∘L E i := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsetSum_comp, comp_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [adjoint_comp]
  simp only [comp_assoc]

/-- **The product family inherits the operator-sum trace condition** (Nielsen–Chuang Exercise 8.6).
If `Σᵢ Eᵢ† Eᵢ ≤ 1` and `Σⱼ Fⱼ† Fⱼ ≤ 1`, then the product family `(j, i) ↦ Fⱼ ∘ Eᵢ` satisfies
`Σ_{j,i} (Fⱼ Eᵢ)† (Fⱼ Eᵢ) ≤ 1`. Factoring the double sum as `Σᵢ Eᵢ† (Σⱼ Fⱼ† Fⱼ) Eᵢ`
(`sum_adjoint_comp_comp_eq_sum`) and writing `B := Σⱼ Fⱼ† Fⱼ`, monotonicity of `X ↦ Eᵢ† X Eᵢ` in the
Loewner order (`IsPositive.conj_adjoint` applied to `1 - B ≥ 0`) bounds each summand by `Eᵢ† Eᵢ`, so
the total is `≤ Σᵢ Eᵢ† Eᵢ ≤ 1`. This is the trace condition for the composite quantum operation. -/
theorem sum_adjoint_comp_comp_le_one (E : ι → H →L[ℂ] G) (F : κ → G →L[ℂ] K)
    (hE : ∑ i, adjoint (E i) ∘L E i ≤ 1) (hF : ∑ j, adjoint (F j) ∘L F j ≤ 1) :
    ∑ p : κ × ι, adjoint ((F p.1).comp (E p.2)) ∘L (F p.1).comp (E p.2) ≤ 1 := by
  rw [sum_adjoint_comp_comp_eq_sum]
  set B := ∑ j, adjoint (F j) ∘L F j
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) hE
  -- `Eᵢ† B Eᵢ ≤ Eᵢ† Eᵢ`, since `B ≤ 1` and conjugation is Loewner-monotone.
  have hp := nonneg_iff_isPositive.mp (sub_nonneg.mpr hF)
  have hcj := hp.conj_adjoint (adjoint (E i))
  rw [adjoint_adjoint] at hcj
  have h2 := nonneg_iff_isPositive.mpr hcj
  have hexp : adjoint (E i) ∘L (1 - B) ∘L E i
      = adjoint (E i) ∘L E i - adjoint (E i) ∘L B ∘L E i := by
    rw [sub_comp, comp_sub, one_def, id_comp]
  rw [hexp] at h2
  exact sub_nonneg.mp h2

/-- **The product family inherits operator-sum trace-preservation** — the equality (exact,
trace-preserving) companion of `sum_adjoint_comp_comp_le_one` (Nielsen–Chuang Exercise 8.6). If
`Σᵢ Eᵢ† Eᵢ = 1` and `Σⱼ Fⱼ† Fⱼ = 1`, then the product family `(j, i) ↦ Fⱼ ∘ Eᵢ` is trace-preserving:
`Σ_{j,i} (Fⱼ Eᵢ)† (Fⱼ Eᵢ) = 1`. Factoring the double sum as `Σᵢ Eᵢ† (Σⱼ Fⱼ† Fⱼ) Eᵢ` and
substituting `Σⱼ Fⱼ† Fⱼ = 1` collapses each summand to `Eᵢ† Eᵢ`, summing to `1` by the `E`
hypothesis. This is the trace-preservation of the composite `Ψ ∘ Φ` of two trace-preserving
operations, used in Nielsen & Chuang's converse to Theorem 12.6 (Eq. (12.58)). -/
theorem sum_adjoint_comp_comp_eq_one (E : ι → H →L[ℂ] G) (F : κ → G →L[ℂ] K)
    (hE : ∑ i, adjoint (E i) ∘L E i = 1) (hF : ∑ j, adjoint (F j) ∘L F j = 1) :
    ∑ p : κ × ι, adjoint ((F p.1).comp (E p.2)) ∘L (F p.1).comp (E p.2) = 1 := by
  rw [sum_adjoint_comp_comp_eq_sum, hF]
  simp only [one_def, id_comp]
  exact hE

/-- **The composition of quantum operations is a quantum operation** (Nielsen–Chuang, *Quantum
Computation and Quantum Information*, **Exercise 8.6**). If superoperators `Φ` and `Ψ` have
operator-sum (Kraus) representations — `IsOperatorSum E Φ` (i.e. `Φ = krausSumₗ E` with
`Σᵢ Eᵢ† Eᵢ ≤ 1`) and `IsOperatorSum F Ψ` — then their composite `Ψ ∘ Φ` has the operator-sum
representation given by the product family `(j, i) ↦ Fⱼ ∘ Eᵢ`, `IsOperatorSum (fun p ↦ Fₚ₁ ∘ Eₚ₂)
(Ψ ∘ Φ)`. The map equality is `krausSumₗ_comp` and the trace condition is
`sum_adjoint_comp_comp_le_one`.

The spaces need not coincide (`E : ι → H →L[ℂ] G`, `F : κ → G →L[ℂ] K`), so this is the
space-changing extension the exercise asks for, with the "same quantum system" case the
specialisation `H = G = K`. -/
theorem IsOperatorSum.comp {E : ι → H →L[ℂ] G} {F : κ → G →L[ℂ] K}
    {Φ : (H →L[ℂ] H) →ₗ[ℂ] G →L[ℂ] G} {Ψ : (G →L[ℂ] G) →ₗ[ℂ] K →L[ℂ] K}
    (hE : IsOperatorSum E Φ) (hF : IsOperatorSum F Ψ) :
    IsOperatorSum (fun p : κ × ι => (F p.1).comp (E p.2)) (Ψ.comp Φ) := by
  obtain ⟨hΦ, hEcond⟩ := hE
  obtain ⟨hΨ, hFcond⟩ := hF
  refine ⟨?_, sum_adjoint_comp_comp_le_one E F hEcond hFcond⟩
  rw [hΦ, hΨ, krausSumₗ_comp]

end

section

variable {H G K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K] [CompleteSpace K]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The composite of two quantum operations satisfies the operation axioms** (Nielsen–Chuang
Exercise 8.6, together with Theorem 8.1). If `Φ` and `Ψ` have operator-sum representations, then the
composite `Ψ ∘ Φ` satisfies the Nielsen–Chuang quantum-operation axioms A1, A2, A3
(`SatisfiesOperationAxioms`): the composite has an operator-sum representation
(`IsOperatorSum.comp`) and any operator-sum map is a quantum operation
(`IsOperatorSum.satisfiesAxioms`, the forward direction of Theorem 8.1). -/
theorem IsOperatorSum.comp_satisfiesAxioms {E : ι → H →L[ℂ] G} {F : κ → G →L[ℂ] K}
    {Φ : (H →L[ℂ] H) →ₗ[ℂ] G →L[ℂ] G} {Ψ : (G →L[ℂ] G) →ₗ[ℂ] K →L[ℂ] K}
    (hE : IsOperatorSum E Φ) (hF : IsOperatorSum F Ψ) :
    SatisfiesOperationAxioms (Ψ.comp Φ) :=
  (hE.comp hF).satisfiesAxioms

end

end ContinuousLinearMap
