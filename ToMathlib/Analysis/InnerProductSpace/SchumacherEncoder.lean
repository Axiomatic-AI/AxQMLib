/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.EntanglementFidelity
public import ToMathlib.Analysis.InnerProductSpace.RankOneProjector

/-! # Schumacher's projection–reset encoder and its entanglement fidelity

This file records the *encoding operation* used in the direct (achievability) part of Schumacher's
quantum noiseless channel coding theorem (Nielsen–Chuang, *Quantum Computation and Quantum
Information*, §12.2.2, eqs. (12.50)–(12.52)), together with the two structural facts that make it a
reliable compression scheme: it is trace-preserving, and its entanglement fidelity is bounded below
by `|tr(ρ P)|²`.

Fix an orthonormal basis `b : OrthonormalBasis ι ℂ H`, a finite index set `s : Finset ι` — the
"typical" indices, cutting out the code subspace `range P` with projector
`P = ∑_{i ∈ s} |bᵢ⟩⟨bᵢ|` (`InnerProductSpace.orthonormalProjector`) — and a reference index `i₀`.
The **projection–reset encoder** is the trace-preserving quantum operation with operation elements
`{P} ∪ {Aᵢ : i ∉ s}`, where `Aᵢ = |b i₀⟩⟨bᵢ|` (N&C eq. (12.50)):

`C(σ) = P σ P + ∑_{i ∉ s} Aᵢ σ Aᵢ†`.

The projector `P` leaves the code subspace untouched, while each reset operator `Aᵢ` collapses the
atypical basis vector `bᵢ` onto the fixed reference vector `b i₀`; taking `i₀ ∈ s` puts the whole
image inside the code subspace, so `C` compresses into `range P`. The decoding operation is the
identity, so the composite `D ∘ C` has the same operation elements as `C`.

## Main results

* `ContinuousLinearMap.schumacherEncoder` — the family of operation elements, indexed by `Option ι`
  (`none ↦ P`, `some i ↦ Aᵢ`, taken to be `0` for `i ∈ s`).
* `ContinuousLinearMap.schumacherEncoder_isTracePreserving` — the completeness relation
  `∑ⱼ Eⱼ† Eⱼ = 1`, i.e. `C` is a trace-preserving quantum operation. It follows from
  `P + ∑_{i ∉ s} |bᵢ⟩⟨bᵢ| = 1` (the resolution of identity split across `s` and `sᶜ`).
* `ContinuousLinearMap.entanglementFidelity_schumacherEncoder` — **N&C eq. (12.51)**:
  `F(ρ, C) = |tr(ρ P)|² + ∑_{i ∉ s} |tr(ρ Aᵢ)|²`.
* `ContinuousLinearMap.entanglementFidelity_schumacherEncoder_ge` — **N&C eq. (12.52)**:
  `F(ρ, C) ≥ |tr(ρ P)|²`, because `P` is one of the operation elements and the remaining terms are
  nonnegative. In Schumacher's theorem the right-hand side is `|tr(ρ^⊗ⁿ P(n,ε))|² ≥ (1 − δ)²` by
  part (1) of the typical subspace theorem, giving reliability.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.2.2 (eqs. (12.50)–(12.52)).
-/

open scoped InnerProductSpace ComplexConjugate

@[expose] public section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Schumacher's projection–reset encoder** (Nielsen & Chuang, eq. (12.50)), as a family of
operation elements indexed by `Option ι`. Given an orthonormal basis `b`, a set `s` of "typical"
indices and a reference index `i₀`:

* `none ↦ P = ∑_{i ∈ s} |bᵢ⟩⟨bᵢ|`, the projector onto the code subspace;
* `some i ↦ |b i₀⟩⟨bᵢ|` for `i ∉ s` (and `0` for `i ∈ s`), the reset operator collapsing the
  atypical vector `bᵢ` onto the reference vector `b i₀`.

The associated quantum operation is `C(σ) = P σ P + ∑_{i ∉ s} |b i₀⟩⟨bᵢ| σ |bᵢ⟩⟨b i₀|`; it is
trace-preserving (`schumacherEncoder_isTracePreserving`). -/
noncomputable def schumacherEncoder (b : OrthonormalBasis ι ℂ H) (s : Finset ι) (i₀ : ι) :
    Option ι → H →L[ℂ] H
  | none => InnerProductSpace.orthonormalProjector ℂ (⇑b) s
  | some i => if i ∈ s then 0 else (InnerProductSpace.rankOne ℂ (b i₀)) (b i)

/-- The `none` element of the Schumacher encoder is the code-subspace projector `P`. -/
@[simp]
theorem schumacherEncoder_none (b : OrthonormalBasis ι ℂ H) (s : Finset ι) (i₀ : ι) :
    schumacherEncoder b s i₀ none = InnerProductSpace.orthonormalProjector ℂ (⇑b) s := rfl

/-- For an atypical index `i ∉ s`, the `some i` element of the Schumacher encoder is the reset
operator `Aᵢ = |b i₀⟩⟨bᵢ|`. -/
theorem schumacherEncoder_some_of_notMem (b : OrthonormalBasis ι ℂ H) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (i₀ : ι) :
    schumacherEncoder b s i₀ (some i) = (InnerProductSpace.rankOne ℂ (b i₀)) (b i) :=
  ite_eq_right hi

/-- For a typical index `i ∈ s`, the `some i` element of the Schumacher encoder vanishes (that basis
vector is already handled by the projector `P`). -/
theorem schumacherEncoder_some_of_mem (b : OrthonormalBasis ι ℂ H) {s : Finset ι} {i : ι}
    (hi : i ∈ s) (i₀ : ι) : schumacherEncoder b s i₀ (some i) = 0 :=
  ite_eq_left hi

/-- **Nielsen & Chuang, Eq. (12.55).** Every Schumacher operation element factors through the code
projector `P = ∑_{i ∈ s} |bᵢ⟩⟨bᵢ|`: `P · Eₒ = Eₒ`. The projector element (`none`) is idempotent
(`P · P = P`); a typical reset element (`some i ∈ s`) is `0`; and an atypical reset element
(`some i ∉ s`) is `|b i₀⟩⟨bᵢ|`, on which `P` acts as the identity because `i₀ ∈ s` fixes
`P (b i₀) = b i₀`. This is the compression condition satisfied by the projection–reset encoder, used
to build the code subspace of a compression scheme. -/
theorem orthonormalProjector_mul_schumacherEncoder (b : OrthonormalBasis ι ℂ H) (s : Finset ι)
    (i₀ : ι) (hi₀ : i₀ ∈ s) (o : Option ι) :
    InnerProductSpace.orthonormalProjector ℂ (⇑b) s * schumacherEncoder b s i₀ o
      = schumacherEncoder b s i₀ o := by
  cases o with
  | none =>
    rw [schumacherEncoder_none]
    exact InnerProductSpace.isIdempotentElem_orthonormalProjector b.orthonormal s
  | some i =>
    by_cases hi : i ∈ s
    · rw [schumacherEncoder_some_of_mem b hi, mul_zero]
    · rw [schumacherEncoder_some_of_notMem b hi, mul_def, InnerProductSpace.comp_rankOne,
        InnerProductSpace.orthonormalProjector_apply_eq_ite b.orthonormal s i₀, ite_eq_left hi₀]

variable [CompleteSpace H]

/-- The Schumacher encoder is a **trace-preserving** quantum operation: its operation elements
satisfy the completeness relation `∑ⱼ Eⱼ† Eⱼ = 1` (Nielsen & Chuang, §12.2.2). Each reset element
contributes `Aᵢ† Aᵢ = |bᵢ⟩⟨bᵢ|` (using `‖b i₀‖ = 1`), the projector contributes `P† P = P`, and
`P + ∑_{i ∉ s} |bᵢ⟩⟨bᵢ|` is the resolution of identity `∑ᵢ |bᵢ⟩⟨bᵢ| = 1` split across `s`
and `sᶜ`. -/
theorem schumacherEncoder_isTracePreserving (b : OrthonormalBasis ι ℂ H) (s : Finset ι) (i₀ : ι) :
    ∑ j, adjoint (schumacherEncoder b s i₀ j) * (schumacherEncoder b s i₀ j) = 1 := by
  rw [Fintype.sum_option]
  have hnone : adjoint (schumacherEncoder b s i₀ none) * (schumacherEncoder b s i₀ none)
      = InnerProductSpace.orthonormalProjector ℂ (⇑b) s := by
    have hp := InnerProductSpace.isStarProjection_orthonormalProjector b.orthonormal s
    rw [schumacherEncoder_none, ← star_eq_adjoint, hp.isSelfAdjoint]
    exact hp.isIdempotentElem
  have hsome : ∀ i,
      adjoint (schumacherEncoder b s i₀ (some i)) * (schumacherEncoder b s i₀ (some i))
      = if i ∈ s then 0 else (InnerProductSpace.rankOne ℂ (b i)) (b i) := by
    intro i
    by_cases hi : i ∈ s
    · rw [schumacherEncoder_some_of_mem b hi, ite_eq_left hi]; simp
    · rw [schumacherEncoder_some_of_notMem b hi, ite_eq_right hi, InnerProductSpace.adjoint_rankOne,
        mul_def, InnerProductSpace.rankOne_comp_rankOne,
        orthonormal_iff_ite.mp b.orthonormal i₀ i₀]
      simp
  rw [hnone, Finset.sum_congr rfl (fun i _ => hsome i), Finset.sum_ite, Finset.sum_const_zero,
    zero_add]
  have hfilter : (Finset.univ.filter (fun i => i ∉ s)) = sᶜ := by ext i; simp
  rw [hfilter, InnerProductSpace.orthonormalProjector_eq_sum,
    Finset.sum_add_sum_compl s (fun i => (InnerProductSpace.rankOne ℂ (b i)) (b i)),
    OrthonormalBasis.sum_rankOne_eq_id]
  rfl

omit [CompleteSpace H] in
/-- **Nielsen & Chuang, eq. (12.51).** The entanglement fidelity of the Schumacher encoder splits as
`F(ρ, C) = |tr(ρ P)|² + ∑_{i ∉ s} |tr(ρ Aᵢ)|²`, the code-projector term plus the reset-operator
terms. -/
theorem entanglementFidelity_schumacherEncoder (b : OrthonormalBasis ι ℂ H) (s : Finset ι)
    (i₀ : ι) (ρ : H →L[ℂ] H) :
    entanglementFidelity ρ (schumacherEncoder b s i₀)
      = ‖LinearMap.trace ℂ H
          ((ρ * InnerProductSpace.orthonormalProjector ℂ (⇑b) s : H →L[ℂ] H) : H →ₗ[ℂ] H)‖ ^ 2
        + ∑ i ∈ sᶜ, ‖LinearMap.trace ℂ H
          ((ρ * (InnerProductSpace.rankOne ℂ (b i₀)) (b i) : H →L[ℂ] H) : H →ₗ[ℂ] H)‖ ^ 2 := by
  rw [entanglementFidelity, Fintype.sum_option, schumacherEncoder_none]
  congr 1
  have hsome : ∀ i, ‖LinearMap.trace ℂ H
        ((ρ * schumacherEncoder b s i₀ (some i) : H →L[ℂ] H) : H →ₗ[ℂ] H)‖ ^ 2
      = if i ∈ s then 0 else ‖LinearMap.trace ℂ H
        ((ρ * (InnerProductSpace.rankOne ℂ (b i₀)) (b i) : H →L[ℂ] H) : H →ₗ[ℂ] H)‖ ^ 2 := by
    intro i
    by_cases hi : i ∈ s
    · rw [schumacherEncoder_some_of_mem b hi, ite_eq_left hi]; simp
    · rw [schumacherEncoder_some_of_notMem b hi, ite_eq_right hi]
  rw [Finset.sum_congr rfl (fun i _ => hsome i), Finset.sum_ite, Finset.sum_const_zero, zero_add]
  congr 1
  ext i; simp

omit [CompleteSpace H] in
/-- **Nielsen & Chuang, eq. (12.52).** The entanglement fidelity of the Schumacher encoder is
bounded below by `|tr(ρ P)|²`, the squared overlap of `ρ` with the code projector `P`: `P` is one of
the operation elements and the remaining reset-operator terms are nonnegative. This is the direct
(achievability) inequality of Schumacher's noiseless channel coding theorem: with `ρ = ρ^⊗ⁿ` and
`P = P(n, ε)` the typical subspace projector, part (1) of the typical subspace theorem gives
`tr(ρ^⊗ⁿ P) ≥ 1 − δ`, whence `F ≥ (1 − δ)²`. -/
theorem entanglementFidelity_schumacherEncoder_ge (b : OrthonormalBasis ι ℂ H) (s : Finset ι)
    (i₀ : ι) (ρ : H →L[ℂ] H) :
    ‖LinearMap.trace ℂ H ((ρ * InnerProductSpace.orthonormalProjector ℂ (⇑b) s : H →L[ℂ] H) :
          H →ₗ[ℂ] H)‖ ^ 2
      ≤ entanglementFidelity ρ (schumacherEncoder b s i₀) := by
  rw [entanglementFidelity, ← schumacherEncoder_none b s i₀]
  exact Finset.single_le_sum
    (f := fun j => ‖LinearMap.trace ℂ H ((ρ * schumacherEncoder b s i₀ j : H →L[ℂ] H) :
      H →ₗ[ℂ] H)‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ none)

end ContinuousLinearMap
