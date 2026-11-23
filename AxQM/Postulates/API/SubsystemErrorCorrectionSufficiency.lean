/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SubsystemErrorCorrectionProtection
import ToMathlib.Analysis.InnerProductSpace.RankOneProjector

/-!
# AxQM.Postulates.API — decoupling is sufficient to correct errors on a subsystem

**Nielsen & Chuang, Exercise 12.14** (p. 567), the *sufficiency* direction:

Sufficiency of the decoupling condition for correcting errors on a subsystem.

This file **assembles** the two halves proved in
`AxQM/Postulates/API/SubsystemErrorCorrectionDecoupling.lean` and
`AxQM/Postulates/API/SubsystemErrorCorrectionProtection.lean` into the exercise's conclusion. The
setup is N&C's information-theoretic picture of quantum error-correction: a code with orthonormal
codewords `w : ι → Q₁ ⊗ Q₂` and code projector `P = ∑ᵢ |wᵢ⟩⟨wᵢ|`, purified against a reference `R`
(of the same dimension `N = card ι` as the code) into the maximally-entangled `|RQ⟩ = (1/√N) ∑ₓ
|x⟩ ⊗ |wₓ⟩` (`codePurifyVec`), where `Q = Q₁ ⊗ Q₂` splits the coded system into the subsystem `Q₁`
on which errors occur and the remaining qubits `Q₂`. Compare the error-correction conditions in
`ToMathlib/Analysis/InnerProductSpace/QuantumErrorCorrection.lean` and N&C Theorem 10.1
(`AxQM/NC/Ch10/Theorem10_1.lean`).

## The assembly

Both halves characterise the *same* codeword-reduced-operator condition — the family
`σᵢⱼ := Tr_{Q₂} |wᵢ⟩⟨wⱼ|` is **scalar-diagonal**, `σᵢⱼ = if i = j then ρ₁ else 0` — so they chain:

* **decoupling side** (`codePurify_decoupledLeftFactor_iff`): the marginal decoupling
  `ρ^{RQ1} = ρ^R ⊗ ρ₁` holds **iff** `σ` is scalar-diagonal with diagonal block `ρ₁`;
* **protection side** (`protectsLeftFactor_iff_codewordReducedScalar`): the code
  **protects the left factor `Q₁`** — `∀ A, ∃ c, P (A ⊗ I) P = c • P` (`ProtectsLeftFactor P`) —
  **iff** `σ` is scalar-diagonal (for *some* `ρ₁`).

Threading `ρ₁ = ρ^{Q1}` through both gives `decoupledLeftFactor_protectsLeftFactor` (decoupling ⟹
`ProtectsLeftFactor P`). Feeding that into `ProtectsLeftFactor.satisfiesQECConditions` (N&C Theorem
10.1) yields the Knill–Laflamme conditions for the **complete `Q₁`-error family**
`{|a⟩⟨b| ⊗ I}` (`leftFactorErrorBasis`), and `satisfiesQECConditions_iff_exists_correction` /
`SatisfiesQECConditions.exists_correctionChannel` (N&C Theorem 10.1) turns those into an explicit
recovery — a trace-preserving recovery operation, and a genuine recovery **channel**, correcting
every error on `Q₁`. This is exactly N&C's claim that the decoupling condition is *sufficient* for
correction.

The claims are stated as separate theorems:
`decoupledLeftFactor_protectsLeftFactor`, `satisfiesQECConditions_of_decoupledLeftFactor`,
`exists_correction_of_decoupledLeftFactor` (Kraus form) and
`exists_correctionChannel_of_decoupledLeftFactor` (channel form).

## Route and fidelity

This is the **Knill–Laflamme route** to Exercise 12.14: rather than N&C's constructive
Schmidt-decomposition recovery (§12.4.2, Eqs. (12.137)–(12.141)), the decoupling condition is shown
equivalent to the code protecting `Q₁`, i.e. to the QEC conditions for the complete `Q₁`-error
family, whence correctability follows from the *already formalised* Theorem 10.1. "Correcting
arbitrary errors on `Q₁`" is faithfully rendered as correcting the complete family of `Q₁`-supported
operation elements `{|a⟩⟨b| ⊗ I_{Q₂}}` (`leftFactorErrorBasis`), which spans every operator on `Q₁`;
by the discretization of errors (`SatisfiesQECConditions.recombine`, Theorem 10.2) any error
process built from these is corrected by the same recovery.

The statement of Exercise 12.14 is in `AxQM/NC/Ch12/Exercise12_14.lean`.
-/

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

noncomputable section

namespace AxQM

section Projector

variable {ι : Type*} [Fintype ι] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The (unnormalised) code projector `P = ∑ᵢ |wᵢ⟩⟨wᵢ|` **is the orthonormal projector** onto the
span of `w`: `∑ i, |wᵢ⟩⟨wᵢ| = orthonormalProjector ℂ w Finset.univ` (Mathlib's
`InnerProductSpace.orthonormalProjector_eq_sum`, read backwards). The bridge that lets the code
projector inherit self-adjointness / idempotence from Mathlib's `orthonormalProjector` API. -/
theorem codewordProj_eq_orthonormalProjector (w : ι → H) :
    (∑ i, rankOne ℂ (w i) (w i)) = InnerProductSpace.orthonormalProjector ℂ w Finset.univ :=
  (InnerProductSpace.orthonormalProjector_eq_sum w Finset.univ).symm

/-- The code projector `P = ∑ᵢ |wᵢ⟩⟨wᵢ|` is **self-adjoint** (a Hermitian projector). -/
theorem codewordProj_isSelfAdjoint [CompleteSpace H] (w : ι → H) :
    IsSelfAdjoint (∑ i, rankOne ℂ (w i) (w i)) := by
  rw [codewordProj_eq_orthonormalProjector]
  exact InnerProductSpace.isSelfAdjoint_orthonormalProjector w Finset.univ

/-- The code projector `P = ∑ᵢ |wᵢ⟩⟨wᵢ|` of an **orthonormal** family is **idempotent**,
`P ∘L P = P` (an orthogonal projector). -/
theorem codewordProj_comp_self {w : ι → H} (hw : Orthonormal ℂ w) :
    (∑ i, rankOne ℂ (w i) (w i)) ∘L (∑ i, rankOne ℂ (w i) (w i)) = ∑ i, rankOne ℂ (w i) (w i) := by
  rw [codewordProj_eq_orthonormalProjector, ← ContinuousLinearMap.mul_def]
  exact InnerProductSpace.isIdempotentElem_orthonormalProjector hw Finset.univ

/-- The code projector `P = ∑ᵢ |wᵢ⟩⟨wᵢ|` of a **nonempty** orthonormal family is **nonzero**:
`P wᵢ = wᵢ ≠ 0`. -/
theorem codewordProj_ne_zero [Nonempty ι] {w : ι → H} (hw : Orthonormal ℂ w) :
    (∑ i, rankOne ℂ (w i) (w i)) ≠ 0 := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  intro h
  have happ : (∑ i, rankOne ℂ (w i) (w i)) (w i₀) = w i₀ := by
    rw [codewordProj_eq_orthonormalProjector,
      InnerProductSpace.orthonormalProjector_apply_eq_ite hw Finset.univ i₀,
      ite_eq_left (Finset.mem_univ i₀)]
  rw [h, _root_.zero_apply] at happ
  exact (hw.ne_zero i₀) happ.symm

end Projector

variable {Q₁ Q₂ : QSystem} {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **N&C Exercise 12.14 — decoupling implies the code protects `Q₁`.** For the maximally-mixed
code purification `|RQ⟩ = ∑ₓ eₓ ⊗ wₓ` on `R ⊗ (Q₁ ⊗ Q₂)` (`e` an orthonormal basis of the
`N = card ι`-dimensional reference `R`, `w` the orthonormal codewords), if the marginal
**decoupling** condition `ρ^{RQ1} = ρ^R ⊗ ρ₁` holds for the `Q₁`-state `ρ₁`, then the code projector
`P = ∑ᵢ |wᵢ⟩⟨wᵢ|` **protects the left factor `Q₁`** — `∀ A, ∃ c, P (A ⊗ I) P = c • P`
(`ProtectsLeftFactor P`).

The two companion equivalences turn on the *same* scalar-diagonal condition on the codeword reduced
operators `σᵢⱼ = Tr_{Q₂} |wᵢ⟩⟨wⱼ|`: decoupling ⟺ `σ` scalar-diagonal
(`codePurify_decoupledLeftFactor_iff`), and `ProtectsLeftFactor P` ⟺ `σ` scalar-diagonal
(`protectsLeftFactor_iff_codewordReducedScalar`). Threading `ρ₁` through both chains them. -/
theorem decoupledLeftFactor_protectsLeftFactor {R : Type*} [NormedAddCommGroup R]
    [InnerProductSpace ℂ R] [FiniteDimensional ℂ R] (e : OrthonormalBasis ι ℂ R)
    {κ κ' : Type*} [Fintype κ] [Fintype κ'] (bB : OrthonormalBasis κ ℂ Q₂.space)
    (bAB : OrthonormalBasis κ' ℂ (Q₁.space ⊗[ℂ] Q₂.space)) {w : ι → (Q₁ ⊗ Q₂).space}
    (hw : Orthonormal ℂ w) (ρ1 : Q₁.space →ₗ[ℂ] Q₁.space)
    (hdec : (Fintype.card ι : ℂ)⁻¹ • LinearMap.partialTraceRight bB
          ((TensorProduct.assoc ℂ R Q₁.space Q₂.space).symm.conj
            ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap)
        = TensorProduct.map
            ((Fintype.card ι : ℂ)⁻¹ • LinearMap.partialTraceRight bAB
              ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap) ρ1) :
    ProtectsLeftFactor (Q₂ := Q₂) (∑ i, rankOne ℂ (w i) (w i)) := by
  classical
  have hσ := (codePurify_decoupledLeftFactor_iff e bB bAB hw ρ1).mp hdec
  exact (protectsLeftFactor_iff_codewordReducedScalar bB w hw).mpr ⟨ρ1, hσ⟩

/-- **N&C Exercise 12.14 — decoupling implies the Knill–Laflamme conditions for the `Q₁`-errors.**
Under the decoupling condition `ρ^{RQ1} = ρ^R ⊗ ρ₁`, the code projector `P = ∑ᵢ |wᵢ⟩⟨wᵢ|` and the
complete `Q₁`-error family `leftFactorErrorBasis b = {|b a⟩⟨b c| ⊗ I_{Q₂}}` (all operation elements
supported on `Q₁`, `b` an orthonormal basis of `Q₁`) satisfy the quantum error-correction conditions
(`SatisfiesQECConditions`, N&C Theorem 10.1). This is `decoupledLeftFactor_protectsLeftFactor`
composed with `ProtectsLeftFactor.satisfiesQECConditions`; the code projector's self-adjointness and
nonvanishing are `codewordProj_isSelfAdjoint` / `codewordProj_ne_zero`. -/
theorem satisfiesQECConditions_of_decoupledLeftFactor {R : Type*} [NormedAddCommGroup R]
    [InnerProductSpace ℂ R] [FiniteDimensional ℂ R] (e : OrthonormalBasis ι ℂ R)
    {ιb : Type*} [Fintype ιb] (b : OrthonormalBasis ιb ℂ Q₁.space) {κ κ' : Type*} [Fintype κ]
    [Fintype κ'] (bB : OrthonormalBasis κ ℂ Q₂.space)
    (bAB : OrthonormalBasis κ' ℂ (Q₁.space ⊗[ℂ] Q₂.space)) {w : ι → (Q₁ ⊗ Q₂).space}
    (hw : Orthonormal ℂ w) (ρ1 : Q₁.space →ₗ[ℂ] Q₁.space)
    (hdec : (Fintype.card ι : ℂ)⁻¹ • LinearMap.partialTraceRight bB
          ((TensorProduct.assoc ℂ R Q₁.space Q₂.space).symm.conj
            ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap)
        = TensorProduct.map
            ((Fintype.card ι : ℂ)⁻¹ • LinearMap.partialTraceRight bAB
              ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap) ρ1) :
    SatisfiesQECConditions (∑ i, rankOne ℂ (w i) (w i)) (leftFactorErrorBasis (Q₂ := Q₂) b) := by
  classical
  exact (decoupledLeftFactor_protectsLeftFactor e bB bAB hw ρ1 hdec).satisfiesQECConditions
    (codewordProj_isSelfAdjoint w) (codewordProj_ne_zero hw) b

/-- **N&C Exercise 12.14 — decoupling is sufficient to correct errors on `Q₁`** (recovery
operator-sum form). Under the decoupling condition `ρ^{RQ1} = ρ^R ⊗ ρ₁`, there is a
**trace-preserving recovery** family `R` (`∑ₒ Rₒ† Rₒ = 1`) that **corrects** the complete
`Q₁`-error family `leftFactorErrorBasis b` on the code
(`ContinuousLinearMap.Corrects`): the composed noise-then-recovery returns every operator supported
on the code to a scalar multiple of itself. This is the sufficiency claimed in the exercise, via the
Knill–Laflamme characterisation `satisfiesQECConditions_iff_exists_correction` (N&C Theorem 10.1)
applied to `satisfiesQECConditions_of_decoupledLeftFactor`. -/
theorem exists_correction_of_decoupledLeftFactor {R : Type*} [NormedAddCommGroup R]
    [InnerProductSpace ℂ R] [FiniteDimensional ℂ R] (e : OrthonormalBasis ι ℂ R)
    {ιb : Type} [Fintype ιb] (b : OrthonormalBasis ιb ℂ Q₁.space) {κ κ' : Type*} [Fintype κ]
    [Fintype κ'] (bB : OrthonormalBasis κ ℂ Q₂.space)
    (bAB : OrthonormalBasis κ' ℂ (Q₁.space ⊗[ℂ] Q₂.space)) {w : ι → (Q₁ ⊗ Q₂).space}
    (hw : Orthonormal ℂ w) (ρ1 : Q₁.space →ₗ[ℂ] Q₁.space)
    (hdec : (Fintype.card ι : ℂ)⁻¹ • LinearMap.partialTraceRight bB
          ((TensorProduct.assoc ℂ R Q₁.space Q₂.space).symm.conj
            ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap)
        = TensorProduct.map
            ((Fintype.card ι : ℂ)⁻¹ • LinearMap.partialTraceRight bAB
              ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap) ρ1) :
    ∃ (γ : Type) (_ : Fintype γ) (Rec : γ → (Q₁ ⊗ Q₂).space →L[ℂ] (Q₁ ⊗ Q₂).space),
      (∑ o, ContinuousLinearMap.adjoint (Rec o) ∘L Rec o = 1) ∧
        ContinuousLinearMap.Corrects (∑ i, rankOne ℂ (w i) (w i))
          (leftFactorErrorBasis (Q₂ := Q₂) b) Rec := by
  classical
  exact (satisfiesQECConditions_iff_exists_correction (codewordProj_isSelfAdjoint w)
      (codewordProj_comp_self hw) (codewordProj_ne_zero hw)).mp
    (satisfiesQECConditions_of_decoupledLeftFactor e b bB bAB hw ρ1 hdec)

/-- **N&C Exercise 12.14 — decoupling yields a recovery channel correcting the `Q₁`-errors**
(channel form). Under the decoupling condition `ρ^{RQ1} = ρ^R ⊗ ρ₁`, there is a genuine quantum
recovery **channel** `rec : State (Q₁ ⊗ Q₂) → State (Q₁ ⊗ Q₂)` (`IsChannel`, with Kraus family `R`)
and a single state-independent constant `λ ≥ 0` such that for every code state `ρ`
(`P ρ P = ρ`) the composed noise-then-recovery returns `ρ` to the same scalar multiple of itself,
`R(E(ρ)) = λ • ρ` — the hallmark of genuine error-correction
(`SatisfiesQECConditions.exists_correctionChannel`, N&C Theorem 10.1). -/
theorem exists_correctionChannel_of_decoupledLeftFactor {R : Type*} [NormedAddCommGroup R]
    [InnerProductSpace ℂ R] [FiniteDimensional ℂ R] (e : OrthonormalBasis ι ℂ R)
    {ιb : Type} [Fintype ιb] (b : OrthonormalBasis ιb ℂ Q₁.space) {κ κ' : Type*} [Fintype κ]
    [Fintype κ'] (bB : OrthonormalBasis κ ℂ Q₂.space)
    (bAB : OrthonormalBasis κ' ℂ (Q₁.space ⊗[ℂ] Q₂.space)) {w : ι → (Q₁ ⊗ Q₂).space}
    (hw : Orthonormal ℂ w) (ρ1 : Q₁.space →ₗ[ℂ] Q₁.space)
    (hdec : (Fintype.card ι : ℂ)⁻¹ • LinearMap.partialTraceRight bB
          ((TensorProduct.assoc ℂ R Q₁.space Q₂.space).symm.conj
            ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap)
        = TensorProduct.map
            ((Fintype.card ι : ℂ)⁻¹ • LinearMap.partialTraceRight bAB
              ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap) ρ1) :
    ∃ (γ : Type) (_ : Fintype γ) (Rec : γ → (Q₁ ⊗ Q₂).space →L[ℂ] (Q₁ ⊗ Q₂).space)
      (rec : State (Q₁ ⊗ Q₂) → State (Q₁ ⊗ Q₂)),
      IsChannel rec ∧
        (∀ ρ : State (Q₁ ⊗ Q₂), (rec ρ).op = ContinuousLinearMap.krausSumₗ Rec ρ.op) ∧
          ∃ lam : ℝ, 0 ≤ lam ∧ ∀ ρ : State (Q₁ ⊗ Q₂),
            (∑ i, rankOne ℂ (w i) (w i)) ∘L ρ.op ∘L (∑ i, rankOne ℂ (w i) (w i)) = ρ.op →
              ContinuousLinearMap.krausSumₗ Rec
                  (ContinuousLinearMap.krausSumₗ (leftFactorErrorBasis (Q₂ := Q₂) b) ρ.op)
                = (lam : ℂ) • ρ.op := by
  classical
  exact (satisfiesQECConditions_of_decoupledLeftFactor e b bB bAB hw ρ1 hdec)
    |>.exists_correctionChannel (codewordProj_isSelfAdjoint w) (codewordProj_comp_self hw)
      (codewordProj_ne_zero hw)

end AxQM
