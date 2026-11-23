/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EntropyJointTheorem
import AxQM.Postulates.API.MutualInformation
import AxQM.Postulates.API.ArakiLiebEqualityConditions
import AxQM.Postulates.API.Qudit
import AxQM.Postulates.PartialTraceTensor
import AxQM.Postulates.API.EntropyConcavity
import AxQM.Postulates.API.EntropyEvolution
import AxQM.Postulates.API.EntropyComposite

/-!
# AxQM — the Holevo χ quantity and its classical–quantum representation

The **Holevo χ quantity** of an ensemble `{pₓ, ρₓ}` of quantum states (Nielsen & Chuang,
eq. (12.208)):

`χ ≡ S(ρ) − ∑ₓ pₓ S(ρₓ)`,   with `ρ = ∑ₓ pₓ ρₓ`,

is the amount by which the average component entropy falls short of the entropy of the mixture.
It is the central quantity of Chapter 12 (the Holevo bound, the HSW theorem) and of the
alternate proof of the Holevo bound (N&C Problem 12.1), whose engine is that `χ` **equals a
quantum mutual information**: attaching a classical *index register* `P` correlated with the
ensemble produces the **classical–quantum state**

`ρᴾ⁄ᔆ = ∑ₓ pₓ |x⟩⟨x|ᴾ ⊗ ρₓ`,

whose mutual information `S(P : S)` is exactly `χ`. This file supplies the following pieces:

* `State.holevoChi` — the χ quantity of an ensemble of states;
* `State.holevoCQState` — the classical–quantum state, with the classical register realised as the
  computational basis of `qudit (Fintype.card ι)` (a concrete register, so
  no abstract-register orthogonality hypothesis is needed);
* `State.holevoChi_eq_vonNeumannMutualInfo_holevoCQState` — the bridge `χ = S(P : S)`.

Elementary χ facts (used by the no-cloning argument, N&C Problem 12.2):

* `State.holevoChi_eq_sum_mul_quantumRelativeEntropy` — `χ = ∑ᵢ pᵢ D(ρᵢ ‖ μ)` (concavity gap);
* `State.holevoChi_nonneg` — `0 ≤ χ`;
* `State.holevoChi_of_forall_vonNeumannEntropy_zero` / `State.holevoChi_pure` — for a pure-state
  ensemble, `χ = S(μ)`.

Once `χ = S(P : S)`, N&C's Problem 12.1 follows from two facts:
discarding a subsystem cannot increase mutual information
(`State.vonNeumannMutualInfo_le_of_discard'`, part (1)) and a quantum operation on one factor
cannot increase it (Theorem 11.15(3), part (2)); those parts, and the apparatus construction of
part (3), are the subject of `AxQM/NC/Ch12/Problem12_1.lean`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem} {ι : Type*} [Fintype ι]
  (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S)

/-- The **Holevo χ quantity** of an ensemble `{pᵢ, ρᵢ}` (Nielsen & Chuang, eq. (12.208)):
`χ = S(∑ᵢ pᵢ ρᵢ) − ∑ᵢ pᵢ S(ρᵢ)`, the entropy of the mixture minus the average component entropy. -/
def State.holevoChi : ℝ :=
  (State.mix p hp hsum ρ).vonNeumannEntropy - ∑ i, p i * (ρ i).vonNeumannEntropy

/-- Unfolding lemma for the Holevo χ quantity: `χ = S(∑ᵢ pᵢ ρᵢ) − ∑ᵢ pᵢ S(ρᵢ)`. -/
theorem State.holevoChi_def :
    State.holevoChi p hp hsum ρ =
      (State.mix p hp hsum ρ).vonNeumannEntropy - ∑ i, p i * (ρ i).vonNeumannEntropy := rfl

/-- The **classical–quantum state** `∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ` associated to an ensemble `{pᵢ, ρᵢ}`
(Nielsen & Chuang Problem 12.1, the "extra system correlated with the ensemble"): the classical
index register is the computational basis `|i⟩` of `qudit (Fintype.card ι)`, tensored with the
corresponding ensemble state and mixed with weight `pᵢ`. Its mutual information between the
register and the system equals the Holevo χ (see
`State.holevoChi_eq_vonNeumannMutualInfo_holevoCQState`). -/
def State.holevoCQState : State (qudit (Fintype.card ι) ⊗ S) :=
  State.mix p hp hsum (fun i => (quditBasis (Fintype.equivFin ι i)).toState.tmul (ρ i))

/-- The system marginal of the classical–quantum state is the ensemble mixture: tracing out the
classical register `P` from `∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ` leaves `∑ᵢ pᵢ ρᵢ`. -/
theorem State.holevoCQState_reducedRight :
    (State.holevoCQState p hp hsum ρ).reducedRight = State.mix p hp hsum ρ := by
  unfold State.holevoCQState
  rw [State.reducedRight_mix]
  simp only [State.reducedRight_tmul]

/-- The von Neumann entropy of the classical–quantum state decomposes as the Shannon entropy of the
weights plus the average component entropy: `S(∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)`. This is
the joint entropy theorem `State.vonNeumannEntropy_jointEntropyTheorem` (N&C Theorem 11.8(5))
applied to the orthonormal register kets `|i⟩` (the computational basis of `qudit (Fintype.card ι)`
reindexed by `Fintype.equivFin`, orthonormal by `quditBasis_orthonormal`). -/
theorem State.vonNeumannEntropy_holevoCQState :
    (State.holevoCQState p hp hsum ρ).vonNeumannEntropy
      = Real.entropy p + ∑ i, p i * (ρ i).vonNeumannEntropy := by
  unfold State.holevoCQState
  exact State.vonNeumannEntropy_jointEntropyTheorem p hp hsum
    (fun i => quditBasis (Fintype.equivFin ι i)) (quditBasis_equivFin_orthonormal ι) ρ

/-- The register marginal of the classical–quantum state has entropy equal to the Shannon entropy
of the weights: `S(Tr_S (∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ)) = H(p)`. Tracing out `S` leaves the diagonal register
state `∑ᵢ pᵢ |i⟩⟨i|`, a mixture of the orthonormal pure states `|i⟩`; its entropy is `H(p)` by
`State.vonNeumannEntropy_mix_toState_orthonormal`. -/
theorem State.vonNeumannEntropy_reducedLeft_holevoCQState :
    (State.holevoCQState p hp hsum ρ).reducedLeft.vonNeumannEntropy = Real.entropy p := by
  unfold State.holevoCQState
  rw [State.reducedLeft_mix]
  simp only [State.reducedLeft_tmul]
  exact State.vonNeumannEntropy_mix_toState_orthonormal p hp hsum
    (fun i => quditBasis (Fintype.equivFin ι i)) (quditBasis_equivFin_orthonormal ι)

/-- **The Holevo χ quantity is a quantum mutual information** (Nielsen & Chuang Problem 12.1, the
key identity): for the classical–quantum state `∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ`, the mutual information between
the classical register `P` and the system `S` equals the Holevo χ,

`S(P : S) = χ = S(∑ᵢ pᵢ ρᵢ) − ∑ᵢ pᵢ S(ρᵢ)`.

The register marginal contributes `H(p)`, the system marginal `S(∑ᵢ pᵢ ρᵢ)`, and the joint state
`H(p) + ∑ᵢ pᵢ S(ρᵢ)`, so the `H(p)` terms cancel. This turns every χ-monotonicity statement of
Problem 12.1 into a mutual-information monotonicity statement already available in the library. -/
theorem State.holevoChi_eq_vonNeumannMutualInfo_holevoCQState :
    (State.holevoCQState p hp hsum ρ).vonNeumannMutualInfo = State.holevoChi p hp hsum ρ := by
  rw [State.vonNeumannMutualInfo_def, State.vonNeumannEntropy_reducedLeft_holevoCQState,
    State.holevoCQState_reducedRight, State.vonNeumannEntropy_holevoCQState, State.holevoChi_def]
  ring

/-- The Holevo χ quantity is the **average relative entropy to the mean**:
`χ = ∑ᵢ pᵢ D(ρᵢ ‖ μ)`, where `μ = ∑ⱼ pⱼ ρⱼ` is the average state. This is the concavity-gap form
of the entropy (Nielsen & Chuang Theorem 11.10), obtained from the mixing identity
`State.sum_mul_quantumRelativeEntropy_mix`. -/
theorem State.holevoChi_eq_sum_mul_quantumRelativeEntropy :
    State.holevoChi p hp hsum ρ
      = ∑ i, p i * (ρ i).quantumRelativeEntropy (State.mix p hp hsum ρ) := by
  rw [State.holevoChi_def]
  exact (State.sum_mul_quantumRelativeEntropy_mix p hp hsum ρ).symm

/-- The Holevo χ quantity is **non-negative**, `0 ≤ χ`. This is exactly concavity of the von
Neumann entropy, `∑ᵢ pᵢ S(ρᵢ) ≤ S(∑ᵢ pᵢ ρᵢ)`
(`State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix'`, the faithfulness-free form). -/
theorem State.holevoChi_nonneg : 0 ≤ State.holevoChi p hp hsum ρ := by
  rw [State.holevoChi_def, sub_nonneg]
  exact State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix' p hp hsum ρ

/-- If every component of the ensemble has zero von Neumann entropy (in particular, if every `ρᵢ` is
pure), the Holevo χ quantity **collapses to the entropy of the average state**, `χ = S(μ)`. -/
theorem State.holevoChi_of_forall_vonNeumannEntropy_zero
    (h : ∀ i, (ρ i).vonNeumannEntropy = 0) :
    State.holevoChi p hp hsum ρ = (State.mix p hp hsum ρ).vonNeumannEntropy := by
  simp [State.holevoChi_def, h]

/-- For an ensemble of **pure** states `{pᵢ, |ψᵢ⟩}` the Holevo χ quantity equals the von Neumann
entropy of the average state, `χ = S(∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|)`, since each pure state has zero entropy
(`PureState.vonNeumannEntropy_toState_eq_zero`). This is the form used in the no-cloning argument
(Nielsen & Chuang Problem 12.2). -/
theorem State.holevoChi_pure (ψ : ι → PureState S) :
    State.holevoChi p hp hsum (fun i => (ψ i).toState) =
      (State.mix p hp hsum (fun i => (ψ i).toState)).vonNeumannEntropy :=
  State.holevoChi_of_forall_vonNeumannEntropy_zero p hp hsum _
    (fun i => (ψ i).vonNeumannEntropy_toState_eq_zero)

/-- **The Holevo χ quantity is invariant under a unitary applied to every ensemble state**:
`χ(p, U ρ U†) = χ(p, ρ)`. Both the mixture entropy — `S(∑ᵢ pᵢ U ρᵢ U†) = S(U (∑ᵢ pᵢ ρᵢ) U†) =
S(∑ᵢ pᵢ ρᵢ)` via `State.evolve_mix` and the unitary invariance `State.vonNeumannEntropy_evolve` —
and each component entropy `S(U ρᵢ U†) = S(ρᵢ)` are unchanged. This is the "apply the unitary
interaction of the environment" step of the alternate Holevo-bound proof (N&C Problem 12.1(2)). -/
theorem State.holevoChi_evolve (U : Evolution S) :
    State.holevoChi p hp hsum (fun i => U.evolve (ρ i)) = State.holevoChi p hp hsum ρ := by
  rw [State.holevoChi_def, State.holevoChi_def, ← State.evolve_mix]
  simp only [State.vonNeumannEntropy_evolve]

/-- **The Holevo χ quantity is invariant under appending a fixed pure ancilla**:
`χ(p, ρᵢ ⊗ |ω⟩⟨ω|) = χ(p, ρ)`. Tensoring the pure state `ω` onto every component adds
`S(ω) = 0` to both the mixture entropy — `S((∑ᵢ pᵢ ρᵢ) ⊗ ω) = S(∑ᵢ pᵢ ρᵢ)` via `State.mix_tmul`
and additivity `State.vonNeumannEntropy_tmul` — and each component entropy, so χ is unchanged. This
is the "adjoin the environment in a pure state" step of the alternate Holevo-bound proof
(N&C Problem 12.1(2)). -/
theorem State.holevoChi_tmul_pure_right {C : QSystem} (ω : PureState C) :
    State.holevoChi p hp hsum (fun i => (ρ i).tmul ω.toState) = State.holevoChi p hp hsum ρ := by
  rw [State.holevoChi_def, State.holevoChi_def, ← State.mix_tmul]
  simp only [State.vonNeumannEntropy_tmul, PureState.vonNeumannEntropy_toState_eq_zero, add_zero]

/-- **The Holevo χ quantity is invariant under transporting every ensemble state along a system
isomorphism**: `χ(p, e ρᵢ e⁻¹) = χ(p, ρ)` for `e : S ≃ₛ T`. Transport commutes with mixing
(`State.congr_mix`, so `S(∑ᵢ pᵢ e ρᵢ e⁻¹) = S(e (∑ᵢ pᵢ ρᵢ) e⁻¹) = S(∑ᵢ pᵢ ρᵢ)`) and leaves the von
Neumann entropy unchanged (`State.vonNeumannEntropy_congr`), so both the mixture entropy and each
component entropy are unchanged. The `State.congr` companion of `State.holevoChi_evolve`; it lets a
χ-monotonicity statement be transported across a re-association or swap of the underlying systems
(e.g. `State.holevoChi_reducedRight_le`, tracing out the *left* factor via the swap isomorphism). -/
theorem State.holevoChi_congr {T : QSystem} (e : S.Iso T) :
    State.holevoChi p hp hsum (fun i => State.congr e (ρ i)) = State.holevoChi p hp hsum ρ := by
  rw [State.holevoChi_def, State.holevoChi_def, ← State.congr_mix]
  simp only [State.vonNeumannEntropy_congr]

/-- **The Holevo χ quantity is invariant under reindexing the ensemble by an equivalence**
`e : α ≃ β`: `χ(p ∘ e, ρ ∘ e) = χ(p, ρ)`. The χ depends on the ensemble only through its mixture and
its weighted-average component entropy, both finite sums invariant under bijective reindexing
(`Equiv.sum_comp`). The reindexing companion of `State.holevoChi_evolve` / `State.holevoChi_congr`;
it lets an ensemble indexed by an arbitrary finite type be moved to a `Fin n` index without changing
its χ value. -/
theorem State.holevoChi_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (p : β → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : β → State S)
    (hp' : ∀ i, 0 ≤ p (e i)) (hsum' : ∑ i, p (e i) = 1) :
    State.holevoChi (fun i => p (e i)) hp' hsum' (fun i => ρ (e i))
      = State.holevoChi p hp hsum ρ := by
  rw [State.holevoChi_def, State.holevoChi_def]
  congr 1
  · congr 1
    apply State.ext
    rw [State.mix_op, State.mix_op]
    exact Equiv.sum_comp e (fun k => (p k : ℂ) • (ρ k).op)
  · exact Equiv.sum_comp e (fun k => p k * (ρ k).vonNeumannEntropy)

end AxQM
