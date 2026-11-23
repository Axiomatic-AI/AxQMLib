/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Qubit
import AxQM.Postulates.API.MaximallyMixed
import AxQM.Postulates.API.QuantumChannel
import AxQM.Concrete.PauliAverage

/-!
# AxQM.Postulates.API — completely depolarizing qubit channel (Pauli operation elements)

The **completely depolarizing channel** on a single qubit is the noise process that discards all
information: whatever the input state `ρ`, the output is the completely randomized (maximally
mixed) state `I/2`. This file constructs its **operation elements (Kraus operators)** — the object
Nielsen & Chuang, Exercise 10.11 asks for — and proves they realise the constant map `ρ ↦ I/2`.

The **answer** delivered here is the qubit *Pauli* construction (N&C eq. 8.101, the `p = 1` case of
the depolarizing channel `E(ρ) = (1-p)ρ + p(I/2)`): the four operation elements

`E₀ = ½ I`,   `E₁ = ½ X`,   `E₂ = ½ Y`,   `E₃ = ½ Z`,

one half of each Pauli. Their operator sum is the qubit *Pauli twirl*
`∑ₖ Eₖ ρ Eₖ† = ¼(ρ + XρX + YρY + ZρZ) = (tr ρ / 2) I = I/2`
(using `tr ρ = 1`), and their completeness relation is `∑ₖ Eₖ† Eₖ = ¼·4·I = I` (each Pauli is a
self-adjoint involution), so `E` is a genuine trace-preserving quantum channel.

* `AxQM.pauliFamilyOp` — the four Pauli operators `σ₀ = I, σ₁ = X, σ₂ = Y, σ₃ = Z` on the
  qubit as a family indexed by `Fin 4`, with `pauliFamilyOp_selfAdjoint` (each is self-adjoint) and
  `pauliFamilyOp_mul_self` (each is an involution, `σₖ² = I`).
* `AxQM.sum_pauliFamilyOp_conj` — **the operator-level qubit Pauli twirl**
  `∑ₖ σₖ T σₖ = (2 · tr T) · I` for any operator `T`, transported from the concrete `2×2` matrix
  identity `Concrete.pauliConjSum_eq` through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`.
* `AxQM.completelyDepolarizingKraus` — **the operation elements** `Eₖ = ½ σₖ`, with the
  **completeness relation** `completelyDepolarizingKraus_completeness` (`∑ₖ Eₖ† Eₖ = I`) and the
  **operator sum** `completelyDepolarizingKraus_krausSum` (`∑ₖ Eₖ ρ Eₖ† = I/2` for every state `ρ`).
* `AxQM.completelyDepolarizingChannel` — the induced state-map `ρ ↦ ∑ₖ Eₖ ρ Eₖ†`, a genuine
  `State qubit → State qubit`; the consequences (it is an `IsChannel`, and it maps
  every state to `I/2`) are stated in `AxQM/NC/Ch10/Exercise10_11.lean`.

Compare `RandomUnitaryChannel`, `maximallyMixedState`, and the generalized
depolarizing channel `genDepolarizingKraus`. `AxQM/NC/Ch10/Exercise10_11.lean` states the
consequences for `IsChannel` and `maximallyMixedState`.

## Design notes

* **Why the Pauli construction, not the design unitaries.** The completely depolarizing channel is
  the `p = 1` case of the general depolarizing channel `genDepolarizingChannel` (whose operator-sum
  uses the `2ᵈ d!` depolarizing-design unitaries). For a *single qubit* the physically natural and
  textbook answer (N&C's §10.3 Pauli-error framing, eq. 8.101) is the four Pauli operation elements
  `½ σₖ`; this file gives that construction directly, reusing the concrete Pauli twirl
  `Concrete.pauliConjSum_eq` rather than specialising the design-unitary machinery.
* **Strength.** The map is proved to send *every* state `ρ` to `I/2` (not merely to fix `I/2`,
  which is unitality) — the full content of the exercise.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The four Pauli operators of the qubit** `σ₀ = I, σ₁ = X, σ₂ = Y, σ₃ = Z`, as a family
indexed by `Fin 4`. `σ₀` is the identity operator; `σ₁, σ₂, σ₃` are the operators of the Pauli
`X, Y, Z` observables. These are the (unnormalised) operation elements of the completely
depolarizing channel, scaled by `½` in `completelyDepolarizingKraus`. -/
def pauliFamilyOp : Fin 4 → qubit.space →L[ℂ] qubit.space
  | 0 => 1
  | 1 => pauliXObservable.op
  | 2 => pauliYObservable.op
  | 3 => pauliZObservable.op

/-- Each Pauli operator is **self-adjoint** (`σₖ† = σₖ`): the identity is self-adjoint, and the
Pauli `X, Y, Z` observables are self-adjoint by construction (`Observable.selfAdjoint`). -/
theorem pauliFamilyOp_selfAdjoint (k : Fin 4) : IsSelfAdjoint (pauliFamilyOp k) := by
  fin_cases k
  · exact IsSelfAdjoint.one _
  · exact pauliXObservable.selfAdjoint
  · exact pauliYObservable.selfAdjoint
  · exact pauliZObservable.selfAdjoint

/-- Each Pauli operator is an **involution** `σₖ² = I`: trivial for the identity, and the
involution property of the Pauli `X, Y, Z` observables (`pauliXObservable_op_mul_self`, …). -/
theorem pauliFamilyOp_mul_self (k : Fin 4) : pauliFamilyOp k * pauliFamilyOp k = 1 := by
  fin_cases k
  · exact one_mul 1
  · exact pauliXObservable_op_mul_self
  · exact pauliYObservable_op_mul_self
  · exact pauliZObservable_op_mul_self

/-- **The operator-level qubit Pauli twirl** `∑ₖ σₖ T σₖ = (2 · tr T) · I` for any operator `T` on
the qubit (the identity term contributes `T`, so the sum is `T + XTX + YTY + ZTZ`). This is the
concrete `2×2` matrix identity `Concrete.pauliConjSum_eq` (`A + XAX + YAY + ZAZ = (2·tr A)·I`)
transported through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`, using
`Matrix.trace_toEuclideanCLM` to identify the operator trace with the matrix trace. It is the engine
of the completely depolarizing channel's operator sum. -/
theorem sum_pauliFamilyOp_conj (T : qubit.space →L[ℂ] qubit.space) :
    ∑ k, pauliFamilyOp k * T * pauliFamilyOp k
      = (2 * LinearMap.trace ℂ qubit.space (T : qubit.space →ₗ[ℂ] qubit.space)) • 1 := by
  obtain ⟨A, rfl⟩ := EquivLike.surjective (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) T
  rw [Fin.sum_univ_four]
  simp only [pauliFamilyOp, one_mul, mul_one, pauliXObservable_op, pauliYObservable_op,
    pauliZObservable_op]
  have h := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) (Concrete.pauliConjSum_eq A)
  simp only [map_add, map_mul, map_smul, map_one] at h
  exact h.trans (congrArg (fun t => (2 * t) • (1 : qubit.space →L[ℂ] qubit.space))
    (Matrix.trace_toEuclideanCLM A).symm)

/-- **The operation elements of the completely depolarizing qubit channel** (Nielsen & Chuang,
Exercise 10.11): `Eₖ = ½ σₖ`, one half of each Pauli `σ₀ = I, σ₁ = X, σ₂ = Y, σ₃ = Z`. Their
operator sum sends every state to `I/2` (`completelyDepolarizingKraus_krausSum`) and they satisfy
the completeness relation `∑ₖ Eₖ† Eₖ = I` (`completelyDepolarizingKraus_completeness`). -/
def completelyDepolarizingKraus (k : Fin 4) : qubit.space →L[ℂ] qubit.space :=
  ((1 / 2 : ℝ) : ℂ) • pauliFamilyOp k

/-- Each operation element is **self-adjoint**: `Eₖ† = (½ σₖ)† = ½ σₖ† = ½ σₖ = Eₖ` (the scalar `½`
is real, `σₖ` is self-adjoint). -/
theorem completelyDepolarizingKraus_selfAdjoint (k : Fin 4) :
    adjoint (completelyDepolarizingKraus k) = completelyDepolarizingKraus k := by
  rw [completelyDepolarizingKraus, ← star_eq_adjoint, star_smul,
    isSelfAdjoint_iff.mp (pauliFamilyOp_selfAdjoint k), Complex.star_def, Complex.conj_ofReal]

/-- **The completeness relation** `∑ₖ Eₖ† Eₖ = I` for the completely depolarizing operation
elements (Nielsen & Chuang's trace condition, certifying `E` is trace preserving). Each element is
self-adjoint and `Eₖ² = (½)² σₖ² = ¼ I`, so the sum is `4 · (¼ I) = I`. -/
theorem completelyDepolarizingKraus_completeness :
    ∑ k, (adjoint (completelyDepolarizingKraus k)).comp (completelyDepolarizingKraus k) = 1 := by
  have hterm : ∀ k, (adjoint (completelyDepolarizingKraus k)).comp (completelyDepolarizingKraus k)
      = ((1 / 4 : ℝ) : ℂ) • 1 := by
    intro k
    rw [completelyDepolarizingKraus_selfAdjoint, completelyDepolarizingKraus, smul_comp, comp_smul,
      smul_smul, ← ContinuousLinearMap.mul_def, pauliFamilyOp_mul_self]
    rw [← Complex.ofReal_mul]
    norm_num
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

/-- **The operator sum of the completely depolarizing operation elements is `I/2`** (Nielsen &
Chuang, Exercise 10.11): for *every* state `ρ`, `∑ₖ Eₖ ρ Eₖ† = I/2 = maximallyMixedState qubit`.
Each element being self-adjoint, `Eₖ ρ Eₖ† = ¼ σₖ ρ σₖ`, so the sum is `¼ ∑ₖ σₖ ρ σₖ = ¼ (2 tr ρ) I
= I/2` by the Pauli twirl `sum_pauliFamilyOp_conj` and `tr ρ = 1`. This is the completely
randomizing action the exercise asks for. -/
theorem completelyDepolarizingKraus_krausSum (ρ : State qubit) :
    krausSumₗ completelyDepolarizingKraus ρ.op = (maximallyMixedState qubit).op := by
  rw [krausSumₗ_apply]
  have hterm : ∀ k, (completelyDepolarizingKraus k).comp
      (ρ.op.comp (adjoint (completelyDepolarizingKraus k)))
      = ((1 / 4 : ℝ) : ℂ) • (pauliFamilyOp k * ρ.op * pauliFamilyOp k) := by
    intro k
    rw [completelyDepolarizingKraus_selfAdjoint, completelyDepolarizingKraus, smul_comp, comp_smul,
      comp_smul, smul_smul, ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def,
      ← mul_assoc, ← Complex.ofReal_mul]
    congr 1
    norm_num
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.smul_sum, sum_pauliFamilyOp_conj,
    State.trace_op_eq_one, maximallyMixedState_op, finrank_qubit_space, smul_smul]
  norm_num

/-- **The completely depolarizing qubit channel** `E(ρ) = ∑ₖ Eₖ ρ Eₖ†` as a state map, the operator
sum of the Pauli operation elements `completelyDepolarizingKraus`. It is a genuine `State qubit →
State qubit`: the operator sum of a completeness-satisfying Kraus family sends density operators to
density operators (`isDensityOp_krausSumₗ`). That it is a CPTP channel
mapping every state to `I/2` is the statement in
`AxQM/NC/Ch10/Exercise10_11.lean`. -/
def completelyDepolarizingChannel (ρ : State qubit) : State qubit where
  op := krausSumₗ completelyDepolarizingKraus ρ.op
  isDensity :=
    isDensityOp_krausSumₗ completelyDepolarizingKraus completelyDepolarizingKraus_completeness
      ρ.isDensity

/-- The operator of the completely depolarizing channel is the Kraus sum `∑ₖ Eₖ ρ Eₖ†`. -/
@[simp]
theorem completelyDepolarizingChannel_op (ρ : State qubit) :
    (completelyDepolarizingChannel ρ).op = krausSumₗ completelyDepolarizingKraus ρ.op := rfl

end AxQM
