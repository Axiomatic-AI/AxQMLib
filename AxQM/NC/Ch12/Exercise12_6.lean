/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.FidelityPiTensor
import AxQM.Postulates.API.RotationYColumn
import AxQM.Postulates.API.PurificationInvariance
import AxQM.Postulates.API.ControlledRotation
import AxQM.Postulates.API.ControlledControlledUnitary
import Mathlib.InformationTheory.Hamming

/-!
# Nielsen & Chuang, Exercise 12.6 — the coefficients `C_X` of Schumacher's Box 12.4

Give explicit C_X for Box 12.4; construct circuit for U_n; count elementary ops.
operations do you require, as a function of `n`?  (N&C §12.2.2, Box 12.4, p. 546–547)

**Box 12.4 (Schumacher compression).** An i.i.d. qubit source produces `|ψ₀⟩ = |0⟩` or
`|ψ₁⟩ = (|0⟩ + |1⟩)/√2 = |+⟩` with equal probabilities. Its density operator
`ρ = ¼ !![3, 1; 1, 1]` has orthonormal eigen-decomposition `p|0̄⟩⟨0̄| + (1−p)|1̄⟩⟨1̄|`, where the
**typical basis** is the `π/8`-rotation of the computational basis,
`|0̄⟩ = cos(π/8)|0⟩ + sin(π/8)|1⟩`, `|1̄⟩ = −sin(π/8)|0⟩ + cos(π/8)|1⟩` (i.e. `|b̄⟩ = R_y(π/4)|b⟩`).
A block of `n` source qubits is expanded in the product typical basis `{|X⟩ = |x₁…xₙ⟩}` (each
`xᵢ ∈ {0̄, 1̄}`) as `∑_X C_X |X⟩`, and — this is the compression idea — the coefficient `C_X` decays
exponentially in the Hamming weight of `X`, so only the low-weight (typical) `|X⟩` carry appreciable
weight.

## The three parts, and which are formalisable

Its **first part carries a genuine, verifiable proposition** — the "explicit expression for
`C_X`" — which we formalise here. (Compare Exercise 12.1, which has a real existence claim.) The
other two parts are construction/counting prompts with no proposition to state:

* **Part 1 (`C_X`) — formalised.** For a source block `|Ψ⟩ = |ψ_{k₁}⟩ ⊗ ⋯ ⊗ |ψ_{kₙ}⟩` (an arbitrary
  realisation `k : Fin n → Fin 2` of the source) and a typical-basis label `X = x₁…xₙ`
  (`x : Fin n → Fin 2`), the coefficient is `C_X = ⟨X | Ψ⟩ = ∏ᵢ ⟨x̄ᵢ | ψ_{kᵢ}⟩`
  (`schumacherBlock_overlap`, by multilinearity of the inner product). The single-qubit amplitudes
  are `⟨0̄ | ψ_k⟩ = cos(π/8)` and `⟨1̄ | ψ_k⟩ = ∓sin(π/8)` — **the same magnitude for both source
  states `k`** (`schumacherTypicalKet_overlap_sourceKet`). Hence the **magnitude** of `C_X` is
  source-independent and decays with the Hamming weight `w(X)` of the label (the number of `1̄`
  entries):

  `|C_X| = F(|X⟩, |Ψ⟩) = cos(π/8)^{n − w(X)} · sin(π/8)^{w(X)}`  (`schumacherBlock_fidelity`),

  expressed through the fidelity `F(|φ⟩, |χ⟩) = ‖⟨φ | χ⟩‖`. This is exactly the box's
  observation that "for `X` with large Hamming weight, the coefficients `C_X` are very small",
  since `sin(π/8) < cos(π/8)`.

* **Part 2 (circuit for `Uₙ`) — not formalised.** "Describe how to construct a quantum circuit"
  to lexicographically re-order the `2ⁿ` basis states by Hamming weight (packing the typical
  subspace into the first `≈ nH(p)` qubits). An open-ended synthesis prompt with no specified
  circuit or canonical proposition; a permutation-sorting network can be built from controlled-NOT
  gates (the library has the multiply-controlled-NOT apparatus, e.g. `Evolution.placedMcNot`), but
  the exercise asks for a *description*, not a named claim.

* **Part 3 (elementary-operation count) — not formalised.** "How many elementary operations … as
  a function of `n`?" is an asymptotic gate-count estimate with no unique closed form (it depends on
  the chosen realisation of `Uₙ`); there is no verifiable equality to state.

## Contents

The formalisation of Part 1 is here, stated with `PureState`, `Evolution`, `overlap` and
`fidelity`:

* `schumacherTypicalKet`, `schumacherSourceKet` — the typical basis `|b̄⟩` and sources `|ψ_k⟩`;
* `schumacherTypicalKet_overlap_sourceKet` / `_fidelity_sourceKet` — the single-qubit amplitudes and
  their (source-independent) magnitudes;
* `schumacherBlock_overlap` — the exact block coefficient `C_X = ∏ᵢ ⟨x̄ᵢ | ψ_{kᵢ}⟩`;
* `schumacherBlock_fidelity` — the headline `|C_X| = cos(π/8)^{n−w} sin(π/8)^{w}`.

The proofs use `PureState.overlap_piTensor` / `fidelity_piTensor`
(`AxQM/Postulates/API/FidelityPiTensor.lean`, product amplitudes factorize) and the
`ŷ`-rotation column lemmas (`AxQM/Postulates/API/RotationYColumn.lean`).

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.2.2, Box 12.4, Exercise 12.6.
-/

open scoped InnerProductSpace BigOperators

noncomputable section

namespace AxQM

/-- **The Schumacher typical basis of Box 12.4:** `|b̄⟩ = R_y(π/4)|b⟩`, i.e.
`|0̄⟩ = cos(π/8)|0⟩ + sin(π/8)|1⟩` and `|1̄⟩ = −sin(π/8)|0⟩ + cos(π/8)|1⟩`, the orthonormal
eigenbasis of the source density operator `ρ = ¼!![3,1;1,1]`. -/
def schumacherTypicalKet (b : Fin 2) : PureState qubit :=
  (rotYGate (Real.pi / 4)).evolvePure (qubitBasis b)

/-- **The Schumacher source states of Box 12.4:** `|ψ₀⟩ = |0⟩` and
`|ψ₁⟩ = R_y(π/2)|0⟩ = (|0⟩ + |1⟩)/√2 = |+⟩`, emitted with equal probabilities. -/
def schumacherSourceKet : Fin 2 → PureState qubit :=
  ![qubitBasis 0, (rotYGate (Real.pi / 2)).evolvePure (qubitBasis 0)]

/-- `|ψ₀⟩ = |0⟩`, rewritten as `R_y(π/4)` applied to `R_y(−π/4)|0⟩` (`R_y(π/4)·R_y(−π/4) = 1`), the
form in which the amplitude against `|b̄⟩ = R_y(π/4)|b⟩` reduces by unitary invariance. -/
theorem schumacherSourceKet_zero_eq :
    schumacherSourceKet 0 = (rotYGate (Real.pi / 4)).evolvePure
      ((rotYGate (-(Real.pi / 4))).evolvePure (qubitBasis 0)) := by
  rw [← Evolution.evolvePure_comp, rotYGate_comp, add_neg_cancel, rotYGate_zero,
    Evolution.id_evolvePure]
  simp [schumacherSourceKet]

/-- `|ψ₁⟩ = R_y(π/2)|0⟩`, rewritten as `R_y(π/4)` applied to `R_y(π/4)|0⟩` (`R_y(π/4)·R_y(π/4) =
R_y(π/2)`), the form in which the amplitude against `|b̄⟩ = R_y(π/4)|b⟩` reduces by unitary
invariance. -/
theorem schumacherSourceKet_one_eq :
    schumacherSourceKet 1 = (rotYGate (Real.pi / 4)).evolvePure
      ((rotYGate (Real.pi / 4)).evolvePure (qubitBasis 0)) := by
  rw [← Evolution.evolvePure_comp, rotYGate_comp,
    show Real.pi / 4 + Real.pi / 4 = Real.pi / 2 by ring]
  simp [schumacherSourceKet]

/-- **The single-qubit amplitudes `⟨b̄ | ψ_k⟩` of Box 12.4.** The overlap of the typical-basis state
`|b̄⟩` with a source state `|ψ_k⟩` is `cos(π/8)` for `b = 0̄` and `∓sin(π/8)` for `b = 1̄` (the sign
`−` for `k = 0`, `+` for `k = 1`). The key structural fact — *the magnitude is the same for both
source states `k`* — is what makes `|C_X|` depend only on the label `X`. Proved by writing both
`|b̄⟩` and `|ψ_k⟩` as `R_y(π/4)` applied to a computational state and using unitary invariance of
the overlap (`Evolution.overlap_evolvePure`) plus the `ŷ`-rotation amplitudes
(`rotYGate_evolvePure_qubitBasisZero_overlap`). -/
theorem schumacherTypicalKet_overlap_sourceKet (b k : Fin 2) :
    (schumacherTypicalKet b).overlap (schumacherSourceKet k)
      = if b = 0 then (Real.cos (Real.pi / 8) : ℂ)
        else if k = 0 then -(Real.sin (Real.pi / 8) : ℂ) else (Real.sin (Real.pi / 8) : ℂ) := by
  unfold schumacherTypicalKet
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · rw [schumacherSourceKet_zero_eq, Evolution.overlap_evolvePure,
      rotYGate_evolvePure_qubitBasisZero_overlap,
      show -(Real.pi / 4) / 2 = -(Real.pi / 8) by ring, Real.cos_neg, Real.sin_neg,
      Complex.ofReal_neg]
    simp
  · rw [schumacherSourceKet_one_eq, Evolution.overlap_evolvePure,
      rotYGate_evolvePure_qubitBasisZero_overlap, show Real.pi / 4 / 2 = Real.pi / 8 by ring]
    simp

/-- **The single-qubit magnitudes `|⟨b̄ | ψ_k⟩| = F(|b̄⟩, |ψ_k⟩)` of Box 12.4.** The fidelity of the
typical-basis state `|b̄⟩` with a source state `|ψ_k⟩` is `cos(π/8)` for `b = 0̄` and `sin(π/8)` for
`b = 1̄`, **independent of the source label `k`** (N&C: `|⟨0̄|ψ_k⟩| = cos(π/8)` is much larger than
`|⟨1̄|ψ_k⟩| = sin(π/8)`). The magnitude of `schumacherTypicalKet_overlap_sourceKet` via
`F = ‖overlap‖`, with `cos(π/8), sin(π/8) ≥ 0`. -/
theorem schumacherTypicalKet_fidelity_sourceKet (b k : Fin 2) :
    (schumacherTypicalKet b).toState.fidelity (schumacherSourceKet k).toState
      = if b = 0 then Real.cos (Real.pi / 8) else Real.sin (Real.pi / 8) := by
  rw [State.fidelity_toState_toState, ← PureState.overlap_def,
    schumacherTypicalKet_overlap_sourceKet]
  have hc : (0 : ℝ) ≤ Real.cos (Real.pi / 8) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hs : (0 : ℝ) ≤ Real.sin (Real.pi / 8) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  fin_cases b <;> fin_cases k <;> simp [norm_neg]

/-- **The exact block coefficient `C_X` of Box 12.4.** For a source block
`|Ψ⟩ = |ψ_{k₁}⟩ ⊗ ⋯ ⊗ |ψ_{kₙ}⟩` and a typical-basis label `X = x₁…xₙ`, the coefficient
`C_X = ⟨X | Ψ⟩` factorizes over the tensor factors as the product of the single-qubit amplitudes,
`C_X = ∏ᵢ ⟨x̄ᵢ | ψ_{kᵢ}⟩` — the "explicit expression for `C_X` in terms of `X`" the exercise asks
for (each factor given explicitly by `schumacherTypicalKet_overlap_sourceKet`). Immediate from
`PureState.overlap_piTensor` (multilinearity of the inner product). -/
theorem schumacherBlock_overlap {n : ℕ} (x k : Fin n → Fin 2) :
    (PureState.piTensor fun i => schumacherTypicalKet (x i)).overlap
        (PureState.piTensor fun i => schumacherSourceKet (k i))
      = ∏ i, (schumacherTypicalKet (x i)).overlap (schumacherSourceKet (k i)) :=
  PureState.overlap_piTensor _ _

/-- **Nielsen & Chuang, Exercise 12.6 (Box 12.4): the magnitude of the block coefficient `C_X`.**
For a source block `|Ψ⟩ = |ψ_{k₁}⟩ ⊗ ⋯ ⊗ |ψ_{kₙ}⟩` (any realisation `k : Fin n → Fin 2` of the
source) and a typical-basis label `X = x₁…xₙ` (`x : Fin n → Fin 2`), the magnitude of the
coefficient `C_X = ⟨X | Ψ⟩` is

`|C_X| = F(|X⟩, |Ψ⟩) = cos(π/8)^{n − w(X)} · sin(π/8)^{w(X)}`,

where `w(X) = hammingNorm x` is the Hamming weight of the label (the number of `1̄` entries). The
magnitude is **independent of the source realisation `k`** and decays exponentially in `w(X)` (since
`sin(π/8) < cos(π/8)`): this is precisely the box's statement that the coefficients `C_X` are very
small for `X` of large Hamming weight, hence only the low-weight (typical) labels carry appreciable
weight — the basis of Schumacher compression.

Proof: `PureState.fidelity_piTensor` factorizes `F(|X⟩, |Ψ⟩) = ∏ᵢ F(|x̄ᵢ⟩, |ψ_{kᵢ}⟩)`; each factor
is `cos(π/8)` or `sin(π/8)` per `schumacherTypicalKet_fidelity_sourceKet` (independent of `kᵢ`);
splitting the product by the value of `xᵢ` gives `cos^{#{xᵢ = 0̄}} · sin^{#{xᵢ = 1̄}}`, and
`#{xᵢ = 1̄} = w(X)`, `#{xᵢ = 0̄} = n − w(X)`. -/
theorem schumacherBlock_fidelity {n : ℕ} (x k : Fin n → Fin 2) :
    (PureState.piTensor fun i => schumacherTypicalKet (x i)).toState.fidelity
        (PureState.piTensor fun i => schumacherSourceKet (k i)).toState
      = Real.cos (Real.pi / 8) ^ (n - hammingNorm x) * Real.sin (Real.pi / 8) ^ hammingNorm x := by
  rw [PureState.fidelity_piTensor]
  simp_rw [schumacherTypicalKet_fidelity_sourceKet]
  rw [Finset.prod_ite (fun _ => Real.cos (Real.pi / 8)) (fun _ => Real.sin (Real.pi / 8)),
    Finset.prod_const, Finset.prod_const]
  have hw : (Finset.univ.filter fun i => ¬ (x i = 0)).card = hammingNorm x := rfl
  have hn : (Finset.univ.filter fun i => x i = 0).card = n - hammingNorm x := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => x i = 0)
    rw [Finset.card_univ, Fintype.card_fin, hw] at hsum
    omega
  rw [hw, hn]

end AxQM
