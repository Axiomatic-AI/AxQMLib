/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.StateMajorization
import AxQM.Postulates.API.RandomUnitaryEntropy

/-!
# AxQM — von Neumann entropy is monotone non-increasing under LOCC / majorization

For bipartite pure states, converting `|ψ⟩` to `|φ⟩` by local operations and classical
communication (LOCC) can only **decrease** the entanglement, measured by the von Neumann entropy of
the reduced state. At the reduced-state level (where Nielsen's theorem lives, N&C Thm 12.15):

`ρ.Majorize σ → σ.vonNeumannEntropy ≤ ρ.vonNeumannEntropy`,

equivalently `ρ.LOCCConvertible σ → S(σ) ≤ S(ρ)`. Since `ρ ≺ σ` (majorization) is Nielsen's
condition for `|ψ⟩ → |φ⟩` by LOCC — and majorization `ρ ≺ σ` means the eigenvalue distribution of
`σ` is *more concentrated* (lower Shannon entropy) than that of `ρ` — this is the statement that
**entanglement entropy cannot be increased by LOCC**.

## Use in N&C Exercise 12.23

This is the monotone behind the **optimality of entanglement distillation** (N&C
Exercise 12.23): the distillable entanglement of `|ψ⟩` cannot exceed `S(ρ_ψ)`, because distilling
Bell states out of copies of `|ψ⟩` by LOCC can only reduce the total entanglement entropy, and `n`
Bell states carry entanglement entropy `n · log 2`. The converse bound of Exercise 12.23
uses this lemma together with additivity of the entropy across copies and the asymptotic
distillation-rate framework.

## Proof

`ρ ≺ σ` is realised as a **random-unitary mixture** of `σ`: by the forward operator-majorization
theorem (`State.exists_op_eq_sum_unitary_conj_of_majorize`, N&C Thm 12.13 at the density-operator
level) there are unitaries `Uⱼ` and probabilities `pⱼ` with `ρ.op = ∑ⱼ pⱼ Uⱼ σ.op Uⱼ†`, i.e.
`ρ = ∑ⱼ pⱼ (Uⱼ σ Uⱼ†)` is the probabilistic mixture of the unitary conjugates `(Uⱼ).evolve σ`.
A mixture of unitary conjugates of `σ` never decreases the entropy
(`State.vonNeumannEntropy_le_mix_evolve`, the shared core also behind
`RandomUnitaryChannel.vonNeumannEntropy_apply_ge`): faithfulness-free concavity
(`State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix'`, the mixture being generally
rank-deficient) gives `S(ρ) ≥ ∑ⱼ pⱼ S(Uⱼ σ Uⱼ†)`, and unitary invariance
(`State.vonNeumannEntropy_evolve`, `S(Uⱼ σ Uⱼ†) = S(σ)`) collapses the right-hand side to
`(∑ⱼ pⱼ) S(σ) = S(σ)`.

The proof works at the operator level (`.op`); the operator-level majorization results it invokes
are in `AxQM/Postulates/API/StateMajorization.lean`.
-/

noncomputable section

namespace AxQM

namespace State

variable {S : QSystem}

/-- **Entanglement entropy is monotone non-increasing under majorization.** If `ρ.Majorize σ`
(N&C's `ρ ≺ σ`, Nielsen's LOCC condition on the reduced states) then `S(σ) ≤ S(ρ)`.

`ρ ≺ σ` presents `ρ` as a random-unitary mixture `ρ = ∑ⱼ pⱼ Uⱼ σ Uⱼ†` of `σ`
(`State.exists_op_eq_sum_unitary_conj_of_majorize`), and a mixture of unitary conjugates of `σ`
never decreases the entropy (`State.vonNeumannEntropy_le_mix_evolve`), giving `S(σ) ≤ S(ρ)`. -/
theorem Majorize.vonNeumannEntropy_le {ρ σ : State S} (h : ρ.Majorize σ) :
    σ.vonNeumannEntropy ≤ ρ.vonNeumannEntropy := by
  obtain ⟨ι, hι, p, U, hp, hsum, hunit, hρ⟩ := exists_op_eq_sum_unitary_conj_of_majorize h
  -- `ρ` is the random-unitary mixture of `σ`: package each unitary `Uⱼ` as an evolution.
  have hmix : ρ = State.mix p hp hsum (fun j => (⟨U j, hunit j⟩ : Evolution S).evolve σ) := by
    apply State.ext
    rw [State.mix_op, hρ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Evolution.evolve_op]
  -- A mixture of unitary conjugates of `σ` never decreases the entropy.
  rw [hmix]
  exact State.vonNeumannEntropy_le_mix_evolve p hp hsum (fun j => ⟨U j, hunit j⟩) σ

/-- **Entanglement entropy cannot be increased by LOCC** (the `LOCCConvertible` form of
`State.Majorize.vonNeumannEntropy_le`). If `ρ` is one-way LOCC convertible to `σ` then
`S(σ) ≤ S(ρ)`. Follows from the forward direction of Nielsen's theorem
(`State.LOCCConvertible.majorize`, `ρ.LOCCConvertible σ → ρ.Majorize σ`) and the majorization
monotone. -/
theorem LOCCConvertible.vonNeumannEntropy_le {ρ σ : State S} (h : ρ.LOCCConvertible σ) :
    σ.vonNeumannEntropy ≤ ρ.vonNeumannEntropy :=
  h.majorize.vonNeumannEntropy_le

end State

end AxQM
