/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EntropyConcavity
import AxQM.Postulates.API.EntropyEvolution
import AxQM.Postulates.API.RandomUnitaryChannel

/-!
# AxQM.Postulates.API — random-unitary channels never decrease entropy

A **random-unitary (mixed-unitary) channel** `E(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†` never *decreases* the von
Neumann entropy of its input:

`S(ρ) ≤ S(E(ρ))`.

This is the abstract content of the *alternate proof* of Nielsen & Chuang, Theorem 11.9
(projective measurements never decrease entropy) requested by **Exercise 11.20**: once the pinching
`ρ ↦ P ρ P + Q ρ Q` is exhibited as a random-unitary channel (see
`AxQM/NC/Ch11/Exercise11_20.lean`), this lemma delivers the entropy bound with no further
work. The proof is exactly N&C's concavity argument:

`S(E(ρ)) = S(∑ₖ pₖ Uₖ ρ Uₖ†) ≥ ∑ₖ pₖ S(Uₖ ρ Uₖ†) = ∑ₖ pₖ S(ρ) = S(ρ)`,

the inequality being *concavity* of the entropy
(`State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix'`, the faithfulness-free form — the
mixture `E(ρ)` is generally rank-deficient), and the two equalities
being *unitary invariance* of the entropy (`State.vonNeumannEntropy_evolve`, `S(UρU†) = S(ρ)`) and
`∑ₖ pₖ = 1`.

## Main results

* `AxQM.RandomUnitaryChannel.vonNeumannEntropy_apply_ge` — for a concrete
  `RandomUnitaryChannel` `C`, `S(ρ) ≤ S(C.apply ρ)`.
* `AxQM.vonNeumannEntropy_le_of_isRandomUnitary` — the `IsRandomUnitary`-predicate form:
  any random-unitary state-map `f` satisfies `S(ρ) ≤ S(f ρ)`.

The proof uses the faithfulness-free concavity of the entropy from
`AxQM/Postulates/API/EntropyConcavity.lean`.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A probabilistic mixture of unitary conjugates of `ρ` never decreases the entropy:**
`S(ρ) ≤ S(∑ⱼ pⱼ Uⱼ ρ Uⱼ†)`, over an arbitrary finite index type. Faithfulness-free concavity
(`sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix'`) plus unitary invariance
(`vonNeumannEntropy_evolve`, `S(Uⱼ ρ Uⱼ†) = S(ρ)`) collapse the average component entropy to
`(∑ⱼ pⱼ) S(ρ) = S(ρ)`. Shared core of `RandomUnitaryChannel.vonNeumannEntropy_apply_ge` and the
majorization monotone `State.Majorize.vonNeumannEntropy_le`. -/
theorem State.vonNeumannEntropy_le_mix_evolve {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (U : ι → Evolution S) (ρ : State S) :
    ρ.vonNeumannEntropy ≤ (State.mix p hp hsum fun j => (U j).evolve ρ).vonNeumannEntropy := by
  have hconc := State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix' p hp hsum
    fun j => (U j).evolve ρ
  have hev : ∀ j, ((U j).evolve ρ).vonNeumannEntropy = ρ.vonNeumannEntropy :=
    fun j => State.vonNeumannEntropy_evolve (U j) ρ
  simp only [hev] at hconc
  rwa [← Finset.sum_mul, hsum, one_mul] at hconc

/-- **A random-unitary channel never decreases the von Neumann entropy:** `S(ρ) ≤ S(C.apply ρ)`.

The channel output `C.apply ρ = ∑ₖ pₖ Uₖ ρ Uₖ†` is the probabilistic mixture of the conjugated
states `Uₖ ρ Uₖ† = (C.unitary k).evolve ρ`, so by concavity of the entropy (the faithfulness-free
form `State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix'`, since the mixture is generally
rank-deficient) `S(C.apply ρ) ≥ ∑ₖ pₖ S(Uₖ ρ Uₖ†)`. Unitary conjugation preserves entropy
(`State.vonNeumannEntropy_evolve`, `S(Uₖ ρ Uₖ†) = S(ρ)`), so the right-hand side is `(∑ₖ pₖ) S(ρ) =
S(ρ)`. -/
theorem RandomUnitaryChannel.vonNeumannEntropy_apply_ge (C : RandomUnitaryChannel S) (ρ : State S) :
    ρ.vonNeumannEntropy ≤ (C.apply ρ).vonNeumannEntropy := by
  rw [C.apply_eq_mix ρ]
  exact State.vonNeumannEntropy_le_mix_evolve C.prob C.prob_nonneg C.sum_prob C.unitary ρ

/-- **A random-unitary state-map never decreases the von Neumann entropy** (the `IsRandomUnitary`
form of `RandomUnitaryChannel.vonNeumannEntropy_apply_ge`): if `f` is realised by some
`RandomUnitaryChannel` (`IsRandomUnitary f`) then `S(ρ) ≤ S(f ρ)` for every `ρ`. This is the
reusable "probabilistic unitary mixtures never decrease entropy" lemma behind the concavity-based
alternate
proof of Nielsen & Chuang Theorem 11.9 (Exercise 11.20). -/
theorem vonNeumannEntropy_le_of_isRandomUnitary {f : State S → State S}
    (hf : IsRandomUnitary f) (ρ : State S) :
    ρ.vonNeumannEntropy ≤ (f ρ).vonNeumannEntropy := by
  obtain ⟨C, hC⟩ := hf
  rw [← hC ρ]
  exact C.vonNeumannEntropy_apply_ge ρ

end AxQM
