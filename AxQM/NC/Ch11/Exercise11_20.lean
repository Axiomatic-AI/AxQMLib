/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ProjectorPinching
import AxQM.Postulates.API.RandomUnitaryEntropy

/-!
# N&C Exercise 11.20 — the pinching is a probabilistic unitary mixture; alternate proof of Thm 11.9

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.20, p. 518.

Show P rho P + Q rho Q is a probabilistic unitary mixture; give alt proof of Thm 11.9.

## The two parts

**Part 1 — the observation** (in `AxQM/Postulates/API/ProjectorPinching.lean`):
for a projector `P` with `Q = 1 − P`,
`P ρ P + Q ρ Q = ½ (U₁ ρ U₁†) + ½ (U₂ ρ U₂†)` with the two witnesses realized as genuine unitary
`Evolution`s `U₁ = 1`, `U₂ = 1 − 2P = −(2P − 1)` (`AxQM.reflectionEvolutionOfProj`),
`p = ½` — `AxQM.projPinching_two_eq_reflection_evolve_mix`, on the underlying ring identity
`AxQM.projPinching_two_eq_reflection_mix`.

**Part 2 — the alternate proof of Theorem 11.9.** Theorem 11.9 asserts **both** `S(ρ') ≥ S(ρ)`
**and** the equality condition `S(ρ') = S(ρ) ↔ ρ' = ρ`, for a **complete set of orthogonal
projectors** — so a two-outcome-only argument, or one delivering only the inequality, would silently
weaken it. The observation generalises: the pinching `ρ ↦ Σᵢ Pᵢ ρ Pᵢ` of *any* projective
measurement is the uniform average of the `2^|ι|` sign unitaries `U_ε = Σᵢ εᵢ Pᵢ`
(`AxQM.pinchingRandomUnitaryChannel`), hence a **random-unitary channel**. This file lifts
that to the theorems below:
`Measurement.IsProjective.unreadState_isRandomUnitary` (the observation, in full generality);
`Measurement.IsProjective.vonNeumannEntropy_unreadState_ge_of_concavity` (`S(ρ) ≤ S(Σᵢ Pᵢ ρ Pᵢ)`,
eq. (11.66), via `AxQM.vonNeumannEntropy_le_of_isRandomUnitary`); and
`Measurement.IsProjective.vonNeumannEntropy_unreadState_eq_iff_of_concavity` (the equality
condition, via the faithfulness-free **strict**-concavity equality
`State.vonNeumannEntropy_mix_eq_sum_iff'`).

This is genuinely N&C's *alternate* proof, distinct from the library's Klein route
(`Theorem11_9.lean`): there the entropy increase and its equality case come from `D(ρ ‖ ρ') ≥ 0` and
its equality case; here from **concavity** and **strict** concavity applied to the random-unitary
decomposition. The two-theorem structure (`…_ge_of_concavity` + `…_eq_iff_of_concavity`) mirrors the
Klein-based pair, re-proving the **whole** of Theorem 11.9 in full N&C generality — every density
operator `ρ`, every complete set of orthogonal projectors — with no weakening.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- **Nielsen & Chuang, Exercise 11.20 — the pinching is a probabilistic unitary mixture** (in full
generality). The unread (non-selective) post-measurement state `ρ ↦ Σᵢ Pᵢ ρ Pᵢ`
(`Measurement.unreadState`) of a projective measurement `m` is a **random-unitary channel**
(`IsRandomUnitary`): it is the uniform mixture of the `2^|ι|` sign unitaries `U_ε = Σᵢ εᵢ Pᵢ`
(`AxQM.pinchingRandomUnitaryChannel`). For the two-outcome case `{P, Q = 1 − P}` this is
N&C's observation `P ρ P + Q ρ Q = ½ (U₁ ρ U₁†) + ½ (U₂ ρ U₂†)` with unitary witnesses `U₁ = 1`,
`U₂ = 1 − 2P`, `p = ½` (`AxQM.projPinching_two_eq_reflection_evolve_mix`). -/
theorem Measurement.IsProjective.unreadState_isRandomUnitary {m : Measurement ι S}
    (h : m.IsProjective) : IsRandomUnitary m.unreadState := by
  classical
  exact ⟨pinchingRandomUnitaryChannel m h, pinchingRandomUnitaryChannel_apply m h⟩

/-- **Nielsen & Chuang, Theorem 11.9, eq. (11.66) — alternate proof via concavity (Exercise
11.20).** For a projective measurement `m` and any state `ρ`, the unread post-measurement state
`ρ' = Σᵢ Pᵢ ρ Pᵢ` (`m.unreadState ρ`) has entropy at least that of `ρ`,

  `S(ρ) ≤ S(ρ')`.

Proof (N&C's alternate route): the pinching is a random-unitary channel
(`Measurement.IsProjective.unreadState_isRandomUnitary`), and a random-unitary channel never
decreases the von Neumann entropy by **concavity** and unitary invariance
(`AxQM.vonNeumannEntropy_le_of_isRandomUnitary`). This is the entropy-increase inequality
of Theorem 11.9 in full generality (no Klein inequality); its equality condition is the companion
`vonNeumannEntropy_unreadState_eq_iff_of_concavity`. -/
theorem Measurement.IsProjective.vonNeumannEntropy_unreadState_ge_of_concavity
    {m : Measurement ι S} (h : m.IsProjective) (ρ : State S) :
    ρ.vonNeumannEntropy ≤ (m.unreadState ρ).vonNeumannEntropy :=
  vonNeumannEntropy_le_of_isRandomUnitary h.unreadState_isRandomUnitary ρ

/-- **Nielsen & Chuang, Theorem 11.9 — equality condition, alternate proof via strict concavity
(Exercise 11.20).** For a projective measurement `m` and any state `ρ`, the unread post-measurement
state `ρ' = Σᵢ Pᵢ ρ Pᵢ` (`m.unreadState ρ`) has the **same** entropy as `ρ` iff the measurement
leaves the state unchanged,

  `S(ρ') = S(ρ) ↔ ρ' = ρ`.

Proof (N&C's alternate route, via *strict* concavity — the equality companion of
`vonNeumannEntropy_unreadState_ge_of_concavity`): `ρ'` is the uniform mixture of the `2^|ι|`
sign-unitary conjugations `Uₖ ρ Uₖ†` (`unreadState_isRandomUnitary` /
`pinchingRandomUnitaryChannel`), each with `S(Uₖ ρ Uₖ†) = S(ρ)` (unitary invariance). Equal entropy
`S(ρ') = S(ρ)` therefore saturates
the concavity inequality, so the faithfulness-free strict-concavity equality condition
`State.vonNeumannEntropy_mix_eq_sum_iff'` forces every positive-weight component to equal `ρ'`; the
all-`+1` component is `ρ` itself (`signEvolution_const_true_evolve`, `Σᵢ Pᵢ = 1`), whence `ρ' = ρ`.
The reverse direction is immediate. Together with the inequality this re-proves the **whole** of
Theorem 11.9 via concavity, matching the two-theorem structure of the Klein-based `Theorem11_9.lean`
(`…vonNeumannEntropy_unreadState_eq_iff`). No faithfulness or two-outcome restriction. -/
theorem Measurement.IsProjective.vonNeumannEntropy_unreadState_eq_iff_of_concavity
    {m : Measurement ι S} (h : m.IsProjective) (ρ : State S) :
    (m.unreadState ρ).vonNeumannEntropy = ρ.vonNeumannEntropy ↔ m.unreadState ρ = ρ := by
  classical
  refine ⟨fun heq => ?_, fun heq => by rw [heq]⟩
  set C := pinchingRandomUnitaryChannel m h with hC
  -- `ρ'` is the uniform mixture of the sign-unitary conjugations of `ρ`
  have hCapply : C.apply ρ = m.unreadState ρ := by
    rw [hC]; exact pinchingRandomUnitaryChannel_apply m h ρ
  have hmix : m.unreadState ρ
      = State.mix C.prob C.prob_nonneg C.sum_prob (fun k => (C.unitary k).evolve ρ) :=
    hCapply.symm.trans (C.apply_eq_mix ρ)
  -- equal entropy saturates the concavity inequality (unitary invariance of the entropy)
  have hsum_eq : (State.mix C.prob C.prob_nonneg C.sum_prob
        (fun k => (C.unitary k).evolve ρ)).vonNeumannEntropy
      = ∑ k, C.prob k * ((C.unitary k).evolve ρ).vonNeumannEntropy := by
    rw [← hmix, heq]
    have hev : ∀ k, ((C.unitary k).evolve ρ).vonNeumannEntropy = ρ.vonNeumannEntropy :=
      fun k => State.vonNeumannEntropy_evolve (C.unitary k) ρ
    simp only [hev]
    rw [← Finset.sum_mul, C.sum_prob, one_mul]
  -- strict concavity (faithfulness-free): every positive-weight component equals the mixture
  have hall := (State.vonNeumannEntropy_mix_eq_sum_iff' C.prob C.prob_nonneg C.sum_prob
    (fun k => (C.unitary k).evolve ρ)).mp hsum_eq
  -- the all-`+1` sign vector is an identity component (weight `> 0`) whose conjugation is `ρ`
  set k₀ := (Fintype.equivFin (ι → Bool)) (fun _ => true) with hk0
  have hprob0 : 0 < C.prob k₀ := by
    change (0 : ℝ) < (Fintype.card (ι → Bool) : ℝ)⁻¹
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hσ0 : (C.unitary k₀).evolve ρ = ρ := by
    have hcu : C.unitary k₀ = signEvolution m h (fun _ => true) := by
      change signEvolution m h ((Fintype.equivFin (ι → Bool)).symm k₀)
        = signEvolution m h (fun _ => true)
      rw [hk0, Equiv.symm_apply_apply]
    rw [hcu, signEvolution_const_true_evolve]
  rw [hmix]
  exact (hall k₀ hprob0).symm.trans hσ0

end AxQM
