/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RandomUnitaryEntropy
import AxQM.Postulates.API.UnreadMeasurement
import AxQM.Concrete.SignVectorCharacter

/-!
# AxQM.Postulates.API — the pinching (dephasing) map as a random-unitary channel

The **pinching** (non-selective dephasing) map of a projective measurement with orthogonal
projectors `{Pᵢ}` (a complete set, `∑ᵢ Pᵢ = 1`) is `ρ ↦ Σᵢ Pᵢ ρ Pᵢ` — the unread post-measurement
state `Measurement.unreadState` of that measurement. This file exhibits it as a **random-unitary
channel** `E(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†`, the construction behind the concavity-based *alternate proof of
Nielsen & Chuang Theorem 11.9* requested by **Exercise 11.20**.

## The construction

The pinching is the uniform average of the `2^|ι|` **sign unitaries** `U_ε = Σᵢ εᵢ Pᵢ`, one per sign
vector `ε : ι → Bool` (`εᵢ = ±1`): `(1 / 2^|ι|) · Σ_ε U_ε ρ U_ε = Σᵢ Pᵢ ρ Pᵢ`. Each `U_ε` is a
self-adjoint unitary (involution `U_ε² = Σᵢ Pᵢ = 1`, by orthogonality and idempotence), hence an
`Evolution`; the averaging identity is **character orthogonality** `(1/2^|ι|) Σ_ε εᵢ εⱼ = δᵢⱼ` (the
off-diagonal cancels because flipping the `i`-th sign negates `εᵢ εⱼ`), collapsing the double sum
`Σ_{i,j} (Σ_ε εᵢ εⱼ) Pᵢ ρ Pⱼ` to the diagonal `Σᵢ Pᵢ ρ Pᵢ`.

## Main results

* `AxQM.signProjSum` / `AxQM.signEvolution` — the sign operator `U_ε = Σᵢ εᵢ Pᵢ`
  and its packaging as a unitary `Evolution` for a projective measurement.
* `AxQM.sum_signProjSum_conj` — the averaging identity
  `Σ_ε U_ε ρ U_ε = 2^|ι| · Σᵢ Pᵢ ρ Pᵢ` (character orthogonality).
* `AxQM.pinchingRandomUnitaryChannel` / `AxQM.pinchingRandomUnitaryChannel_apply` — the pinching
  packaged as a `RandomUnitaryChannel`, with `C.apply ρ = m.unreadState ρ` (used in
  `AxQM/NC/Ch11/Exercise11_20.lean`).
* `AxQM.reflectionEvolutionOfProj` / `AxQM.projPinching_two_eq_reflection_mix` —
  the **two-projector observation** of Exercise 11.20 with explicit witnesses: for `Q = 1 - P`,
  `P ρ P + Q ρ Q = ½ ρ + ½ (1 - 2P) ρ (1 - 2P)`, i.e. `U₁ = 1`, `U₂ = 1 - 2P`, `p = ½` (the
  `|ι| = 2` case, stated concretely).

The statements of Exercise 11.20 are in `AxQM/NC/Ch11/Exercise11_20.lean`.
-/

open scoped BigOperators
open ContinuousLinearMap AxQM.Concrete

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-! ### The sign operators `U_ε = Σᵢ εᵢ Pᵢ`

The `±1` sign scalar `sgnBool` and the character-orthogonality sum `sum_sgnBool_mul_sgnBool` are
pure combinatorics and are in `AxQM.Concrete.SignVectorCharacter`; they are `open`ed above. -/

/-- The **sign operator** `U_ε = Σᵢ (±1) Pᵢ` of a family of operators `P` and a sign vector
`ε : ι → Bool`. For a complete set of orthogonal projectors it is a self-adjoint unitary
(`signProjSum_isSelfAdjoint`, `signProjSum_mul_self`), packaged as an `Evolution` in
`signEvolution`. -/
def signProjSum (P : ι → (S →L[ℂ] S)) (ε : ι → Bool) : S →L[ℂ] S := ∑ i, sgnBool (ε i) • P i

/-- `U_ε` is **self-adjoint** when every `Pᵢ` is: `U_ε† = U_ε` (the `±1` weights are real). -/
theorem signProjSum_isSelfAdjoint {P : ι → (S →L[ℂ] S)} (hsa : ∀ i, IsSelfAdjoint (P i))
    (ε : ι → Bool) : IsSelfAdjoint (signProjSum P ε) := by
  simp only [isSelfAdjoint_iff, signProjSum, star_sum, star_smul, sgnBool_star, (hsa _).star_eq]

/-- `U_ε` is an **involution**, `U_ε² = 1`, for a complete set of orthogonal projectors: the double
sum `Σᵢⱼ εᵢ εⱼ Pᵢ Pⱼ` collapses by orthogonality `Pᵢ Pⱼ = 0` (`i ≠ j`) and idempotence `Pᵢ² = Pᵢ`
to `Σᵢ (εᵢ)² Pᵢ = Σᵢ Pᵢ = 1`. -/
theorem signProjSum_mul_self {P : ι → (S →L[ℂ] S)} (hproj : ∀ i, IsStarProjection (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (hsum : ∑ i, P i = 1) (ε : ι → Bool) :
    signProjSum P ε * signProjSum P ε = 1 := by
  classical
  simp only [signProjSum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul]
  have hcollapse : ∀ x, ∑ y, (sgnBool (ε x) * sgnBool (ε y)) • (P y * P x) = P x := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [(hproj x).isIdempotentElem, sgnBool_mul_self, one_smul]
    · intro y _ hyx; rw [horth y x hyx, smul_zero]
    · intro hx; exact absurd (Finset.mem_univ x) hx
  simp_rw [hcollapse]; exact hsum

/-- **The pinching averaging identity (character orthogonality):**
`Σ_ε U_ε ρ U_ε = 2^|ι| · Σᵢ Pᵢ ρ Pᵢ`. Expanding `U_ε ρ U_ε = Σᵢⱼ εᵢ εⱼ (Pᵢ ρ Pⱼ)` and summing over
`ε` gives `Σᵢⱼ (Σ_ε εᵢ εⱼ) (Pᵢ ρ Pⱼ)`; by `sum_sgnBool_mul_sgnBool` the inner average is
`2^|ι| δᵢⱼ`, killing the off-diagonal. Pure operator/scalar algebra — no projector hypotheses. -/
theorem sum_signProjSum_conj [DecidableEq ι] (P : ι → (S →L[ℂ] S)) (ρ : S →L[ℂ] S) :
    ∑ ε : ι → Bool, signProjSum P ε * ρ * signProjSum P ε
      = (Fintype.card (ι → Bool) : ℂ) • ∑ i, (P i * ρ * P i) := by
  classical
  have hexp : ∀ ε : ι → Bool, signProjSum P ε * ρ * signProjSum P ε
      = ∑ i, ∑ j, (sgnBool (ε i) * sgnBool (ε j)) • (P j * ρ * P i) := by
    intro ε
    simp only [signProjSum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      Finset.smul_sum, smul_smul]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (γ := ι → Bool), ← Finset.sum_smul, sum_sgnBool_mul_sgnBool, ite_smul,
    zero_smul, Finset.sum_ite_eq Finset.univ, Finset.mem_univ, ite_true, Finset.smul_sum]

/-- The **sign unitary as an `Evolution`**: `U_ε = Σᵢ εᵢ Pᵢ` for the projectors `Pᵢ = m.op i` of a
projective measurement `m`, a genuine unitary (self-adjoint involution). The `2^|ι|` of these are
the unitaries mixed by the pinching channel `pinchingRandomUnitaryChannel`. -/
def signEvolution (m : Measurement ι S) (h : m.IsProjective) (ε : ι → Bool) : Evolution S where
  op := signProjSum m.op ε
  unitary := by
    have hsa : IsSelfAdjoint (signProjSum m.op ε) :=
      signProjSum_isSelfAdjoint (fun i => (h i).isSelfAdjoint) ε
    have hinv : signProjSum m.op ε * signProjSum m.op ε = 1 :=
      signProjSum_mul_self h (fun _ _ hij => h.orthogonal hij) h.sum_op_eq_one ε
    rw [Unitary.mem_iff, hsa.star_eq]
    exact ⟨hinv, hinv⟩

@[simp]
theorem signEvolution_op (m : Measurement ι S) (h : m.IsProjective) (ε : ι → Bool) :
    (signEvolution m h ε).op = signProjSum m.op ε := rfl

/-- The state conjugation `U_ε ρ U_ε†` unfolds to `U_ε ρ U_ε` (self-adjoint `U_ε`): its operator is
`signProjSum m.op ε * ρ * signProjSum m.op ε`. -/
theorem signEvolution_evolve_op (m : Measurement ι S) (h : m.IsProjective) (ε : ι → Bool)
    (ρ : State S) :
    ((signEvolution m h ε).evolve ρ).op
      = signProjSum m.op ε * ρ.op * signProjSum m.op ε := by
  have hsa : IsSelfAdjoint (signEvolution m h ε).op :=
    signProjSum_isSelfAdjoint (fun i => (h i).isSelfAdjoint) ε
  rw [Evolution.evolve_op_of_isSelfAdjoint hsa ρ, signEvolution_op]

/-! ### The pinching as a random-unitary channel -/

/-- **The pinching (dephasing) map of a projective measurement, as a random-unitary channel.** The
uniform mixture of the `2^|ι|` sign unitaries `U_ε` (each with probability `1/2^|ι|`); its action is
the pinching `ρ ↦ Σᵢ Pᵢ ρ Pᵢ = m.unreadState ρ` (`pinchingRandomUnitaryChannel_apply`). The index
`ι → Bool` is enumerated as `Fin 2^|ι|` through `Fintype.equivFin`. -/
def pinchingRandomUnitaryChannel (m : Measurement ι S) (h : m.IsProjective) [DecidableEq ι] :
    RandomUnitaryChannel S where
  card := Fintype.card (ι → Bool)
  prob := fun _ => (Fintype.card (ι → Bool) : ℝ)⁻¹
  unitary := fun k => signEvolution m h ((Fintype.equivFin (ι → Bool)).symm k)
  prob_nonneg := fun _ => by positivity
  sum_prob := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)]

/-- **The pinching channel acts as the unread post-measurement state:**
`C.apply ρ = m.unreadState ρ = Σᵢ Pᵢ ρ Pᵢ`. Reindexing the `Fin 2^|ι|` mixture back to `ι → Bool`,
each summand is `(1/2^|ι|) U_ε ρ U_ε` (`signEvolution_evolve_op`); the averaging identity
`sum_signProjSum_conj` turns the total into `(1/2^|ι|) · 2^|ι| · Σᵢ Pᵢ ρ Pᵢ = Σᵢ Pᵢ ρ Pᵢ`, which is
the projective unread state (`Measurement.IsProjective.unreadState_op`). -/
theorem pinchingRandomUnitaryChannel_apply (m : Measurement ι S) (h : m.IsProjective)
    [DecidableEq ι] (ρ : State S) :
    (pinchingRandomUnitaryChannel m h).apply ρ = m.unreadState ρ := by
  have hcard0 : (Fintype.card (ι → Bool) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply State.ext
  rw [RandomUnitaryChannel.apply_op, h.unreadState_op]
  -- match the projective unread state to the diagonal sum
  have hrhs : ∑ i, (m.op i).comp (ρ.op.comp (m.op i)) = ∑ i, (m.op i * ρ.op * m.op i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, mul_assoc]
  rw [hrhs]
  -- reindex the `Fin 2^|ι|` mixture back to a sum over sign vectors `ε : ι → Bool`, unfolding the
  -- channel's `prob`/`unitary` fields (`signEvolution_evolve_op`) on the way
  have hreindex : (∑ k, ((pinchingRandomUnitaryChannel m h).prob k : ℂ) •
        (((pinchingRandomUnitaryChannel m h).unitary k).evolve ρ).op)
      = ∑ ε : ι → Bool, ((Fintype.card (ι → Bool) : ℂ))⁻¹ •
          (signProjSum m.op ε * ρ.op * signProjSum m.op ε) :=
    Fintype.sum_bijective (Fintype.equivFin (ι → Bool)).symm
      (Fintype.equivFin (ι → Bool)).symm.bijective
      (fun k => ((pinchingRandomUnitaryChannel m h).prob k : ℂ) •
        (((pinchingRandomUnitaryChannel m h).unitary k).evolve ρ).op)
      (fun ε => ((Fintype.card (ι → Bool) : ℂ))⁻¹ •
        (signProjSum m.op ε * ρ.op * signProjSum m.op ε))
      (fun k => by
        simp only [pinchingRandomUnitaryChannel, signEvolution_evolve_op, Complex.ofReal_inv,
          Complex.ofReal_natCast])
  rw [hreindex, ← Finset.smul_sum, sum_signProjSum_conj, smul_smul, inv_mul_cancel₀ hcard0,
    one_smul]

/-- **The all-`+1` sign vector is the identity unitary.** For a projective measurement `m`, the sign
operator of the constant-`true` vector is `U = Σᵢ 1 · Pᵢ = Σᵢ Pᵢ = 1`, so its conjugation fixes
every state: `(signEvolution m h (fun _ => true)).evolve ρ = ρ`. This is the identity component of
the pinching channel `pinchingRandomUnitaryChannel`, and it is what turns the strict-concavity
equality case into `Σᵢ Pᵢ ρ Pᵢ = ρ` for the equality condition of Theorem 11.9 (Exercise 11.20). -/
theorem signEvolution_const_true_evolve (m : Measurement ι S) (h : m.IsProjective) (ρ : State S) :
    (signEvolution m h (fun _ => true)).evolve ρ = ρ := by
  have hone : signProjSum m.op (fun _ => true) = 1 := by
    have htrue : sgnBool true = 1 := by simp [sgnBool]
    simp only [signProjSum, htrue, one_smul]
    exact h.sum_op_eq_one
  apply State.ext
  rw [Evolution.evolve_op, signEvolution_op, hone, ← ContinuousLinearMap.star_eq_adjoint,
    star_one, ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, one_mul, mul_one]

/-! ### The two-projector observation (Exercise 11.20, Part 1) -/

/-- The **reflection** `1 - 2P` of an orthogonal projector `P`, as a unitary `Evolution`. It is a
self-adjoint involution: `(1 - 2P)² = 1 - 4P + 4P² = 1` by idempotence `P² = P`. On the two-outcome
decomposition `{P, Q = 1 - P}` it is the `U₂` witness of Exercise 11.20's observation (equivalently
`-(2P - 1)`, whose conjugation action is identical). -/
def reflectionEvolutionOfProj {P : S →L[ℂ] S} (hP : IsStarProjection P) : Evolution S where
  op := 1 - (2 : ℂ) • P
  unitary := by
    have hsa : star (1 - (2 : ℂ) • P) = 1 - (2 : ℂ) • P := by
      rw [star_sub, star_one, star_smul, hP.isSelfAdjoint.star_eq]; norm_num
    have hinv : (1 - (2 : ℂ) • P) * (1 - (2 : ℂ) • P) = 1 := by
      have hi : P * P = P := hP.isIdempotentElem
      simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hi]
      match_scalars <;> ring
    rw [Unitary.mem_iff, hsa]; exact ⟨hinv, hinv⟩

@[simp]
theorem reflectionEvolutionOfProj_op {P : S →L[ℂ] S} (hP : IsStarProjection P) :
    (reflectionEvolutionOfProj hP).op = 1 - (2 : ℂ) • P := rfl

/-- **The reflection `1 - 2P` is self-adjoint** (`(1 - 2P)† = 1 - 2P`, the `2` real and `P`
self-adjoint). The named companion of `signProjSum_isSelfAdjoint`, feeding the
conjugation bridge `Evolution.evolve_op_of_isSelfAdjoint` in
`projPinching_two_eq_reflection_evolve_mix`. -/
theorem reflectionEvolutionOfProj_isSelfAdjoint {P : S →L[ℂ] S} (hP : IsStarProjection P) :
    IsSelfAdjoint (reflectionEvolutionOfProj hP).op := by
  rw [isSelfAdjoint_iff, reflectionEvolutionOfProj_op, star_sub, star_one, star_smul,
    hP.isSelfAdjoint.star_eq]; norm_num

/-- **The two-projector operator identity** underlying Exercise 11.20's observation. For any
operators `P`, `ρ`, `P ρ P + (1 - P) ρ (1 - P) = ½ ρ + ½ (1 - 2P) ρ (1 - 2P)` — both sides equal
`ρ - P ρ - ρ P + 2 P ρ P`, a pure ring identity needing no property of `P`. It is the algebraic
heart of `projPinching_two_eq_reflection_evolve_mix`, which upgrades `1` and `1 - 2P` to genuine
unitary `Evolution`s for a star projection `P`. -/
theorem projPinching_two_eq_reflection_mix (P ρ : S →L[ℂ] S) :
    P * ρ * P + (1 - P) * ρ * (1 - P)
      = (1 / 2 : ℂ) • ρ + (1 / 2 : ℂ) • ((1 - (2 : ℂ) • P) * ρ * (1 - (2 : ℂ) • P)) := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_sub]
  match_scalars <;> ring

/-- **Nielsen & Chuang, Exercise 11.20 — the two-projector observation, with unitary witnesses.**
For an orthogonal projector `P` (`Q = 1 - P`) and any state `ρ`, the two-outcome pinching
`P ρ P + Q ρ Q` is the equal mixture of the two unitary conjugations `U₁ ρ U₁†` and `U₂ ρ U₂†`,

  `P ρ P + Q ρ Q = ½ (U₁ ρ U₁†) + ½ (U₂ ρ U₂†)`,

with witnesses `U₁ = 1` (`Evolution.id`), `U₂ = 1 - 2P` (`reflectionEvolutionOfProj hP`, the
reflection through `range P`, self-adjoint so `U₂† = U₂`), and `p = ½` — exactly N&C's
`P ρ P + Q ρ Q = p U₁ ρ U₁† + (1 - p) U₂ ρ U₂†`. Here the `U`s are honest `Evolution`s (unitaries),
not bare operators, realizing the exercise's "there **are** unitary operators `U₁` and `U₂`"; the
`.evolve` conjugations unfold (via self-adjointness of the reflection and `id.evolve ρ = ρ`) to the
ring identity `projPinching_two_eq_reflection_mix`. -/
theorem projPinching_two_eq_reflection_evolve_mix {P : S →L[ℂ] S} (hP : IsStarProjection P)
    (ρ : State S) :
    P * ρ.op * P + (1 - P) * ρ.op * (1 - P)
      = (1 / 2 : ℂ) • ((Evolution.id : Evolution S).evolve ρ).op
        + (1 / 2 : ℂ) • ((reflectionEvolutionOfProj hP).evolve ρ).op := by
  have hid_ev : ((Evolution.id : Evolution S).evolve ρ).op = ρ.op := by rw [Evolution.evolve_id]
  have hrefl_ev : ((reflectionEvolutionOfProj hP).evolve ρ).op
      = (1 - (2 : ℂ) • P) * ρ.op * (1 - (2 : ℂ) • P) := by
    rw [Evolution.evolve_op_of_isSelfAdjoint (reflectionEvolutionOfProj_isSelfAdjoint hP) ρ,
      reflectionEvolutionOfProj_op]
  rw [hid_ev, hrefl_ev]
  exact projPinching_two_eq_reflection_mix P ρ.op

end AxQM
