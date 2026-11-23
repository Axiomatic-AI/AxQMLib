/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliMeasurement

/-!
# AxQM.Postulates.API — the ± eigenprojector operator-sum identity

The purely algebraic identity behind the *alternate operator-sum representation* of a channel
built from a `±1` observable (Nielsen & Chuang, Exercise 10.2): for any observable `A` with its
eigenprojectors `P₊ = (I + A)/2`, `P₋ = (I − A)/2` (`Observable.projPlus` / `Observable.projMinus`)
and *any* operator `T`,

`(1 − p) T + p (A T A) = (1 − 2p) T + 2p (P₊ T P₊) + 2p (P₋ T P₋)`.

Reading `T = ρ` this says the "flip with probability `p`" operator sum `(1−p) ρ + p A ρ A` equals
the "measure in the `A`-eigenbasis with probability `2p`" operator sum
`(1−2p) ρ + 2p P₊ ρ P₊ + 2p P₋ ρ P₋`. Note the identity holds for *every* real `p` and *every*
operator `A` — no involution or positivity hypothesis is needed, because the cross terms
`A T` and `T A` cancel between the `P₊` and `P₋` conjugations:
`P₊ T P₊ + P₋ T P₋ = ½ (T + A T A)` (`Observable.projConj_add_eq`).

The bit-flip channel's alternate representation in `AxQM/NC/Ch10/Exercise10_2.lean` uses it.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Observable

/-- **The two `±1`-eigenprojector conjugations average the identity and the `A`-conjugation:**
`P₊ T P₊ + P₋ T P₋ = ½ (T + A T A)` for any observable `A` and operator `T`. Substituting
`P₊ = ½(I + A)`, `P₋ = ½(I − A)` and expanding, the cross terms `A T` and `T A` cancel between the
two conjugations, leaving `¼·(2 T + 2 A T A) = ½(T + A T A)`. No hypothesis on `A` is required. -/
theorem projConj_add_eq (A : Observable S) (T : S.space →L[ℂ] S.space) :
    A.projPlus * T * A.projPlus + A.projMinus * T * A.projMinus
      = (2⁻¹ : ℂ) • (T + A.op * T * A.op) := by
  have expand :
      (1 + A.op) * T * (1 + A.op) + (1 - A.op) * T * (1 - A.op)
        = (T + A.op * T * A.op) + (T + A.op * T * A.op) := by
    noncomm_ring
  rw [projPlus, projMinus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← smul_add, expand, ← two_smul ℂ (T + A.op * T * A.op), smul_smul]
  norm_num

/-- **The alternate operator-sum identity of a `±1` observable** (Nielsen & Chuang, Exercise 10.2,
the algebraic core). For any observable `A`, real weight `p`, and operator `T`,

`(1 − p) T + p (A T A) = (1 − 2p) T + 2p (P₊ T P₊) + 2p (P₋ T P₋)`,

where `P₊ = A.projPlus`, `P₋ = A.projMinus`. This is the operator identity exhibiting the
"flip with probability `p`" operator sum `(1−p) ρ + p A ρ A` in the alternate "measure in the
`A`-eigenbasis with probability `2p`" form. Proved from `projConj_add_eq` by collecting the scalar
weights (`2p · ½ = p`, `(1−2p) + p = 1−p`); no involution hypothesis is used. -/
theorem dichotomic_operatorSum (A : Observable S) (p : ℝ) (T : S.space →L[ℂ] S.space) :
    ((1 - p : ℝ) : ℂ) • T + (p : ℂ) • (A.op * T * A.op)
      = ((1 - 2 * p : ℝ) : ℂ) • T
          + ((2 * p : ℝ) : ℂ) • (A.projPlus * T * A.projPlus)
          + ((2 * p : ℝ) : ℂ) • (A.projMinus * T * A.projMinus) := by
  rw [add_assoc, ← smul_add, projConj_add_eq, smul_smul]
  push_cast
  match_scalars <;> ring

end Observable

end AxQM
