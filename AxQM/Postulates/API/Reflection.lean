/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Evolution

/-!
# AxQM.Postulates.API — the state reflection `R_ψ = I − 2|ψ⟩⟨ψ|`

The reflection underlying **generalized quantum searching**
(Nielsen & Chuang, Problem 6.2): for a pure state `ψ`, the unitary

`R_ψ ≡ I − 2|ψ⟩⟨ψ|`,

which — in N&C's words — "gives the state `|ψ⟩` a `−1` phase, and leaves states orthogonal to
`|ψ⟩` invariant". It is the Grover/amplitude-amplification **reflection operator** in its
state-dependent form (the `|ψ⟩ = |0⟩⊗ⁿ` special case is the conditional phase shift of
Exercise 6.1, up to global sign).

* `AxQM.reflectionEvolution ψ` — `R_ψ`, packaged as an `Evolution`. The `Evolution`
  structure bundles unitarity; producing this term discharges it. `R_ψ` is a
  **self-adjoint involution** (`(I − 2P)² = I` since the rank-one projector `P = |ψ⟩⟨ψ|` is
  idempotent for a unit vector), hence unitary.
* `AxQM.reflectionEvolution_op` — its operator `1 − 2 • |ψ⟩⟨ψ|`.
* `AxQM.reflectionEvolution_op_apply` — its action `x ↦ x − 2⟪ψ, x⟫ • ψ`.
* `AxQM.reflectionEvolution_hasEigenstate_neg_one` — the "`−1` phase to `|ψ⟩`":
  `R_ψ |ψ⟩ = −|ψ⟩`.
* `AxQM.reflectionEvolution_op_apply_of_orthogonal` — "leaves orthogonal states
  invariant": `⟪ψ, φ⟫ = 0 → R_ψ φ = φ`.
* `AxQM.reflectionEvolution_evolvePure_conj` — the **implementation identity**
  `R_{Uψ} = U ∘ R_ψ ∘ U†` (reflections are covariant under unitary conjugation). This is the
  content of Problem 6.2(1): given a circuit `U` preparing `|ψ⟩ = U|0⟩⊗ⁿ`, one implements
  `R_ψ` by conjugating the reference reflection `R_{|0⟩⊗ⁿ}` with `U`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The state reflection** `R_ψ = I − 2|ψ⟩⟨ψ|` of Nielsen & Chuang, Problem 6.2, as a
closed-system `Evolution`. It flips the phase of `|ψ⟩` (`R_ψ|ψ⟩ = −|ψ⟩`) and fixes every state
orthogonal to `|ψ⟩`. Unitarity is bundled: `R_ψ` is a self-adjoint involution, since the rank-one
projector `|ψ⟩⟨ψ|` is idempotent (`⟪ψ, ψ⟫ = ‖ψ‖² = 1`) and self-adjoint. -/
def reflectionEvolution (ψ : PureState S) : Evolution S where
  op := 1 - (2 : ℂ) • rankOne ℂ ψ.vec ψ.vec
  unitary := by
    have hself : inner ℂ ψ.vec ψ.vec = (1 : ℂ) := inner_self_eq_one_of_norm_eq_one ψ.normalized
    set P : S.space →L[ℂ] S.space := rankOne ℂ ψ.vec ψ.vec with hPdef
    have hPP : P * P = P := by
      rw [hPdef, ContinuousLinearMap.mul_def, rankOne_comp_rankOne, hself, one_smul]
    have hPsa : star P = P := by
      rw [hPdef, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]
    have hRsa : star (1 - (2 : ℂ) • P) = 1 - (2 : ℂ) • P := by
      rw [star_sub, star_one, star_smul, hPsa, star_ofNat]
    have hRR : (1 - (2 : ℂ) • P) * (1 - (2 : ℂ) • P) = 1 := by
      simp only [mul_sub, sub_mul, one_mul, mul_one, smul_mul_smul_comm, hPP]
      module
    rw [Unitary.mem_iff, hRsa]
    exact ⟨hRR, hRR⟩

@[simp]
theorem reflectionEvolution_op (ψ : PureState S) :
    (reflectionEvolution ψ).op = 1 - (2 : ℂ) • rankOne ℂ ψ.vec ψ.vec := rfl

/-- The action of the reflection `R_ψ` on a vector: `R_ψ x = x − 2⟪ψ, x⟫ • ψ`. -/
theorem reflectionEvolution_op_apply (ψ : PureState S) (x : S.space) :
    (reflectionEvolution ψ).op x = x - (2 * inner ℂ ψ.vec x) • ψ.vec := by
  rw [reflectionEvolution_op]
  simp only [sub_apply, one_apply_eq_self,
    smul_apply, rankOne_apply, smul_smul]

/-- **N&C Problem 6.2, the `−1` phase.** The reflection `R_ψ` gives `|ψ⟩` a `−1` phase:
`R_ψ|ψ⟩ = −|ψ⟩`, i.e. `|ψ⟩` is an eigenstate of `R_ψ` with eigenvalue `−1`. -/
theorem reflectionEvolution_hasEigenstate_neg_one (ψ : PureState S) :
    (reflectionEvolution ψ).HasEigenstate (-1) ψ := by
  change (reflectionEvolution ψ).op ψ.vec = (-1 : ℂ) • ψ.vec
  rw [reflectionEvolution_op_apply, inner_self_eq_norm_sq_to_K, ψ.normalized]
  push_cast
  module

/-- **N&C Problem 6.2, orthogonal invariance.** The reflection `R_ψ` leaves every state
orthogonal to `|ψ⟩` invariant: if `⟪ψ, φ⟫ = 0` then `R_ψ φ = φ`. -/
theorem reflectionEvolution_op_apply_of_orthogonal (ψ : PureState S) {x : S.space}
    (h : inner ℂ ψ.vec x = (0 : ℂ)) :
    (reflectionEvolution ψ).op x = x := by
  rw [reflectionEvolution_op_apply, h]
  simp

/-- **N&C Problem 6.2(1), the implementation identity.** Reflections are *covariant under unitary
conjugation*: `R_{Uψ} = U ∘ R_ψ ∘ U†`. Given a circuit `U` that prepares `|ψ⟩ = U|0⟩⊗ⁿ` (take the
reference state for `ψ`), this says the reflection about the prepared state is implemented by
conjugating the reference reflection `R_{|0⟩⊗ⁿ}` with `U` — the answer to "explain how to
implement `U_ψ`". -/
theorem reflectionEvolution_evolvePure_conj (U : Evolution S) (ψ : PureState S) :
    reflectionEvolution (U.evolvePure ψ)
      = U.comp ((reflectionEvolution ψ).comp U.adjoint) := by
  apply Evolution.ext
  ext x
  have hx : U.op ((adjoint U.op) x) = x := by
    rw [← ContinuousLinearMap.comp_apply, Evolution.comp_adjoint_self,
      one_apply_eq_self]
  simp only [Evolution.comp_op, Evolution.adjoint_op, ContinuousLinearMap.comp_apply]
  rw [reflectionEvolution_op_apply, reflectionEvolution_op_apply, Evolution.evolvePure_vec, map_sub,
    map_smul, ContinuousLinearMap.adjoint_inner_right, hx]

end AxQM
