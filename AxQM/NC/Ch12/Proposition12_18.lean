/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PurificationInvariance

/-!
# Nielsen & Chuang, Proposition 12.18 (information gain implies disturbance)

Information gain implies disturbance for non-orthogonal quantum states.

## What is formalised

The dilated form of N&C's proof is the faithful statement of the proposition's mathematical
content. N&C's "By the results of Section 8.2, we may assume without loss of generality …"
invokes the Stinespring/Ozawa dilation to reduce an arbitrary information-gathering process
to a **unitary interaction with an ancilla** — a separate deep result, not part of
Proposition 12.18's own claim. Proposition 12.18 *itself* is the argument N&C then gives
about that unitary interaction, which is exactly what is formalised here: the signal system
`S`, an ancilla `A`, a unitary `U` on `S ⊗ A`, and the no-disturbance product forms.

The **no-disturbance** hypothesis is modelled precisely as in N&C's Eqs. (12.175)/(12.176):
the joint output of the interaction is again a *product* state whose signal factor is
*unchanged*, `U(ψ ⊗ u) = ψ ⊗ v`. That the signal factor is literally `ψ` (rather than some
perturbed `ψ'`) *is* the statement that the signal is undisturbed; the ancilla is left in
some state `v`. The two signal states `ψ, φ` are non-orthogonal, `ψ.overlap φ ≠ 0`.

* `AxQM.ancilla_eq_of_undisturbed_probe` — the **core rigidity claim**
  (Eqs. 12.177–12.178): if the probe leaves both non-orthogonal signals undisturbed then
  the ancilla acquires the *same* state in both cases, `v = v'`. The probe therefore carries
  no information about which signal was present — no information gain.
* `AxQM.informationGain_implies_disturbance` — the **contrapositive** that gives
  the proposition its name: if the probe *gains information* (its two ancilla outcomes
  differ, `v ≠ v'`) then the simultaneous no-disturbance forms `U(ψ ⊗ u) = ψ ⊗ v`,
  `U(φ ⊗ u) = φ ⊗ v'` cannot both hold — i.e. at least one signal must be disturbed.

The proofs use the following results of `AxQM/Postulates/API/`: a unitary preserves overlaps
(`Evolution.overlap_evolvePure`), product overlaps factorise (`PureState.overlap_tmul`), a
state's self-overlap is `1` (`PureState.overlap_self`), and unit overlap pins the state
(`PureState.eq_of_overlap_eq_one`).

## Proof

`U` preserves overlaps (`Evolution.overlap_evolvePure`), so from the no-disturbance forms
`⟨ψ ⊗ v | φ ⊗ v'⟩ = ⟨ψ ⊗ u | φ ⊗ u⟩`. Both product overlaps factorise
(`PureState.overlap_tmul`) and `⟨u|u⟩ = 1` (`PureState.overlap_self`), giving
`⟨ψ|φ⟩ ⟨v|v'⟩ = ⟨ψ|φ⟩` (Eq. 12.177). Cancelling the nonzero `⟨ψ|φ⟩` (`mul_left_cancel₀`, the
non-orthogonality hypothesis) yields `⟨v|v'⟩ = 1` (Eq. 12.178), whence `v = v'`
(`PureState.eq_of_overlap_eq_one`).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S A : QSystem}

/-- **Proposition 12.18, core rigidity (Eqs. 12.177–12.178).** Let `ψ, φ` be non-orthogonal
pure states of the signal system `S` (`ψ.overlap φ ≠ 0`), and let a unitary interaction `U`
on `S ⊗ A` couple the signal to an ancilla prepared in the standard state `u`, *without
disturbing* the signal: the joint output is again a product state with the signal factor
unchanged, `U(ψ ⊗ u) = ψ ⊗ v` and `U(φ ⊗ u) = φ ⊗ v'`. Then the ancilla acquires the
**same** state in both cases, `v = v'`, so the probe carries no information about which
signal was present.

`U` preserves overlaps (`Evolution.overlap_evolvePure`), so
`⟨ψ ⊗ v | φ ⊗ v'⟩ = ⟨ψ ⊗ u | φ ⊗ u⟩`; the product overlaps factorise
(`PureState.overlap_tmul`) and `⟨u|u⟩ = 1` (`PureState.overlap_self`), giving
`⟨ψ|φ⟩ ⟨v|v'⟩ = ⟨ψ|φ⟩`. Cancelling the nonzero `⟨ψ|φ⟩` forces `⟨v|v'⟩ = 1`, whence `v = v'`
(`PureState.eq_of_overlap_eq_one`). -/
theorem ancilla_eq_of_undisturbed_probe
    {ψ φ : PureState S} {u v v' : PureState A} {U : Evolution (S ⊗ A)}
    (hnonorth : ψ.overlap φ ≠ 0)
    (hψ : U.evolvePure (ψ ⊗ u) = ψ ⊗ v)
    (hφ : U.evolvePure (φ ⊗ u) = φ ⊗ v') :
    v = v' := by
  have base : (U.evolvePure (ψ ⊗ u)).overlap (U.evolvePure (φ ⊗ u))
      = (ψ ⊗ u).overlap (φ ⊗ u) := U.overlap_evolvePure _ _
  rw [hψ, hφ, PureState.overlap_tmul, PureState.overlap_tmul, PureState.overlap_self,
    mul_one] at base
  refine PureState.eq_of_overlap_eq_one (mul_left_cancel₀ hnonorth ?_)
  rw [mul_one]; exact base

/-- **Proposition 12.18 (information gain implies disturbance).** The contrapositive reading
that gives the proposition its name. For non-orthogonal signal states `ψ, φ`
(`ψ.overlap φ ≠ 0`) and a unitary probe `U` on `S ⊗ A` with ancilla prepared in `u`, if the
probe *gains information* — its two possible ancilla outcomes `v, v'` differ — then the
signal cannot have been left undisturbed in both cases: the simultaneous no-disturbance forms
`U(ψ ⊗ u) = ψ ⊗ v` and `U(φ ⊗ u) = φ ⊗ v'` cannot both hold. Information gain is possible only
at the expense of disturbing the signal. Immediate from `ancilla_eq_of_undisturbed_probe`. -/
theorem informationGain_implies_disturbance
    {ψ φ : PureState S} {u v v' : PureState A} {U : Evolution (S ⊗ A)}
    (hnonorth : ψ.overlap φ ≠ 0) (hgain : v ≠ v') :
    ¬ (U.evolvePure (ψ ⊗ u) = ψ ⊗ v ∧ U.evolvePure (φ ⊗ u) = φ ⊗ v') := by
  rintro ⟨hψ, hφ⟩
  exact hgain (ancilla_eq_of_undisturbed_probe hnonorth hψ hφ)

end AxQM
