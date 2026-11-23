/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Theorem9_4
import AxQM.NC.Ch2.Exercise2_81
import AxQM.Postulates.API.PurificationInvariance

/-!
# Nielsen & Chuang, Exercise 9.15 (Uhlmann's theorem with one purification fixed)

Show F(rho,sigma)=max over purifications of sigma with psi fixed purification of rho.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 9.15 (p. 411).

Uhlmann's theorem itself (N&C Theorem 9.4, `State.isGreatest_norm_overlap_purification`) writes the
fidelity `F(ρ, σ)` as the greatest overlap `‖⟨ψ|φ⟩‖` maximized over **both** a purification `|ψ⟩` of
`ρ` and a purification `|φ⟩` of `σ`. This exercise strengthens that: it is enough to fix *any one*
purification `|ψ⟩` of `ρ` and maximize over purifications `|φ⟩` of `σ` alone — the maximum is still
`F(ρ, σ)`, independent of which purification of `ρ` was fixed.

## The statement

`State.isGreatest_norm_overlap_purification_fixed` uses Theorem 9.4's vocabulary exactly, but
with `ψ` a *fixed hypothesis* rather than an existential in the set:

* `ψ : PureState (S ⊗ S)` is a fixed purification of `ρ` (`hψ : ψ.toState.reducedLeft = ρ`), the
  ancilla being a copy of the system `S` (N&C's "system `R`, a copy of `Q`");
* the maximization ranges only over `φ : PureState (S ⊗ S)` with `φ.toState.reducedLeft = σ`;
* the value is `ρ.fidelity σ`, packaged as an `IsGreatest` (attained **and** an upper bound),
  matching N&C's `max`.

## Proof

The set of overlaps `{‖ψ.overlap φ‖ | φ purifies σ}` for the *fixed* `ψ` is shown to **equal** the
full two-sided Uhlmann set `{‖ψ'.overlap φ‖ | ψ' purifies ρ, φ purifies σ}`; `IsGreatest` then
transfers from Theorem 9.4 by rewriting. The nontrivial inclusion (full ⊆ fixed) is where the
freedom in purifications enters: given any pair `(ψ', φ')` with `ψ'` a purification of `ρ`,

* since `ψ` and `ψ'` both purify `ρ`, N&C Exercise 2.81
  (`PureState.exists_evolution_tmul_id_evolvePure_eq`) supplies a unitary `U` on the ancilla with
  `ψ = (I_S ⊗ U) ψ'`;
* then `φ := (I_S ⊗ U) φ'` is again a purification of `σ`
  (`PureState.reducedLeft_evolvePure_tmul_id`: an ancilla unitary preserves the left marginal), and
* `‖ψ.overlap φ‖ = ‖((I_S ⊗ U)ψ').overlap ((I_S ⊗ U)φ')‖ = ‖ψ'.overlap φ'‖`
  (`Evolution.overlap_evolvePure`: a unitary preserves overlaps),

so every achievable value with `ψ'` free is already achievable with `ψ` fixed. The reverse
inclusion is immediate (`ψ` itself purifies `ρ`).

## Faithfulness

N&C fix `|ψ⟩` to be *any* purification of `ρ` and quantify the claim over that choice; the theorem
takes `ψ` as an arbitrary hypothesis satisfying `ψ.toState.reducedLeft = ρ`, so it holds for every
purification, exactly as stated. The maximization being **attained** (`IsGreatest`, not a mere
supremum) is faithful to N&C's `max`. As in Theorem 9.4, "a copy of `Q`" is realized by the system
`S` itself, so the doubled system is `S ⊗ S`.

## Main statements

* `State.isGreatest_norm_overlap_purification_fixed` — Exercise 9.15, `(9.72)`:
  `F(ρ, σ) = max_{|φ⟩} ‖⟨ψ|φ⟩‖` over purifications `φ` of `σ`, for any fixed purification `ψ`
  of `ρ`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.15**, `(9.72)`: for any **fixed** purification `ψ` of `ρ` into
the doubled system `S ⊗ S`, the fidelity `F(ρ, σ)` is the **greatest overlap magnitude** `‖⟨ψ|φ⟩‖`
achievable over all purifications `φ` of `σ`:
`F(ρ, σ) = max_{|φ⟩} |⟨ψ|φ⟩|`.

This strengthens Uhlmann's theorem (N&C Theorem 9.4,
`State.isGreatest_norm_overlap_purification`), which maximizes over purifications of *both* `ρ` and
`σ`: here the purification of `ρ` is fixed and only `φ` varies, yet the maximum is still `F(ρ, σ)`,
whatever purification `ψ` of `ρ` was chosen. Packaged as `IsGreatest`: `ρ.fidelity σ` is attained by
some purification `φ` of `σ` and upper-bounds every achievable overlap.

The achievable set for the fixed `ψ` is shown to coincide with Theorem 9.4's full two-sided set, so
`IsGreatest` transfers. The key inclusion uses freedom in purifications (N&C Exercise 2.81,
`PureState.exists_evolution_tmul_id_evolvePure_eq`): a unitary `U` on the ancilla with
`ψ = (I_S ⊗ U) ψ'` turns any optimal pair `(ψ', φ')` into `(ψ, (I_S ⊗ U) φ')`, preserving the
overlap magnitude (`Evolution.overlap_evolvePure`) and the purified state
(`PureState.reducedLeft_evolvePure_tmul_id`). -/
theorem State.isGreatest_norm_overlap_purification_fixed (ρ σ : State S)
    (ψ : PureState (S ⊗ S)) (hψ : ψ.toState.reducedLeft = ρ) :
    IsGreatest
      {r : ℝ | ∃ φ : PureState (S ⊗ S),
        φ.toState.reducedLeft = σ ∧ r = ‖ψ.overlap φ‖}
      (ρ.fidelity σ) := by
  -- The fixed-`ψ` achievable set is exactly Theorem 9.4's full two-sided Uhlmann set.
  have hset :
      {r : ℝ | ∃ φ : PureState (S ⊗ S), φ.toState.reducedLeft = σ ∧ r = ‖ψ.overlap φ‖}
      = {r : ℝ | ∃ ψ' φ : PureState (S ⊗ S),
          ψ'.toState.reducedLeft = ρ ∧ φ.toState.reducedLeft = σ ∧ r = ‖ψ'.overlap φ‖} := by
    ext r
    simp only [Set.mem_ofPred_eq]
    constructor
    · -- fixed ⊆ full: take `ψ' := ψ`, which purifies `ρ` by `hψ`.
      rintro ⟨φ, hφ, rfl⟩
      exact ⟨ψ, φ, hψ, hφ, rfl⟩
    · -- full ⊆ fixed: transport the optimal pair to the fixed `ψ` by an ancilla unitary.
      rintro ⟨ψ', φ', hψ', hφ', rfl⟩
      obtain ⟨U, hU⟩ := PureState.exists_evolution_tmul_id_evolvePure_eq ψ' ψ (by rw [hψ', hψ])
      refine ⟨((Evolution.id (S := S)).tmul U).evolvePure φ', ?_, ?_⟩
      · rw [PureState.reducedLeft_evolvePure_tmul_id]; exact hφ'
      · rw [hU, Evolution.overlap_evolvePure]
  rw [hset]
  exact ρ.isGreatest_norm_overlap_purification σ

end AxQM
