/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch11.Theorem11_15
import AxQM.Postulates.API.EntropyJointTheorem
import AxQM.Postulates.API.Qudit
import AxQM.Core.ConditionalEntropy

/-!
# N&C Exercise 11.25 — concavity of the conditional entropy from strong subadditivity

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.25, p. 521.

Show concavity of the quantum conditional entropy follows from strong subadditivity.

The **quantum conditional entropy** `S(A|B) = S(A,B) − S(B)` is a **concave** function of the
state `ρ` of `A ⊗ B`: for a probability distribution `p` and a family `ρᵢ` of states,

`∑ᵢ pᵢ S(A|B)(ρᵢ) ≤ S(A|B)(∑ᵢ pᵢ ρᵢ)`.

This is the exact statement of N&C **Corollary 11.13** (concavity of the conditional entropy); the
present exercise asks for the *reverse* implication of the way N&C first obtained it — there,
concavity was assumed and strong subadditivity derived (Theorem 11.14); here concavity is *deduced
from* strong subadditivity. The independent relative-entropy proof of the same statement (N&C's own
proof of Corollary 11.13, needing each `ρᵢ` faithful) lives in
`AxQM/Postulates/API/ConditionalEntropyConcave.lean`; the strong-subadditivity proof given
here needs **no faithfulness hypothesis**, matching the fully general statement.

## The auxiliary-system (flag-register) argument

Following the hint, introduce an auxiliary "flag" system `C` recording the branch index `i` in an
orthonormal family of pure states `|i⟩`, and form the classical–quantum state

`σ := ∑ᵢ pᵢ ρᵢ ⊗ |i⟩⟨i|`   on `A ⊗ (B ⊗ C)`

(re-associated to the `A ⊗ (B ⊗ C)` grouping). Strong subadditivity in the form *conditioning
reduces the conditional entropy*, `S(A|B,C) ≤ S(A|B)`
(`State.conditioning_reduces_vonNeumannEntropy'`, N&C Theorem 11.15(1)), applied to `σ` gives
exactly concavity, because the flag makes the two block entropies split:

* `S(A|B,C)_σ = S(σ) − S(σ_{BC}) = ∑ᵢ pᵢ (S(ρᵢ) − S((ρᵢ)_B)) = ∑ᵢ pᵢ S(A|B)(ρᵢ)`, using the joint
  entropy theorem `S(∑ᵢ pᵢ · ⊗ |i⟩⟨i|) = H(p) + ∑ᵢ pᵢ S(·)` on the whole state and its `B ⊗ C`
  marginal — the two `H(p)` terms cancel
  (`State.vonNeumannEntropy_mix_tmul_toState_orthonormal_right`);
* `S(A|B)_σ = S(σ_{AB}) − S(σ_B) = S(∑ᵢ pᵢ ρᵢ) − S((∑ᵢ pᵢ ρᵢ)_B) = S(A|B)(∑ᵢ pᵢ ρᵢ)`, because the
  flag `C` is traced out of `σ_{AB}` and `σ_B` (`Tr_C |i⟩⟨i| = 1`), leaving the plain mixture.

The four marginals of `σ` are read off with the same re-association machinery used for the pure
ancilla in `MutualInformationAncilla` (`State.reducedRight_congr_symm_assoc_tmul`,
`State.congr_mix`, `State.reducedLeft_mix`, `State.reducedRight_mix`, `State.reducedLeft_tmul`), and
the flag is a `qudit` computational basis reindexed to `ι` (`quditBasis`, `quditBasis_orthonormal`).

## Main result

* `AxQM.State.condVonNeumannEntropy_concave` — concavity of the quantum conditional
  entropy, `∑ᵢ pᵢ S(A|B)(ρᵢ) ≤ S(A|B)(∑ᵢ pᵢ ρᵢ)`, deduced from strong subadditivity.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {A B : QSystem}

/-- **Concavity of the quantum conditional entropy** (Nielsen & Chuang, Corollary 11.13, deduced
from strong subadditivity per Exercise 11.25). For a probability distribution `p` and a family of
states `ρ : ι → State (A ⊗ B)`, the conditional entropy `S(A|B) = S(A,B) − S(B)` satisfies

`∑ᵢ pᵢ S(A|B)(ρᵢ) ≤ S(A|B)(∑ᵢ pᵢ ρᵢ)`.

The proof follows N&C's hint: introduce an orthonormal flag family `|i⟩ = e i` on an auxiliary
`qudit` system `C`, form the re-associated classical–quantum state
`σ := ∑ᵢ pᵢ (ρᵢ ⊗ |i⟩⟨i|)` on `A ⊗ (B ⊗ C)`, and apply *conditioning reduces the conditional
entropy* `S(A|B,C)_σ ≤ S(A|B)_σ` (`State.conditioning_reduces_vonNeumannEntropy'`). The joint
entropy theorem (flag-right form) evaluates `S(σ)` and `S(σ_{BC})` as `H(p) + ∑ pᵢ S(ρᵢ)` and
`H(p) + ∑ pᵢ S((ρᵢ)_B)` (the `H(p)`'s cancel in `S(A|B,C)`), while tracing out the flag from
`σ_{AB}`, `σ_B` leaves the plain mixture `∑ pᵢ ρᵢ` and its `B`-marginal, so `S(A|B)_σ` is the
conditional entropy of the mixture. -/
theorem State.condVonNeumannEntropy_concave {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State (A ⊗ B)) :
    ∑ i, p i * (ρ i).condVonNeumannEntropy
      ≤ (State.mix p hp hsum ρ).condVonNeumannEntropy := by
  classical
  -- The flag system `C`: a `qudit` of dimension `|ι|`, with the computational basis reindexed to
  -- `ι` giving an orthonormal family of pure "branch label" states `|i⟩ = e i`.
  set C : QSystem := qudit (Fintype.card ι) with hC
  set e : ι → PureState C := fun i => quditBasis (Fintype.equivFin ι i) with he_def
  have he : Orthonormal ℂ fun i => (e i).vec :=
    (quditBasis_orthonormal (Fintype.card ι)).comp _ (Fintype.equivFin ι).injective
  -- The flag-tagged mixture `μf = ∑ᵢ pᵢ (ρᵢ ⊗ |i⟩⟨i|)` on `(A ⊗ B) ⊗ C`, and its re-association
  -- `τ = σ` to `A ⊗ (B ⊗ C)` where strong subadditivity is stated.
  set μf : State ((A ⊗ B) ⊗ C) := State.mix p hp hsum (fun i => (ρ i).tmul (e i).toState) with hμf
  set τ : State (A ⊗ (B ⊗ C)) := State.congr (QSystem.assoc A B C).symm μf with hτ
  -- `τ` is the mixture of the individually re-associated blocks (transport commutes with mixing).
  have hτeq : τ = State.mix p hp hsum
      (fun i => State.congr (QSystem.assoc A B C).symm ((ρ i).tmul (e i).toState)) := by
    rw [hτ, hμf, State.congr_mix]
  -- The `B ⊗ C`-marginal of `τ` is the flag-tagged mixture of the `B`-marginals.
  have hτR : τ.reducedRight
      = State.mix p hp hsum (fun i => (ρ i).reducedRight.tmul (e i).toState) := by
    rw [hτeq, State.reducedRight_mix]
    simp_rw [State.reducedRight_congr_symm_assoc_tmul]
  -- (a)  `S(σ) = S(A,B,C) = H(p) + ∑ᵢ pᵢ S(ρᵢ)` (joint entropy theorem, flag on the right).
  have ha : τ.vonNeumannEntropy = Real.entropy p + ∑ i, p i * (ρ i).vonNeumannEntropy := by
    rw [hτ, State.vonNeumannEntropy_congr, hμf]
    exact State.vonNeumannEntropy_mix_tmul_toState_orthonormal_right p hp hsum ρ e he
  -- (b)  `S(σ_{BC}) = S(B,C) = H(p) + ∑ᵢ pᵢ S((ρᵢ)_B)` (joint entropy theorem, `B`-marginals).
  have hb : τ.reducedRight.vonNeumannEntropy
      = Real.entropy p + ∑ i, p i * (ρ i).reducedRight.vonNeumannEntropy := by
    rw [hτR]
    exact State.vonNeumannEntropy_mix_tmul_toState_orthonormal_right p hp hsum
      (fun i => (ρ i).reducedRight) e he
  -- (c)  `S(σ_{AB}) = S(A,B) = S(∑ᵢ pᵢ ρᵢ)`: re-associating back and tracing out the flag `C`
  --      recovers the plain mixture.
  have hc : (τ.congr (QSystem.assoc A B C)).reducedLeft.vonNeumannEntropy
      = (State.mix p hp hsum ρ).vonNeumannEntropy := by
    have hround : τ.congr (QSystem.assoc A B C) = μf := by
      rw [hτ]; exact State.congr_congr_symm _ _
    rw [hround, hμf, State.reducedLeft_mix]
    simp_rw [State.reducedLeft_tmul]
  -- (d)  `S(σ_B) = S(B) = S((∑ᵢ pᵢ ρᵢ)_B)`: tracing out `A` then the flag `C` leaves the
  --      `B`-marginal of the mixture.
  have hd : τ.reducedRight.reducedLeft.vonNeumannEntropy
      = (State.mix p hp hsum ρ).reducedRight.vonNeumannEntropy := by
    rw [hτR, State.reducedLeft_mix]
    simp_rw [State.reducedLeft_tmul]
    rw [State.reducedRight_mix]
  -- Strong subadditivity: `S(A|B,C)_σ ≤ S(A|B)_σ`, with the four marginals substituted.
  have key := State.conditioning_reduces_vonNeumannEntropy' τ
  rw [ha, hb, hc, hd] at key
  -- The average of the branch conditional entropies is the difference of the two averaged sums.
  have hlhs : ∑ i, p i * (ρ i).condVonNeumannEntropy
      = (∑ i, p i * (ρ i).vonNeumannEntropy)
        - ∑ i, p i * (ρ i).reducedRight.vonNeumannEntropy := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [State.condVonNeumannEntropy_def, mul_sub]
  rw [State.condVonNeumannEntropy_def, hlhs]
  linarith [key]

end AxQM
