/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Qudit
import AxQM.Postulates.API.Mixture
import AxQM.Postulates.API.ArakiLiebEqualityConditions
import AxQM.Postulates.API.RelativeEntropy
import AxQM.Postulates.API.QuditMeasurement
import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropyDiagonal

/-!
# AxQM — the POVM measurement outcome channel

The **measurement outcome channel** of a measurement `m : Measurement ι S`: the map sending a
state `ρ` of `S` to the *diagonal Born-distribution state*

`𝓜(ρ) = ∑_y p(y) |y⟩⟨y|`,   with `p(y) = Tr(E_y ρ)` the Born probability of outcome `y`,

on the classical outcome register, realised concretely as `qudit (Fintype.card ι)` with the
computational basis `|y⟩` (reindexed from `ι` by `Fintype.equivFin`, exactly as the Holevo
classical–quantum state `State.holevoCQState` realises its index register). This is the "measure and
record the outcome, forget the post-measurement state" channel — the non-selective measurement seen
as a preparation of a *classical* state whose eigenvalues are the outcome probabilities.

It is the object the modern proof of the Holevo bound (Nielsen & Chuang, Theorem 12.1) processes:
the classical mutual information `H(X:Y)` between Alice's label `X` and Bob's outcome `Y` is
expressed through the quantum relative entropies `D(𝓜(ρₓ)‖𝓜(ρ))`, which the measurement
data-processing inequality bounds by `D(ρₓ‖ρ)`, summing to the Holevo χ.

This file supplies the following pieces:

* `Measurement.measState` — the outcome channel `𝓜` as a state of the outcome register;
* `Measurement.measState_def` — its unfolding to the diagonal Born mixture;
* `Measurement.bornProb_mix` — the Born rule is affine over mixtures,
  `Tr(E_y ∑ₖ pₖ ρₖ) = ∑ₖ pₖ Tr(E_y ρₖ)` (the linearity the Holevo assembly consumes to identify the
  outcome marginal with the Born distribution of the mixture);
* `Measurement.measState_mix` — the outcome channel is affine, `𝓜(∑ₖ pₖ ρₖ) = ∑ₖ pₖ 𝓜(ρₖ)` (the
  channel linearity of the map, in place of an endomorphic `IsChannel`, which does not type-check
  for a system-changing map `State S → State (qudit …)`);
* `Measurement.vonNeumannEntropy_measState` — `S(𝓜(ρ)) = H(Tr(E_· ρ))`, the diagonal Born state's
  von Neumann entropy is the Shannon entropy of the Born distribution (the bridge to the classical
  `H(X:Y)` in the alternate Holevo-bound proof, N&C Problem 12.1(3));
* `Measurement.quantumRelativeEntropy_measState_eq_relativeEntropy_bornProb` — the relative entropy
  of two outcome states is the classical KL divergence of their Born distributions,
  `D(𝓜(ρ) ‖ 𝓜(σ)) = D_cl(p(·|ρ) ‖ p(·|σ))` (the outcome states are diagonal in the same
  computational basis, so the Umegaki relative entropy collapses to the classical one).
-/

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- The **measurement outcome channel** `𝓜(ρ) = ∑_y Tr(E_y ρ) |y⟩⟨y|` of a measurement
`m : Measurement ι S`: the state of the classical outcome register `qudit (Fintype.card ι)` whose
`|y⟩⟨y|` weight is the Born probability of outcome `y`. The outcome kets are the computational basis
`quditBasis` reindexed from `ι` by `Fintype.equivFin`; the weights `m.bornProb ρ` form a probability
distribution (`bornProb_nonneg`, `sum_bornProb_eq_one`), so this is a genuine `State`. -/
def measState (m : Measurement ι S) (ρ : State S) : State (qudit (Fintype.card ι)) :=
  State.mix (m.bornProb ρ) (m.bornProb_nonneg ρ) (m.sum_bornProb_eq_one ρ)
    (fun i => (quditBasis (Fintype.equivFin ι i)).toState)

/-- Unfolding lemma for the measurement outcome channel: `𝓜(ρ)` is the diagonal Born mixture
`∑_y p(y) |y⟩⟨y|` over the reindexed computational basis. -/
theorem measState_def (m : Measurement ι S) (ρ : State S) :
    m.measState ρ = State.mix (m.bornProb ρ) (m.bornProb_nonneg ρ) (m.sum_bornProb_eq_one ρ)
      (fun i => (quditBasis (Fintype.equivFin ι i)).toState) := rfl

/-- The **Born rule is affine over mixtures**: for an ensemble `{pₖ, ρₖ}` with mixture
`ρ = ∑ₖ pₖ ρₖ`, the outcome probability of `y` is the `p`-average of the component outcome
probabilities, `Tr(E_y ∑ₖ pₖ ρₖ) = ∑ₖ pₖ Tr(E_y ρₖ)`. Linearity of the trace and of operator
composition in the density operator, over the convex combination `State.mix_op`. -/
theorem bornProb_mix {κ : Type*} [Fintype κ] (m : Measurement ι S)
    (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1) (ρ : κ → State S) (i : ι) :
    m.bornProb (State.mix p hp hsum ρ) i = ∑ k, p k * m.bornProb (ρ k) i := by
  simp only [bornProb, POVM.toPMF_eq, State.mix_op, ContinuousLinearMap.comp_finsetSum,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.toLinearMap_sum,
        ContinuousLinearMap.toLinearMap_smul,
    map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun x _ => RCLike.re_ofReal_mul (p x) _

/-- The **measurement outcome channel is affine**: `𝓜(∑ₖ pₖ ρₖ) = ∑ₖ pₖ 𝓜(ρₖ)`. Both sides are
diagonal Born mixtures over the same outcome basis; the outcome weight of `y` matches on the two
sides by `bornProb_mix`. This is the channel-linearity of `measState` (an endomorphic `IsChannel`
does not type-check for the system-changing map `State S → State (qudit …)`). -/
theorem measState_mix {κ : Type*} [Fintype κ] (m : Measurement ι S)
    (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1) (ρ : κ → State S) :
    m.measState (State.mix p hp hsum ρ)
      = State.mix p hp hsum (fun k => m.measState (ρ k)) := by
  apply State.ext
  simp only [measState_def, State.mix_op, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_smul, bornProb_mix]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]

/-- **The von Neumann entropy of the outcome channel is the Shannon entropy of the Born
distribution**: `S(𝓜(ρ)) = H(Tr(E_· ρ))`. Since `𝓜(ρ) = ∑_y Tr(E_y ρ) |y⟩⟨y|` is a mixture of the
orthonormal computational-basis kets `|y⟩` with weights `m.bornProb ρ`, its spectrum is exactly the
Born distribution, and the entropy of an orthonormal-support mixture is the Shannon entropy of the
weights (`State.vonNeumannEntropy_mix_toState_orthonormal`, with the register basis orthonormal by
`quditBasis_equivFin_orthonormal`). This is the bridge that turns the Holevo χ of the
measure-and-record ensemble into the classical mutual information `H(X:Y)` in the alternate Holevo
bound proof (Nielsen & Chuang Problem 12.1(3)). -/
theorem vonNeumannEntropy_measState (m : Measurement ι S) (ρ : State S) :
    (m.measState ρ).vonNeumannEntropy = Real.entropy (m.bornProb ρ) := by
  rw [measState_def]
  exact State.vonNeumannEntropy_mix_toState_orthonormal (m.bornProb ρ) (m.bornProb_nonneg ρ)
    (m.sum_bornProb_eq_one ρ) (fun i => quditBasis (Fintype.equivFin ι i))
    (quditBasis_equivFin_orthonormal ι)

/-- **The quantum relative entropy of two measurement-outcome states is the classical KL divergence
of their Born distributions**: for a measurement `m` and states `ρ, σ`,

`D(𝓜(ρ) ‖ 𝓜(σ)) = D_cl(p(·|ρ) ‖ p(·|σ))`,   with `p(y|ρ) = Tr(E_y ρ) = m.bornProb ρ y`.

Both outcome states `𝓜(ρ), 𝓜(σ)` are diagonal in the *same* computational basis `|y⟩` of the
outcome register `qudit (Fintype.card ι)`, with eigenvalues the Born probabilities. Hence their
Umegaki relative entropy collapses to the classical relative entropy of the diagonals
(`ContinuousLinearMap.quantumRelativeEntropy_eq_relativeEntropy_of_isEigenbasis`). The equality is
unconditional — no faithfulness needed — since `Real.log 0 = 0` makes zero-probability outcomes
harmless on both sides.

This is the identity (Nielsen & Chuang, Theorem 12.1) that rewrites the classical mutual
information `H(X:Y)` of the Holevo bound as a sum of quantum relative entropies of the outcome
states `D(𝓜(ρₓ) ‖ 𝓜(ρ))`, on which the measurement data-processing inequality then acts. -/
theorem quantumRelativeEntropy_measState_eq_relativeEntropy_bornProb
    (m : Measurement ι S) (ρ σ : State S) :
    (m.measState ρ).quantumRelativeEntropy (m.measState σ)
      = Real.relativeEntropy (m.bornProb ρ) (m.bornProb σ) := by
  classical
  -- The outcome kets `|y⟩` form an orthonormal basis of the outcome register, indexed by `ι`.
  set b : OrthonormalBasis ι ℂ (qudit (Fintype.card ι)).space :=
    (quditOrthonormalBasis (Fintype.card ι)).reindex (Fintype.equivFin ι).symm with hb_def
  have hb : ∀ i, b i = (quditBasis (Fintype.equivFin ι i)).vec := by
    intro i
    rw [hb_def, OrthonormalBasis.reindex_apply, Equiv.symm_symm, quditOrthonormalBasis_apply]
  -- Each outcome state is diagonal in `b`, with the Born probability as eigenvalue.
  have hdiag : ∀ (τ : State S) (j : ι),
      (m.measState τ).op (b j) = (m.bornProb τ j : ℂ) • b j := by
    intro τ j
    rw [measState_def, State.mix_op, sum_apply, Finset.sum_eq_single j]
    · rw [smul_apply, PureState.toState_op, ← hb j,
        InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal j j, ite_eq_left rfl,
        one_smul]
    · intro i _ hij
      rw [smul_apply, PureState.toState_op, ← hb i,
        InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal i j, ite_eq_right hij,
        zero_smul, smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [State.quantumRelativeEntropy_def]
  exact ContinuousLinearMap.quantumRelativeEntropy_eq_relativeEntropy_of_isEigenbasis b
    (m.measState ρ).isDensity.isPositive.isSelfAdjoint
    (m.measState σ).isDensity.isPositive.isSelfAdjoint (hdiag ρ) (hdiag σ)

end Measurement

end AxQM
