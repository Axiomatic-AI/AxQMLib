/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Mixture
import AxQM.Postulates.API.Entropy
import ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropyMixture

/-!
# AxQM — entropy of a mixture of quantum states (N&C Theorem 11.10, upper bound)

For a mixture `μ = State.mix p ρ = ∑ᵢ pᵢ ρᵢ` of quantum states `ρᵢ` with a probability
distribution `p`, the von Neumann entropy is bounded above by the average entropy of the components
plus the Shannon entropy of the weights:

`S(μ) ≤ ∑ᵢ pᵢ S(ρᵢ) + H(p)`

(Nielsen & Chuang, *Quantum Computation and Quantum Information*, Theorem 11.10, eq. (11.87),
upper-bound half). This is the `State`-level form of the operator bound
`ContinuousLinearMap.IsDensityOp.vonNeumannEntropy_mix_le_sum_add_entropy`.

## Proof

The operator bound is proved on `EuclideanSpace ℂ (Fin d)`; the `State` version transports it to the
abstract system space `S.space` along the standard orthonormal basis
`(stdOrthonormalBasis ℂ S.space).repr`, using the isometry invariance of the von Neumann entropy
(`ContinuousLinearMap.vonNeumannEntropy_conjStarAlgEquiv`) and of the density-operator and
strict-positivity properties (`LinearIsometryEquiv.conjStarAlgEquiv_isDensityOp_iff`,
`LinearIsometryEquiv.conjStarAlgEquiv_isStrictlyPositive_iff`).

## Faithfulness

The relative-entropy route to the bound requires each component `ρᵢ` to be **faithful** (strictly
positive spectrum, `IsStrictlyPositive (ρ i).op`); this is the finite-branch faithfulness convention
shared with Klein's inequality, joint convexity, and strong subadditivity. The general
(possibly rank-deficient) case is not covered by this statement. The equality condition —
equality iff the `ρᵢ` have orthogonal supports — is treated in
`AxQM/Postulates/API/EntropyOrthogonalMixture.lean` and
`AxQM/Postulates/API/EntropyMixtureReverse.lean`.

## Main results

* `AxQM.State.vonNeumannEntropy_mix_le` — `S(∑ᵢ pᵢ ρᵢ) ≤ ∑ᵢ pᵢ S(ρᵢ) + H(p)` for a
  mixture of faithful states.
-/

namespace AxQM

variable {S : QSystem}

/-- **Entropy of a mixture — upper bound** (Nielsen & Chuang, Theorem 11.10, eq. (11.87),
upper-bound half). For a probability distribution `p` and a family `ρ : ι → State S` of **faithful**
states (each `(ρ i).op` strictly positive), the von Neumann entropy of the mixture
`State.mix p hp hsum ρ` is bounded by the average component entropy plus the Shannon entropy
`H(p) = Real.entropy p` of the weights:

`S(∑ᵢ pᵢ ρᵢ) ≤ ∑ᵢ pᵢ S(ρᵢ) + H(p)`.

Lifts the operator bound
`ContinuousLinearMap.IsDensityOp.vonNeumannEntropy_mix_le_sum_add_entropy` to states.
That bound lives on `EuclideanSpace ℂ (Fin d)`; the proof transports the mixture into that space
along `(stdOrthonormalBasis ℂ S.space).repr`, where conjugation by the isometry preserves the von
Neumann entropy, the density-operator property, and strict positivity (so the component and mixture
hypotheses carry over and the entropies read straight back).

The **faithfulness** hypothesis is inherent to the relative-entropy route (see the module
docstring); the orthogonal-support equality condition is treated in
`AxQM/Postulates/API/EntropyMixtureReverse.lean`. -/
theorem State.vonNeumannEntropy_mix_le {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S)
    (hpos : ∀ i, IsStrictlyPositive (ρ i).op) :
    (State.mix p hp hsum ρ).vonNeumannEntropy
      ≤ ∑ i, p i * (ρ i).vonNeumannEntropy + Real.entropy p := by
  classical
  set μ := State.mix p hp hsum ρ with hμ
  -- Transport the mixture into `EuclideanSpace ℂ (Fin d)` along the standard orthonormal basis of
  -- `S.space`, where the operator-level bound is available. Conjugation by the isometry `e`
  -- preserves density, strict positivity, and the von Neumann entropy.
  let e := (stdOrthonormalBasis ℂ S.space).repr
  have hμop : μ.op = ∑ i, (p i : ℂ) • (ρ i).op := hμ ▸ State.mix_op p hp hsum ρ
  have hpos' : ∀ i, IsStrictlyPositive (e.conjStarAlgEquiv (ρ i).op) := fun i =>
    e.conjStarAlgEquiv_isStrictlyPositive_iff.mpr (hpos i)
  have hdens' : ∀ i, (e.conjStarAlgEquiv (ρ i).op).IsDensityOp := fun i =>
    e.conjStarAlgEquiv_isDensityOp_iff.mpr (ρ i).isDensity
  have hμdens' : (e.conjStarAlgEquiv μ.op).IsDensityOp :=
    e.conjStarAlgEquiv_isDensityOp_iff.mpr μ.isDensity
  have hμeq' : e.conjStarAlgEquiv μ.op = ∑ i, (p i : ℂ) • e.conjStarAlgEquiv (ρ i).op := by
    rw [hμop, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  have h := ContinuousLinearMap.IsDensityOp.vonNeumannEntropy_mix_le_sum_add_entropy
    hpos' hdens' hp hμdens' hμeq'
  simpa only [ContinuousLinearMap.vonNeumannEntropy_conjStarAlgEquiv, State.vonNeumannEntropy_def]
    using h

end AxQM
