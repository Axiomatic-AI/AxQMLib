/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RelativeEntropy
import AxQM.Postulates.API.Mixture
import AxQM.Postulates.API.EntropyComposite
import ToMathlib.Analysis.InnerProductSpace.QuantumConditionalEntropy

/-!
# AxQM — concavity of the quantum conditional entropy (N&C Corollary 11.13)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, **Corollary 11.13**: for a
composite system `A ⊗ B`, the quantum conditional entropy

`S(A|B) = S(A,B) − S(B)`

is **concave** in the state `ρ` of `A ⊗ B`. Averaging a family of states cannot decrease the
conditional entropy below the average of the conditional entropies:

`∑ᵢ pᵢ S(A|B)(ρᵢ) ≤ S(A|B)(∑ᵢ pᵢ ρᵢ)`.

## Proof (following N&C)

Let `d = dim A`. The reduced-state identity (grounded in the lemma
`ContinuousLinearMap.quantumRelativeEntropy_mapL_maximallyMixed_left_eq`)

`S(A|B)(ρ) = log d − D(ρ ‖ (I/d) ⊗ ρ_B)`,   `ρ_B = Tr_A ρ = ρ.reducedRight`,

expresses the conditional entropy as an **affine** image of the relative entropy against
`(I/d) ⊗ ρ_B`: the maximally mixed factor `I/d` is constant, and `ρ_B` is linear in `ρ`, so the
whole second argument is affine in `ρ`. The **joint convexity** of the relative entropy (N&C
Theorem 11.12, `State.quantumRelativeEntropy_jointly_convex_sum`) therefore transfers to concavity:
for the mixture `μ = ∑ᵢ pᵢ ρᵢ`, with `μ_B = ∑ᵢ pᵢ (ρᵢ)_B` and `(I/d) ⊗ μ_B = ∑ᵢ pᵢ (I/d) ⊗ (ρᵢ)_B`,

`D(μ ‖ (I/d) ⊗ μ_B) ≤ ∑ᵢ pᵢ D(ρᵢ ‖ (I/d) ⊗ (ρᵢ)_B)`,

and subtracting from `log d` (which `∑ᵢ pᵢ = 1` distributes) gives the concavity inequality.

The conditional entropies are written out as their defining differences
`S(·) − S(·.reducedRight)`, as in the conditional strong-subadditivity theorem
`State.condEntropy_add_le_add` (N&C Problem 11.4).

## Faithfulness

As with Klein's inequality, joint convexity, and strong subadditivity, the finite real-valued
relative-entropy engine requires the states to be **faithful** (strictly positive spectrum). The
mixture `∑ᵢ pᵢ ρᵢ` of faithful states is again faithful (`State.isStrictlyPositive_mix_op`, via the
convexity of the strictly-positive cone), so both sides apply on the faithful branch.
The fully general (possibly rank-deficient) statement follows by the same continuity argument over
faithful approximants, which is not carried out here.

## Main results

* `AxQM.State.quantumRelativeEntropy_maximallyMixed_tmul_reducedRight_eq` — the identity
  `D(ρ ‖ (I/d) ⊗ ρ_B) = log d + S(ρ_B) − S(ρ)`.
* `AxQM.State.vonNeumannEntropy_sub_reducedRight_concave` — Corollary 11.13, concavity of
  `S(A|B) = S(ρ) − S(ρ.reducedRight)`.
* `AxQM.State.isStrictlyPositive_mix_op`, `AxQM.State.mix_reducedRight_op` —
  supporting facts about probabilistic mixtures.
-/

open Module
open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **A probabilistic mixture of faithful states is faithful**: if every `ρ i` has strictly positive
density operator, so does the mixture `∑ᵢ pᵢ ρᵢ`. The strictly-positive operators form a convex cone
(`convex_isStrictlyPositive`), and the mixture is a convex combination of the `(ρ i).op`. -/
theorem State.isStrictlyPositive_mix_op {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S)
    (hpos : ∀ i, IsStrictlyPositive (ρ i).op) :
    IsStrictlyPositive (State.mix p hp hsum ρ).op := by
  simp only [State.mix_op, Complex.coe_smul]
  exact (Convex.sum_mem convex_isStrictlyPositive (fun i _ => hp i) hsum (fun i _ => hpos i) :
    (∑ i, p i • (ρ i).op) ∈ {a : S.space →L[ℂ] S.space | IsStrictlyPositive a})

/-- **The right-reduced state of a mixture is the mixture of the right-reduced states**:
`Tr_A (∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ (Tr_A ρᵢ)`, at the level of density operators. The partial trace is linear
(`LinearMap.partialTraceLeft_sum_smul`), so it commutes with the convex combination defining
`State.mix`. -/
theorem State.mix_reducedRight_op {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State (S ⊗ T)) :
    (State.mix p hp hsum ρ).reducedRight.op = ∑ i, (p i : ℂ) • (ρ i).reducedRight.op := by
  rw [State.reducedRight_op, State.mix_op]
  simp only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul,
      State.reducedRight_op]
  simp only [← map_smul, ← map_sum]
  congr 1
  exact LinearMap.partialTraceLeft_sum_smul (stdOrthonormalBasis ℂ S.space)
    (fun i => (p i : ℂ)) (fun i => (ρ i).op.toLinearMap)

/-- **The left-reduced state of a mixture is the mixture of the left-reduced states**:
`Tr_B (∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ (Tr_B ρᵢ)`, at the level of density operators. The `reducedLeft`
companion of `State.mix_reducedRight_op`: the partial trace is linear
(`LinearMap.partialTraceRight_sum_smul`), so it commutes with the convex combination defining
`State.mix`. -/
theorem State.mix_reducedLeft_op {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State (S ⊗ T)) :
    (State.mix p hp hsum ρ).reducedLeft.op = ∑ i, (p i : ℂ) • (ρ i).reducedLeft.op := by
  rw [State.reducedLeft_op, State.mix_op]
  simp only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul,
      State.reducedLeft_op]
  simp only [← map_smul, ← map_sum]
  congr 1
  exact LinearMap.partialTraceRight_sum_smul (stdOrthonormalBasis ℂ T.space)
    (fun i => (p i : ℂ)) (fun i => (ρ i).op.toLinearMap)

/-- **The conditional entropy as a relative entropy against `(I/d) ⊗ ρ_B`** (the state-level lift of
`ContinuousLinearMap.quantumRelativeEntropy_mapL_maximallyMixed_left_eq`): for a faithful state `ρ`
on `S ⊗ T` (with `d = dim S`),

`D(ρ ‖ (I/d) ⊗ ρ_B) = log d + S(ρ_B) − S(ρ)`,   `ρ_B = ρ.reducedRight`,

where `I/d = maximallyMixedState S`. Equivalently `S(ρ) − S(ρ_B) = log d − D(ρ ‖ (I/d) ⊗ ρ_B)`: the
conditional entropy `S(A|B)` is `log d` minus a relative entropy, the identity behind the concavity
of `S(A|B)` (N&C Corollary 11.13). -/
theorem State.quantumRelativeEntropy_maximallyMixed_tmul_reducedRight_eq [Nontrivial S.space]
    (ρ : State (S ⊗ T)) (hρ : IsStrictlyPositive ρ.op) :
    ρ.quantumRelativeEntropy ((maximallyMixedState S).tmul ρ.reducedRight)
      = Real.log (Module.finrank ℂ S.space) + ρ.reducedRight.vonNeumannEntropy
        - ρ.vonNeumannEntropy := by
  have : Nonempty (Fin (Module.finrank ℂ S.space)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  rw [State.quantumRelativeEntropy_def, State.tmul_op, maximallyMixedState_op,
    State.vonNeumannEntropy_def, State.vonNeumannEntropy_def]
  exact ContinuousLinearMap.quantumRelativeEntropy_mapL_maximallyMixed_left_eq
    (stdOrthonormalBasis ℂ S.space) ρ.isDensity hρ rfl

/-- **Concavity of the quantum conditional entropy** (Nielsen & Chuang, Corollary 11.13): for a
probability distribution `p` and a family `ρ : ι → State (S ⊗ T)` of **faithful** states, the
conditional entropy `S(A|B) = S(ρ) − S(ρ.reducedRight)` is concave —

`∑ᵢ pᵢ (S(ρᵢ) − S((ρᵢ)_B)) ≤ S(μ) − S(μ_B)`,   `μ = ∑ᵢ pᵢ ρᵢ = State.mix p hp hsum ρ`.

The conditional entropy is written out as `S(·) − S(·.reducedRight)` (see the module docstring).
The proof rewrites each conditional entropy via
`State.quantumRelativeEntropy_maximallyMixed_tmul_reducedRight_eq` as `log d − D(· ‖ (I/d) ⊗ ·_B)`
and applies the joint convexity of the relative entropy
(`State.quantumRelativeEntropy_jointly_convex_sum`); the `log d` terms cancel via `∑ᵢ pᵢ = 1`.
Faithfulness of the mixture is `State.isStrictlyPositive_mix_op`, and the affine dependence of the
second argument on `ρ` is threaded by `State.mix_reducedRight_op` and
`TensorProduct.mapL_sum_smul_right`. -/
theorem State.vonNeumannEntropy_sub_reducedRight_concave [Nontrivial S.space]
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (ρ : ι → State (S ⊗ T)) (hpos : ∀ i, IsStrictlyPositive (ρ i).op) :
    ∑ i, p i * ((ρ i).vonNeumannEntropy - (ρ i).reducedRight.vonNeumannEntropy) ≤
      (State.mix p hp hsum ρ).vonNeumannEntropy
        - (State.mix p hp hsum ρ).reducedRight.vonNeumannEntropy := by
  classical
  have : Nonempty (Fin (Module.finrank ℂ S.space)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  -- The mixture and each product state are faithful.
  have hμpos : IsStrictlyPositive (State.mix p hp hsum ρ).op :=
    State.isStrictlyPositive_mix_op p hp hsum ρ hpos
  have hσpos : ∀ i, IsStrictlyPositive ((maximallyMixedState S).tmul (ρ i).reducedRight).op := by
    intro i
    rw [State.tmul_op, maximallyMixedState_op]
    exact TensorProduct.mapL_isStrictlyPositive
      ContinuousLinearMap.isStrictlyPositive_finrank_inv_smul_one
      ((hpos i).of_partialTraceLeft_eq (stdOrthonormalBasis ℂ S.space) rfl)
  -- The two convex-combination hypotheses feeding joint convexity.
  have hρeq : (State.mix p hp hsum ρ).op = ∑ i, p i • (ρ i).op := by
    simp only [State.mix_op, Complex.coe_smul]
  have hσeq : ((maximallyMixedState S).tmul (State.mix p hp hsum ρ).reducedRight).op
      = ∑ i, p i • ((maximallyMixedState S).tmul (ρ i).reducedRight).op := by
    have hpt := TensorProduct.mapL_sum_smul_right (maximallyMixedState S).op
        (fun i => (p i : ℂ)) (fun i => (ρ i).reducedRight.op)
    rw [State.tmul_op, State.mix_reducedRight_op, hpt]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [State.tmul_op]; exact Complex.coe_smul (p i) _
  -- Joint convexity of the relative entropy against `(I/d) ⊗ ·`.
  have hjc := State.quantumRelativeEntropy_jointly_convex_sum (Finset.univ : Finset ι)
    (State.mix p hp hsum ρ)
    ((maximallyMixedState S).tmul (State.mix p hp hsum ρ).reducedRight)
    ρ (fun i => (maximallyMixedState S).tmul (ρ i).reducedRight) p
    (fun i _ => hpos i) (fun i _ => hσpos i) (fun i _ => hp i) hsum hρeq hσeq
  -- Rewrite every relative entropy via the conditional-entropy identity.
  rw [State.quantumRelativeEntropy_maximallyMixed_tmul_reducedRight_eq _ hμpos] at hjc
  have hidi : ∀ i, (ρ i).quantumRelativeEntropy ((maximallyMixedState S).tmul (ρ i).reducedRight)
      = Real.log (Module.finrank ℂ S.space) + (ρ i).reducedRight.vonNeumannEntropy
        - (ρ i).vonNeumannEntropy := fun i =>
    State.quantumRelativeEntropy_maximallyMixed_tmul_reducedRight_eq (ρ i) (hpos i)
  simp only [hidi] at hjc
  -- Distribute the `log d` term through the average (`∑ᵢ pᵢ = 1`).
  have hexp : ∑ i, p i * (Real.log (Module.finrank ℂ S.space)
      + (ρ i).reducedRight.vonNeumannEntropy - (ρ i).vonNeumannEntropy)
      = Real.log (Module.finrank ℂ S.space)
        + ∑ i, p i * ((ρ i).reducedRight.vonNeumannEntropy - (ρ i).vonNeumannEntropy) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hsum, one_mul]
    ring
  rw [hexp] at hjc
  -- The goal's average is the negation of the average appearing in `hjc`.
  have hrel : ∑ i, p i * ((ρ i).vonNeumannEntropy - (ρ i).reducedRight.vonNeumannEntropy)
      + ∑ i, p i * ((ρ i).reducedRight.vonNeumannEntropy - (ρ i).vonNeumannEntropy) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring
  linarith

end AxQM
