/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EntropyOrthogonalMixture
import AxQM.Postulates.API.EntropyComposite
import ToMathlib.Analysis.InnerProductSpace.PosNegPart
import ToMathlib.Analysis.InnerProductSpace.RankOneProjector

/-!
# AxQM — the joint entropy theorem (N&C Thm 11.8, part 5 / eq. (11.58))

The **joint entropy theorem** (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.8, part (5), eq. (11.58)): for a probability distribution `pᵢ`, an orthonormal family
of pure states `|i⟩` of a system `A`, and *arbitrary* states `ρᵢ` of a system `B`,

`S(∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ) = H(pᵢ) + ∑ᵢ pᵢ S(ρᵢ)`.

N&C obtains this "immediately from the preceding result": the block states `σᵢ := |i⟩⟨i| ⊗ ρᵢ`
have *mutually orthogonal supports* (their `A`-factors are the orthogonal one-dimensional ranges
of `|i⟩⟨i|`), so the orthogonal-support mixture identity of part (4) (eq. (11.57)) applies and gives
`S(∑ᵢ pᵢ σᵢ) = H(p) + ∑ᵢ pᵢ S(σᵢ)`; then tensor additivity `State.vonNeumannEntropy_tmul`
together with the purity of `|i⟩⟨i|` (`PureState.vonNeumannEntropy_toState_eq_zero`) collapses
each `S(σᵢ) = S(|i⟩⟨i|) + S(ρᵢ) = S(ρᵢ)`.

The one non-trivial step, orthogonality of the block supports, is discharged purely algebraically
by the *vanishing of the block operator products*: for `i ≠ j`,
`σᵢ.op · σⱼ.op = mapL (|i⟩⟨i| · |j⟩⟨j|) (ρᵢ.op · ρⱼ.op) = mapL 0 (…) = 0`, using multiplicativity of
the tensor map (`TensorProduct.mapL_mul`) and the orthonormal-projector annihilation lemma
`InnerProductSpace.rankOne_self_mul_rankOne_self_eq_zero_of_orthonormal`
(`|i⟩⟨i| · |j⟩⟨j| = ⟪i|j⟫ • |i⟩⟨j| = 0` since `⟪i|j⟫ = 0`). That pairwise annihilation is fed to
`State.vonNeumannEntropy_mix_eq_of_pairwise_op_mul_eq_zero` — the operator-product form of the
part-(4) identity, which converts vanishing products to orthogonal supports internally.

## Main results

The statement of Theorem 11.8 is in `AxQM/NC/Ch11/Theorem11_8.lean`; the declaration is here.

* `AxQM.State.vonNeumannEntropy_jointEntropyTheorem` — Nielsen–Chuang Theorem 11.8
  part (5), the joint entropy theorem `S(∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {A B : QSystem}

/-- **The joint entropy theorem** (Nielsen–Chuang Theorem 11.8, part (5), eq. (11.58)). For a
probability distribution `p`, an **orthonormal family of pure states** `|i⟩ = e i` of a system
`A` (`Orthonormal ℂ (fun i => (e i).vec)`), and an *arbitrary* family of states `ρ : ι → State B`,
the von Neumann entropy of the block-diagonal composite `∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ` is the Shannon entropy
of the weights plus the `p`-average of the component entropies:

`S(∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)`.

This applies the orthogonal-support mixture identity of part (4), through its operator-product
form `State.vonNeumannEntropy_mix_eq_of_pairwise_op_mul_eq_zero`, to the block states
`σᵢ = (e i).toState.tmul (ρ i)`: their operators pairwise annihilate,
`σᵢ.op · σⱼ.op = 0` for `i ≠ j` (the `A`-factors `|i⟩⟨i|`, `|j⟩⟨j|` compose to
`⟪i|j⟫ • |i⟩⟨j| = 0`), and `S(σᵢ) = S(ρᵢ)` by tensor additivity
`State.vonNeumannEntropy_tmul` with `S(|i⟩⟨i|) = 0`. -/
theorem State.vonNeumannEntropy_jointEntropyTheorem {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (e : ι → PureState A) (he : Orthonormal ℂ fun i => (e i).vec) (ρ : ι → State B) :
    (State.mix p hp hsum fun i => (e i).toState.tmul (ρ i)).vonNeumannEntropy
      = Real.entropy p + ∑ i, p i * (ρ i).vonNeumannEntropy := by
  classical
  set σ : ι → State (A.compose B) := fun i => (e i).toState.tmul (ρ i) with hσ
  -- The block operators as `|i⟩⟨i| ⊗ ρᵢ`.
  have hop : ∀ i, (σ i).op
      = TensorProduct.mapL ((InnerProductSpace.rankOne ℂ (e i).vec) (e i).vec) (ρ i).op := by
    intro i
    simp only [hσ]
    rw [State.tmul_op, PureState.toState_op]
  -- Distinct blocks have vanishing operator product: `|i⟩⟨i| · |j⟩⟨j| = ⟪i|j⟫ • |i⟩⟨j| = 0`.
  have hmul : ∀ i j, i ≠ j → (σ i).op * (σ j).op = 0 := by
    intro i j hij
    -- `σᵢ.op · σⱼ.op = mapL (|i⟩⟨i| · |j⟩⟨j|) (ρᵢ.op · ρⱼ.op)` by multiplicativity of `mapL`.
    have key : (σ i).op * (σ j).op
        = TensorProduct.mapL ((InnerProductSpace.rankOne ℂ (e i).vec) (e i).vec
            * (InnerProductSpace.rankOne ℂ (e j).vec) (e j).vec) ((ρ i).op * (ρ j).op) := by
      rw [hop i, hop j]
      exact (TensorProduct.mapL_mul _ _ _ _).symm
    -- The flag factors annihilate (`|i⟩⟨i| · |j⟩⟨j| = ⟪i|j⟫ • |i⟩⟨j| = 0`).
    rw [key, InnerProductSpace.rankOne_self_mul_rankOne_self_eq_zero_of_orthonormal he hij]
    exact TensorProduct.mapL_zero_left _
  -- Each block entropy is `S(ρᵢ)`: tensor additivity with the pure factor contributing `0`.
  have hS : ∀ i, (σ i).vonNeumannEntropy = (ρ i).vonNeumannEntropy := by
    intro i
    simp only [hσ]
    rw [State.vonNeumannEntropy_tmul, PureState.vonNeumannEntropy_toState_eq_zero, zero_add]
  rw [State.vonNeumannEntropy_mix_eq_of_pairwise_op_mul_eq_zero p hp hsum σ hmul]
  simp_rw [hS]

/-- **The joint entropy theorem, flag-on-the-right form.** For a probability distribution `p`, an
*arbitrary* family of states `ρ : ι → State A`, and an **orthonormal family of pure states**
`|i⟩ = e i` of a *second* system `B` (`Orthonormal ℂ (fun i => (e i).vec)`), the von Neumann entropy
of the block-diagonal composite `∑ᵢ pᵢ ρᵢ ⊗ |i⟩⟨i|` is again the Shannon entropy of the weights plus
the `p`-average of the component entropies:

`S(∑ᵢ pᵢ ρᵢ ⊗ |i⟩⟨i|) = H(p) + ∑ᵢ pᵢ S(ρᵢ)`.

This is `State.vonNeumannEntropy_jointEntropyTheorem` with the classical flag `|i⟩⟨i|` tensored
on the **right** rather than the left — the orientation needed when the flag is adjoined to a
bipartite payload `ρᵢ` and then re-associated (as in the concavity argument of N&C Exercise 11.25).
The proof is the mirror image of the left form: the block states `σᵢ := ρᵢ ⊗ |i⟩⟨i|` have pairwise
orthogonal supports because for `i ≠ j`, `σᵢ.op · σⱼ.op = mapL (ρᵢ.op · ρⱼ.op) (|i⟩⟨i| · |j⟩⟨j|) =
mapL (…) 0 = 0` (`TensorProduct.mapL_mul`, the annihilation lemma
`InnerProductSpace.rankOne_self_mul_rankOne_self_eq_zero_of_orthonormal`, and
`TensorProduct.mapL_zero_right`), so the orthogonal-support mixture identity applies (through its
operator-product form `State.vonNeumannEntropy_mix_eq_of_pairwise_op_mul_eq_zero`), and
`S(σᵢ) = S(ρᵢ) + S(|i⟩⟨i|) = S(ρᵢ)` by tensor additivity and the purity of the flag. -/
theorem State.vonNeumannEntropy_mix_tmul_toState_orthonormal_right {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (ρ : ι → State A) (e : ι → PureState B) (he : Orthonormal ℂ fun i => (e i).vec) :
    (State.mix p hp hsum fun i => (ρ i).tmul (e i).toState).vonNeumannEntropy
      = Real.entropy p + ∑ i, p i * (ρ i).vonNeumannEntropy := by
  classical
  set σ : ι → State (A.compose B) := fun i => (ρ i).tmul (e i).toState with hσ
  -- The block operators as `ρᵢ ⊗ |i⟩⟨i|`.
  have hop : ∀ i, (σ i).op
      = TensorProduct.mapL (ρ i).op ((InnerProductSpace.rankOne ℂ (e i).vec) (e i).vec) := by
    intro i
    simp only [hσ]
    rw [State.tmul_op, PureState.toState_op]
  -- Distinct blocks have vanishing operator product: the flag factors compose to zero.
  have hmul : ∀ i j, i ≠ j → (σ i).op * (σ j).op = 0 := by
    intro i j hij
    -- `σᵢ.op · σⱼ.op = mapL (ρᵢ.op · ρⱼ.op) (|i⟩⟨i| · |j⟩⟨j|)` by multiplicativity of `mapL`.
    have key : (σ i).op * (σ j).op
        = TensorProduct.mapL ((ρ i).op * (ρ j).op)
            ((InnerProductSpace.rankOne ℂ (e i).vec) (e i).vec
              * (InnerProductSpace.rankOne ℂ (e j).vec) (e j).vec) := by
      rw [hop i, hop j]
      exact (TensorProduct.mapL_mul _ _ _ _).symm
    -- The flag factors annihilate (`|i⟩⟨i| · |j⟩⟨j| = ⟪i|j⟫ • |i⟩⟨j| = 0`).
    rw [key, InnerProductSpace.rankOne_self_mul_rankOne_self_eq_zero_of_orthonormal he hij]
    exact TensorProduct.mapL_zero_right _
  -- Each block entropy is `S(ρᵢ)`: tensor additivity with the pure flag contributing `0`.
  have hS : ∀ i, (σ i).vonNeumannEntropy = (ρ i).vonNeumannEntropy := by
    intro i
    simp only [hσ]
    rw [State.vonNeumannEntropy_tmul, PureState.vonNeumannEntropy_toState_eq_zero, add_zero]
  rw [State.vonNeumannEntropy_mix_eq_of_pairwise_op_mul_eq_zero p hp hsum σ hmul]
  simp_rw [hS]

end AxQM
