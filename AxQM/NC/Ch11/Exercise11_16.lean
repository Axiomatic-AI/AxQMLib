/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EntropyOrthogonalMixture
import AxQM.Postulates.API.EntropyMixtureReverse
import AxQM.Postulates.API.EntropyConcavity
import AxQM.Postulates.API.PureMarginalEntropy
import AxQM.Postulates.API.ArakiLiebEqualityConditions
import AxQM.Postulates.API.Qubit
import AxQM.Postulates.API.Entropy
import AxQM.NC.Ch2.Exercise2_74
import AxQM.NC.Ch11.Theorem11_10

/-!
# Nielsen & Chuang, Exercise 11.16 — equality conditions for the triangle inequality

**Exercise 11.16 (Equality conditions for `S(A,B) ≥ S(B) − S(A)`), N&C p. 516.** Let
`ρ^{AB} = ∑ᵢ λᵢ |i⟩⟨i|` be a spectral decomposition of `ρ^{AB}`. The exercise asks to show that
the Araki–Lieb (triangle) inequality is saturated, `S(A,B) = S(B) − S(A)`, **if and only if** the
operators `ρ^A_i ≡ tr_B(|i⟩⟨i|)` have a common eigenbasis, and the `ρ^B_i ≡ tr_A(|i⟩⟨i|)` have
orthogonal support.

## The statement is false as printed

The stated condition is **not sufficient**: a common eigenbasis for the `ρ^A_i` is too weak. The
equality forces the `ρ^A_i` (over the eigenvalues `λᵢ > 0`) to be *identical*, not merely
simultaneously diagonalisable. Concretely, `S(A) + H(λ) = S(B)` combines the concavity bound
`S(ρ^A) = S(∑ᵢ λᵢ ρ^A_i) ≥ ∑ᵢ λᵢ S(ρ^A_i)` with the mixture upper bound
`S(ρ^B) = S(∑ᵢ λᵢ ρ^B_i) ≤ H(λ) + ∑ᵢ λᵢ S(ρ^B_i)` and `S(ρ^A_i) = S(ρ^B_i)` (pure `|i⟩`); equality
throughout requires *concavity equality* for the `ρ^A_i` (all equal, N&C Exercise 11.18) — strictly
stronger than a common eigenbasis — together with the orthogonal-support condition on the `ρ^B_i`.
The "`⟹`" direction of N&C's biconditional is correct (equality does imply a common eigenbasis and
orthogonal support), but the "`⟸`" direction fails.

## The corrected statement (this file)

`vonNeumannEntropy_mix_eq_reducedRight_sub_reducedLeft_iff` is the biconditional N&C evidently
intends, with the first condition strengthened from "common eigenbasis" to **"identical"**. For a
(reduced) spectral decomposition `ρ^{AB} = ∑ᵢ λᵢ |i⟩⟨i|` — the `|i⟩` orthonormal (recorded as
pairwise orthogonal supports of the pure projectors `|i⟩⟨i|`) with strictly positive `λᵢ > 0` —
the triangle inequality is saturated `S(A,B) = S(B) − S(A)` **iff**

* the left marginals `ρ^A_i = tr_B(|i⟩⟨i|)` are all **equal**, and
* the right marginals `ρ^B_i = tr_A(|i⟩⟨i|)` have **orthogonal support**.

We take the *reduced* decomposition (the strictly-positive eigenvalues, which is the natural reading
of "the spectral decomposition ∑ᵢ λᵢ|i⟩⟨i|"): a zero eigenvalue contributes nothing to any of the
three entropies and its eigenvector is an arbitrary basis vector of `ker ρ^{AB}`, so the marginals
`ρ^A_i, ρ^B_i` it would contribute are physically irrelevant. This loses no content — every state
has such a decomposition — and it makes both conditions range over exactly the meaningful
eigenprojectors.

The proof reads `S(A,B) = H(λ)` off the orthogonal pure components and decomposes the triangle gap
as a sum of two non-negative gaps,
`S(A) + H(λ) − S(B) = (S(A) − ∑ᵢ λᵢ S(ρ^A_i)) + (H(λ) + ∑ᵢ λᵢ S(ρ^B_i) − S(B))`, using the purity
identity `S(ρ^A_i) = S(ρ^B_i)` (`PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`). The
first bracket is the concavity gap (`State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix'`,
`≥ 0`, vanishing iff the `ρ^A_i` coincide — `State.vonNeumannEntropy_mix_eq_sum_iff'`, Ex 11.18);
the second is the entropy-of-a-mixture gap (`State.vonNeumannEntropy_mix_le'`, `≥ 0`, vanishing iff
the `ρ^B_i` have orthogonal support — `State.vonNeumannEntropy_mix_eq_iff_orthogonal`, Thm 11.10).
A sum of two non-negatives is zero iff both are, which yields the biconditional.

## The counterexample (this file)

The maximally classically-correlated two-qubit state

`ρ^{AB} = classicalCorrQubits = ½ |00⟩⟨00| + ½ |11⟩⟨11|`

is a spectral decomposition with orthonormal eigenvectors `|00⟩, |11⟩` (`classicalCorrKet 0/1`) and
eigenvalues `½, ½`. Its eigenprojector marginals are the computational-basis projectors:
`ρ^A_i = tr_B(|ii⟩⟨ii|) = |i⟩⟨i|` and `ρ^B_i = tr_A(|ii⟩⟨ii|) = |i⟩⟨i|`. Hence

* `classicalCorr_reducedLeft_hasCommonEigenbasis` — the `ρ^A_i` **have a common eigenbasis** (the
  computational basis diagonalises both `|0⟩⟨0|` and `|1⟩⟨1|`): N&C's first condition holds;
* `classicalCorr_reducedRight_orthogonalSupports` — the `ρ^B_i` **have orthogonal support**
  (`|0⟩⟨0|`, `|1⟩⟨1|` are supported on orthogonal lines): N&C's second condition holds;

yet the triangle inequality is **strict**, `S(A,B) = log 2 ≠ 0 = S(B) − S(A)`, because
`S(A,B) = log 2` (`classicalCorrQubits_vonNeumannEntropy`) while both marginals are maximally mixed,
`S(A) = S(B) = log 2` (`classicalCorrQubits_reduced{Left,Right}_vonNeumannEntropy`). The refutation
of the printed biconditional's sufficiency is `classicalCorr_arakiLieb_condition_not_sufficient`.

## Design

All three entropies are read off the orthogonal-support mixture identity (N&C Theorem 11.8 part 4,
`State.vonNeumannEntropy_mix_orthogonalSupport`): `S(∑ᵢ pᵢ ρᵢ) = H(p) + ∑ᵢ pᵢ S(ρᵢ)`, with pure
`|00⟩⟨00|, |11⟩⟨11|` (resp. `|0⟩⟨0|, |1⟩⟨1|`) whose entropies vanish, giving `H(½,½) = log 2`. The
marginals are evaluated with `State.reducedLeft_mix`/`reducedRight_mix` (partial trace is linear)
and `reducedLeft_toState_tmul`/`reducedRight_toState_tmul` (`tr(|ii⟩⟨ii|) = |i⟩⟨i|`). The predicates
`State.HasCommonEigenbasis` / `State.OrthogonalSupports` (the N&C conditions) are defined
in `AxQM/Postulates/API/ArakiLiebEqualityConditions.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ## The corrected equality condition (the intended statement of Exercise 11.16) -/

/-- **Nielsen & Chuang, Exercise 11.16, corrected.** Let `ρ^{AB} = ∑ᵢ λᵢ |i⟩⟨i|` be a (reduced)
spectral decomposition of a bipartite state — the eigenvectors `|i⟩` orthonormal, recorded here as
pairwise **orthogonal supports** of the pure eigenprojectors `|i⟩⟨i|` (`hψ`, equivalent to
orthonormality for unit vectors), with strictly positive eigenvalues `λᵢ > 0` (`hpos`). Then the
Araki–Lieb triangle inequality is saturated,

`S(A,B) = S(B) − S(A)`,

**if and only if**

* the left marginals `ρ^A_i = tr_B(|i⟩⟨i|)` are all **equal** (`∀ i j, ρ^A_i = ρ^A_j`), and
* the right marginals `ρ^B_i = tr_A(|i⟩⟨i|)` have **orthogonal support**
  (`State.OrthogonalSupports`).

This is the statement Exercise 11.16 evidently intends. It differs from the **printed** exercise
only in the first condition: N&C requires the `ρ^A_i` merely to share a common eigenbasis, but that
is too weak — equality forces the `ρ^A_i` to be *identical* (the strict-concavity condition, N&C
Exercise 11.18), strictly stronger than a common eigenbasis. The counterexample
`classicalCorrQubits` below satisfies the printed conditions yet not this equality (see
`classicalCorr_arakiLieb_condition_not_sufficient`). We take the *reduced* decomposition (`hpos`); a
zero eigenvalue contributes nothing to any of the three entropies, so its (arbitrary) eigenvector's
marginals are physically irrelevant — see the module docstring.

Proof. `S(A,B) = H(λ)` because the components are orthogonal pure states
(`State.vonNeumannEntropy_mix_orthogonalSupport`, each `S(|i⟩⟨i|) = 0`). The triangle gap decomposes
as a sum of two non-negative gaps,

`S(A) + H(λ) − S(B) = (S(A) − ∑ᵢ λᵢ S(ρ^A_i)) + (H(λ) + ∑ᵢ λᵢ S(ρ^B_i) − S(B))`,

using the purity identity `S(ρ^A_i) = S(ρ^B_i)`
(`PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`). The first bracket is the concavity gap
(`State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix'`, `≥ 0`; `= 0` iff the `ρ^A_i` coincide,
`State.vonNeumannEntropy_mix_eq_sum_iff'`); the second is the entropy-of-a-mixture gap
(`State.vonNeumannEntropy_mix_le'`, `≥ 0`; `= 0` iff the `ρ^B_i` have orthogonal support,
`State.vonNeumannEntropy_mix_eq_iff_orthogonal`). A sum of two non-negatives is zero iff both are,
which yields the biconditional. The two marginals of the mixture are themselves the mixtures of the
component marginals via `State.reducedLeft_mix` / `State.reducedRight_mix`. -/
theorem State.vonNeumannEntropy_mix_eq_reducedRight_sub_reducedLeft_iff
    {A B : QSystem} {n : ℕ} (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1)
    (hpos : ∀ i, 0 < lam i) (ψ : Fin n → PureState (A ⊗ B))
    (hψ : State.OrthogonalSupports fun i => (ψ i).toState) :
    (State.mix lam hlam hsum fun i => (ψ i).toState).vonNeumannEntropy
        = (State.mix lam hlam hsum fun i => (ψ i).toState).reducedRight.vonNeumannEntropy
          - (State.mix lam hlam hsum fun i => (ψ i).toState).reducedLeft.vonNeumannEntropy
      ↔ (∀ i j, (ψ i).toState.reducedLeft = (ψ j).toState.reducedLeft) ∧
          State.OrthogonalSupports fun i => (ψ i).toState.reducedRight := by
  classical
  -- The two marginals of the mixture are the mixtures of the component marginals.
  have hredL : (State.mix lam hlam hsum fun i => (ψ i).toState).reducedLeft
      = State.mix lam hlam hsum (fun i => (ψ i).toState.reducedLeft) :=
    State.reducedLeft_mix lam hlam hsum (fun i => (ψ i).toState)
  have hredR : (State.mix lam hlam hsum fun i => (ψ i).toState).reducedRight
      = State.mix lam hlam hsum (fun i => (ψ i).toState.reducedRight) :=
    State.reducedRight_mix lam hlam hsum (fun i => (ψ i).toState)
  -- S(A,B) = H(λ): orthogonal pure components.
  have hSmu : (State.mix lam hlam hsum fun i => (ψ i).toState).vonNeumannEntropy
      = Real.entropy lam := by
    rw [State.vonNeumannEntropy_mix_orthogonalSupport lam hlam hsum (fun i => (ψ i).toState) hψ]
    simp only [PureState.vonNeumannEntropy_toState_eq_zero, mul_zero, Finset.sum_const_zero,
      add_zero]
  -- Purity complementarity S(ρ^A_i) = S(ρ^B_i), hence equal weighted sums.
  have hSi : ∀ i, ((ψ i).toState.reducedLeft).vonNeumannEntropy
      = ((ψ i).toState.reducedRight).vonNeumannEntropy :=
    fun i => PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight (ψ i)
  have hEF : (∑ i, lam i * ((ψ i).toState.reducedLeft).vonNeumannEntropy)
      = ∑ i, lam i * ((ψ i).toState.reducedRight).vonNeumannEntropy :=
    Finset.sum_congr rfl fun i _ => by rw [hSi i]
  -- The two non-negative gaps.
  have hconc : (∑ i, lam i * ((ψ i).toState.reducedLeft).vonNeumannEntropy)
      ≤ (State.mix lam hlam hsum (fun i => (ψ i).toState.reducedLeft)).vonNeumannEntropy :=
    State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix' lam hlam hsum _
  have hub : (State.mix lam hlam hsum (fun i => (ψ i).toState.reducedRight)).vonNeumannEntropy
      ≤ (∑ i, lam i * ((ψ i).toState.reducedRight).vonNeumannEntropy) + Real.entropy lam :=
    State.vonNeumannEntropy_mix_le' lam hlam hsum _
  -- The two equality conditions.
  have hiffA : (State.mix lam hlam hsum (fun i => (ψ i).toState.reducedLeft)).vonNeumannEntropy
        = ∑ i, lam i * ((ψ i).toState.reducedLeft).vonNeumannEntropy
      ↔ ∀ i, 0 < lam i → (ψ i).toState.reducedLeft
          = State.mix lam hlam hsum (fun i => (ψ i).toState.reducedLeft) :=
    State.vonNeumannEntropy_mix_eq_sum_iff' lam hlam hsum _
  have hiffB : (State.mix lam hlam hsum (fun i => (ψ i).toState.reducedRight)).vonNeumannEntropy
        = Real.entropy lam + ∑ i, lam i * ((ψ i).toState.reducedRight).vonNeumannEntropy
      ↔ ∀ ⦃i j⦄, i ≠ j → lam i ≠ 0 → lam j ≠ 0 →
          ((ψ i).toState.reducedRight).op * ((ψ j).toState.reducedRight).op = 0 :=
    State.vonNeumannEntropy_mix_eq_iff_orthogonal lam hlam hsum _
  rw [hSmu, hredR, hredL]
  constructor
  · -- Equality ⟹ both conditions: both gaps vanish.
    intro heq
    have hAeq : (State.mix lam hlam hsum (fun i => (ψ i).toState.reducedLeft)).vonNeumannEntropy
        = ∑ i, lam i * ((ψ i).toState.reducedLeft).vonNeumannEntropy := by
      linarith [hconc, hub, hEF]
    have hBeq : (State.mix lam hlam hsum (fun i => (ψ i).toState.reducedRight)).vonNeumannEntropy
        = Real.entropy lam + ∑ i, lam i * ((ψ i).toState.reducedRight).vonNeumannEntropy := by
      linarith [hAeq, hEF]
    refine ⟨fun i j => ?_, ?_⟩
    · have h := hiffA.mp hAeq
      rw [h i (hpos i), h j (hpos j)]
    · intro i j hij
      rw [State.support_isOrtho_iff_op_mul_eq_zero]
      exact hiffB.mp hBeq hij (hpos i).ne' (hpos j).ne'
  · -- Both conditions ⟹ equality: both gaps vanish.
    rintro ⟨hcA, hcB⟩
    have hAeq : (State.mix lam hlam hsum (fun i => (ψ i).toState.reducedLeft)).vonNeumannEntropy
        = ∑ i, lam i * ((ψ i).toState.reducedLeft).vonNeumannEntropy := by
      rw [hiffA]
      exact fun i _ =>
        (State.mix_eq_of_forall_pos_eq lam hlam hsum _ _ (fun j _ => hcA j i)).symm
    have hBeq : (State.mix lam hlam hsum (fun i => (ψ i).toState.reducedRight)).vonNeumannEntropy
        = Real.entropy lam + ∑ i, lam i * ((ψ i).toState.reducedRight).vonNeumannEntropy := by
      rw [hiffB]
      intro i j hij _ _
      rw [← State.support_isOrtho_iff_op_mul_eq_zero]
      exact hcB hij
    linarith [hAeq, hBeq, hEF]

/-- The uniform two-outcome probability distribution `p₀ = p₁ = ½` on `Fin 2`, the mixing weights of
the counterexample state. -/
private def halfHalf : Fin 2 → ℝ := fun _ => 1 / 2

private theorem halfHalf_nonneg (i : Fin 2) : 0 ≤ halfHalf i := by unfold halfHalf; norm_num

private theorem halfHalf_sum : ∑ i, halfHalf i = 1 := by
  simp [halfHalf]

/-- The Shannon entropy of the uniform two-outcome distribution `H(½, ½) = log 2`. -/
private theorem entropy_halfHalf : Real.entropy halfHalf = Real.log 2 := by
  have h : halfHalf = fun _ : Fin 2 => (↑(Fintype.card (Fin 2)))⁻¹ := by
    funext i; rw [Fintype.card_fin]; norm_num [halfHalf]
  rw [h, Real.entropy_uniform]
  simp [Fintype.card_fin]

/-- **The `i`-th eigenvector `|ii⟩` of the counterexample state**: the computational-basis product
state `|i⟩ ⊗ |i⟩` of two qubits. The two vectors `|00⟩`, `|11⟩` are orthonormal, so
`classicalCorrQubits = ½|00⟩⟨00| + ½|11⟩⟨11|` is a spectral decomposition with these as
eigenvectors. -/
def classicalCorrKet (i : Fin 2) : PureState (qubit ⊗ qubit) := (qubitBasis i).tmul (qubitBasis i)

/-- **The maximally classically-correlated two-qubit state** `ρ^{AB} = ½|00⟩⟨00| + ½|11⟩⟨11|` — the
counterexample to the printed form of Nielsen & Chuang Exercise 11.16. It is the uniform mixture of
the two orthonormal pure states `|00⟩`, `|11⟩` (`classicalCorrKet`). -/
def classicalCorrQubits : State (qubit ⊗ qubit) :=
  State.mix halfHalf halfHalf_nonneg halfHalf_sum (fun i => (classicalCorrKet i).toState)

/-- **The left marginal is maximally mixed**: `ρ^A = tr_B(ρ^{AB}) = ½|0⟩⟨0| + ½|1⟩⟨1|`, the uniform
mixture of the computational-basis projectors. Partial trace is linear (`State.reducedLeft_mix`) and
`tr_B(|ii⟩⟨ii|) = |i⟩⟨i|` (`reducedLeft_toState_tmul`). -/
theorem classicalCorrQubits_reducedLeft :
    classicalCorrQubits.reducedLeft
      = State.mix halfHalf halfHalf_nonneg halfHalf_sum (fun i => (qubitBasis i).toState) := by
  rw [classicalCorrQubits, State.reducedLeft_mix]
  simp only [classicalCorrKet, reducedLeft_toState_tmul]

/-- **The right marginal is maximally mixed**: `ρ^B = tr_A(ρ^{AB}) = ½|0⟩⟨0| + ½|1⟩⟨1|`. The
`reducedRight` analogue of `classicalCorrQubits_reducedLeft`. -/
theorem classicalCorrQubits_reducedRight :
    classicalCorrQubits.reducedRight
      = State.mix halfHalf halfHalf_nonneg halfHalf_sum (fun i => (qubitBasis i).toState) := by
  rw [classicalCorrQubits, State.reducedRight_mix]
  simp only [classicalCorrKet, reducedRight_toState_tmul]

/-- **Joint entropy `S(A,B) = log 2`.** The state `½|00⟩⟨00| + ½|11⟩⟨11|` is an orthogonal-support
mixture of two pure states, so `S = H(½,½) + ∑ᵢ ½·S(|ii⟩⟨ii|) = log 2 + 0`. -/
theorem classicalCorrQubits_vonNeumannEntropy :
    classicalCorrQubits.vonNeumannEntropy = Real.log 2 := by
  -- Orthonormality `⟨ii|jj⟩ = δᵢⱼ` of the two eigenvectors (inline, in terms of the state
  -- vectors `.vec`).
  have hortho : Orthonormal ℂ (fun i => (classicalCorrKet i).vec) := by
    rw [orthonormal_iff_ite]
    intro i j
    have htmul : inner ℂ (classicalCorrKet i).vec (classicalCorrKet j).vec
        = inner ℂ (qubitBasis i).vec (qubitBasis j).vec
          * inner ℂ (qubitBasis i).vec (qubitBasis j).vec := rfl
    rw [htmul, qubitBasis_inner_qubitBasis]
    by_cases h : i = j <;> simp [h]
  rw [classicalCorrQubits, State.vonNeumannEntropy_mix_toState_orthonormal _ _ _ _ hortho]
  exact entropy_halfHalf

/-- **Marginal entropy `S(A) = log 2`.** The left marginal `½|0⟩⟨0| + ½|1⟩⟨1|` is the maximally
mixed qubit; via the orthogonal-support mixture identity, `S = H(½,½) + 0 = log 2`. -/
theorem classicalCorrQubits_reducedLeft_vonNeumannEntropy :
    classicalCorrQubits.reducedLeft.vonNeumannEntropy = Real.log 2 := by
  rw [classicalCorrQubits_reducedLeft,
    State.vonNeumannEntropy_mix_toState_orthonormal _ _ _ _ qubitBasis_vec_orthonormal]
  exact entropy_halfHalf

/-- **Marginal entropy `S(B) = log 2`.** The right marginal is likewise maximally mixed. -/
theorem classicalCorrQubits_reducedRight_vonNeumannEntropy :
    classicalCorrQubits.reducedRight.vonNeumannEntropy = Real.log 2 := by
  rw [classicalCorrQubits_reducedRight,
    State.vonNeumannEntropy_mix_toState_orthonormal _ _ _ _ qubitBasis_vec_orthonormal]
  exact entropy_halfHalf

/-- **N&C's first condition holds: the `ρ^A_i = tr_B(|ii⟩⟨ii|)` have a common eigenbasis.** The
marginals are `|0⟩⟨0|`, `|1⟩⟨1|`, both diagonal in the computational basis
`EuclideanSpace.basisFun (Fin 2) ℂ`: `|i⟩⟨i| |k⟩ = δᵢₖ |k⟩`. -/
theorem classicalCorr_reducedLeft_hasCommonEigenbasis :
    State.HasCommonEigenbasis (fun i => (classicalCorrKet i).toState.reducedLeft) := by
  refine ⟨2, fun k => (qubitBasis k).vec, qubitBasis_vec_orthonormal, ?_, fun i k => ?_⟩
  · have h : (fun k => (qubitBasis k).vec) = ⇑qubitModuleBasis :=
      (funext qubitModuleBasis_apply).symm
    rw [h]; exact qubitModuleBasis.span_eq
  · refine ⟨if i = k then 1 else 0, ?_⟩
    have hmarg : (classicalCorrKet i).toState.reducedLeft = (qubitBasis i).toState :=
      reducedLeft_toState_tmul (qubitBasis i) (qubitBasis i)
    simp only [hmarg, PureState.toState_op]
    rw [InnerProductSpace.rankOne_apply, qubitBasis_inner_qubitBasis]
    by_cases h : i = k
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right h]
      exact (zero_smul ℂ _).trans (zero_smul ℂ _).symm

/-- **N&C's second condition holds: the `ρ^B_i = tr_A(|ii⟩⟨ii|) = |i⟩⟨i|` have orthogonal
support.** -/
theorem classicalCorr_reducedRight_orthogonalSupports :
    State.OrthogonalSupports (fun i => (classicalCorrKet i).toState.reducedRight) := by
  intro i j hij
  have hi : (classicalCorrKet i).toState.reducedRight = (qubitBasis i).toState :=
    reducedRight_toState_tmul (qubitBasis i) (qubitBasis i)
  have hj : (classicalCorrKet j).toState.reducedRight = (qubitBasis j).toState :=
    reducedRight_toState_tmul (qubitBasis j) (qubitBasis j)
  simp only [hi, hj]
  exact State.pairwise_support_isOrtho_of_orthonormal (fun i => qubitBasis i)
    qubitBasis_vec_orthonormal hij

/-- **The triangle inequality is strict for the counterexample**: `S(A,B) = log 2 ≠ 0 = S(B) −
S(A)`, so `S(A,B) ≠ S(B) − S(A)`. -/
theorem classicalCorrQubits_vonNeumannEntropy_ne :
    classicalCorrQubits.vonNeumannEntropy
      ≠ classicalCorrQubits.reducedRight.vonNeumannEntropy
        - classicalCorrQubits.reducedLeft.vonNeumannEntropy := by
  rw [classicalCorrQubits_vonNeumannEntropy, classicalCorrQubits_reducedLeft_vonNeumannEntropy,
    classicalCorrQubits_reducedRight_vonNeumannEntropy, sub_self]
  exact (Real.log_pos (by norm_num)).ne'

/-- **Refutation of Nielsen & Chuang Exercise 11.16 as printed.** The two stated conditions — the
`ρ^A_i` have a common eigenbasis, and the `ρ^B_i` have orthogonal support — both hold for
`classicalCorrQubits = ½|00⟩⟨00| + ½|11⟩⟨11|`, yet `S(A,B) ≠ S(B) − S(A)`. Hence the "`⟸`"
direction of the printed biconditional fails: a common eigenbasis for the `ρ^A_i` is *not*
sufficient (identical `ρ^A_i` is the correct condition). See the module docstring for the correct
statement. -/
theorem classicalCorr_arakiLieb_condition_not_sufficient :
    State.HasCommonEigenbasis (fun i => (classicalCorrKet i).toState.reducedLeft) ∧
      State.OrthogonalSupports (fun i => (classicalCorrKet i).toState.reducedRight) ∧
      classicalCorrQubits.vonNeumannEntropy
        ≠ classicalCorrQubits.reducedRight.vonNeumannEntropy
          - classicalCorrQubits.reducedLeft.vonNeumannEntropy :=
  ⟨classicalCorr_reducedLeft_hasCommonEigenbasis,
    classicalCorr_reducedRight_orthogonalSupports, classicalCorrQubits_vonNeumannEntropy_ne⟩

end AxQM
