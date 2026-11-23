/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EntropyMixtureReverse
import AxQM.Postulates.API.BlochStateEntropy
import AxQM.Postulates.API.Mixture
import AxQM.Postulates.API.EntropyComposite
import AxQM.Postulates.API.BellReducedState

/-!
# AxQM.Postulates.API — the entropy of an equiprobable mixture of two pure states

The von Neumann entropy of the **equiprobable mixture of two pure states** `|ψ₁⟩`, `|ψ₂⟩`,

`S(½ |ψ₁⟩⟨ψ₁| + ½ |ψ₂⟩⟨ψ₂|) = H((1 + c)/2, (1 − c)/2)`,   where `c = |⟨ψ₁, ψ₂⟩|`,

expressed as the Shannon entropy of the two eigenvalues `(1 ± c)/2`. This is the spectral crux of
the Holevo-χ proof of the no-cloning theorem (Nielsen & Chuang, Problem 12.2): a cloning device
would map the ensemble `{½, |ψᵢ⟩}` of overlap `c` to `{½, |ψᵢ⟩|ψᵢ⟩}` of overlap `c²`, and since
`c² < c` for `0 < c < 1` and `H((1 + ·)/2, (1 − ·)/2)` is strictly decreasing, the average
component entropy is unchanged (pure states) while the mixture entropy strictly increases — so `χ`
strictly increases, contradicting its monotonicity under quantum operations.

## Main result

* `AxQM.State.vonNeumannEntropy_mixPair_pure` —
  `S(mixPair ½ |ψ₁⟩ |ψ₂⟩) = H((1 ± ‖⟨ψ₁, ψ₂⟩‖)/2)`.

## Proof

The two nonzero eigenvalues of the mixture `ρ` are the eigenvalues of the `2 × 2` Gram matrix
`½ !![1, ⟨ψ₂, ψ₁⟩; ⟨ψ₁, ψ₂⟩, 1]`, which are `(1 ± c)/2`. We reach them through the reference
marginal of the ensemble purification: for the equiprobable two-element ensemble `e = {½, |ψ₁⟩;
½, |ψ₂⟩}`, `S(ρ) = S(σ)` where `σ = Tr_A |AR⟩⟨AR|` is the reference-side qubit marginal
(`Ensemble.vonNeumannEntropy_toState_eq_reducedRight`, purity of the purification), and
`Ensemble.purify_reducedRight_op` exhibits `σ` as exactly that Gram operator. The Gram operator is
Hermitian and trace one, hence a **qubit Bloch state** `σ = blochState r` with Bloch vector
`r⃗ = (Re⟨ψ₁, ψ₂⟩, Im⟨ψ₁, ψ₂⟩, 0)` of norm `‖r⃗‖ = c` (the coefficient matrix matches
`Concrete.blochMatrix r` entrywise). Its entropy is then read off `blochState_vonNeumannEntropy`
(for `c > 0`); when `c = 0` the states are orthonormal and `σ` is the maximally mixed qubit of
entropy `log 2 = H(½, ½)`.

The strict increase of `χ` under cloning and the resulting no-cloning theorem are stated in
`AxQM/NC/Ch12/Problem12_2.lean`.
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

open Matrix ContinuousLinearMap

variable {S : QSystem}

/-- `rankOne` of two standard basis vectors is `Matrix.toEuclideanCLM` of the corresponding matrix
unit `|i⟩⟨j|`: `|eᵢ⟩⟨eⱼ| = toEuclideanCLM (single i j 1)`. The per-term bridge turning the Gram
rank-one sum of `Ensemble.purify_reducedRight_op` into a concrete `2 × 2` matrix. -/
private theorem rankOne_basisFun_eq_toEuclideanCLM (i j : Fin 2) :
    (InnerProductSpace.rankOne ℂ ((EuclideanSpace.basisFun (Fin 2) ℂ) i))
        ((EuclideanSpace.basisFun (Fin 2) ℂ) j)
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Matrix.single i j 1) := by
  have hv : Matrix.vecMulVec ((EuclideanSpace.basisFun (Fin 2) ℂ i)).ofLp
        (star ((EuclideanSpace.basisFun (Fin 2) ℂ j)).ofLp) = Matrix.single i j 1 := by
    simp [EuclideanSpace.basisFun_apply, Matrix.single_eq_single_vecMulVec_single]
  rw [← Matrix.toEuclideanCLM_vecMulVec, hv]

/-- The equiprobable two-element ensemble `{½, |ψ₁⟩; ½, |ψ₂⟩}`, the generating data whose
purification reduces the two-pure-mixture entropy to a qubit Gram/Bloch computation. -/
private def mixPairEnsemble (ψ₁ ψ₂ : PureState S) : Ensemble S where
  card := 2
  prob := ![1 / 2, 1 / 2]
  states := ![ψ₁, ψ₂]
  prob_nonneg := by intro i; fin_cases i <;> norm_num
  sum_prob := by norm_num [Fin.sum_univ_two]

/-- **The von Neumann entropy of an equiprobable mixture of two pure states** (Nielsen & Chuang,
Problem 12.2, spectral crux): for pure states `|ψ₁⟩`, `|ψ₂⟩` of overlap `c = ‖⟨ψ₁, ψ₂⟩‖`,

`S(½ |ψ₁⟩⟨ψ₁| + ½ |ψ₂⟩⟨ψ₂|) = H((1 + c)/2, (1 − c)/2)`,

the Shannon entropy of the mixture's two eigenvalues `(1 ± c)/2`. Holds for any dimension and any
overlap `c ∈ [0, 1]` (the orthogonal case `c = 0` gives the maximally mixed qubit entropy `log 2`).

Proved by reducing to the reference marginal of the ensemble purification — the `2 × 2` Gram
operator — which is a qubit Bloch state with Bloch vector `(Re⟨ψ₁, ψ₂⟩, Im⟨ψ₁, ψ₂⟩, 0)` of norm
`c`, so `blochState_vonNeumannEntropy` supplies the eigenvalues. -/
theorem State.vonNeumannEntropy_mixPair_pure (ψ₁ ψ₂ : PureState S) :
    (State.mixPair (p := 1 / 2) (by norm_num) (by norm_num)
        ψ₁.toState ψ₂.toState).vonNeumannEntropy
      = Real.entropy ![(1 + ‖inner ℂ ψ₁.vec ψ₂.vec‖) / 2,
                       (1 - ‖inner ℂ ψ₁.vec ψ₂.vec‖) / 2] := by
  set z : ℂ := inner ℂ ψ₁.vec ψ₂.vec with hz
  set r : Fin 3 → ℝ := ![z.re, z.im, 0] with hrdef
  -- Ball membership of the Bloch vector: ‖r‖² = ‖z‖² ≤ 1.
  have hznorm : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hzle : ‖z‖ ≤ 1 := by
    calc ‖z‖ ≤ ‖ψ₁.vec‖ * ‖ψ₂.vec‖ := norm_inner_le_norm (𝕜 := ℂ) ψ₁.vec ψ₂.vec
      _ = 1 := by rw [ψ₁.normalized, ψ₂.normalized, mul_one]
  have hSq : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = ‖z‖ ^ 2 := by simp [hrdef, hznorm]
  have hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1 := by rw [hSq]; nlinarith [norm_nonneg z, hzle]
  -- The reference marginal of the ensemble purification, a qubit state.
  set σ := (mixPairEnsemble ψ₁ ψ₂).purify.toState.reducedRight with hσ
  -- Step A: LHS entropy equals σ entropy (purity of the purification).
  have hmix : State.mixPair (p := 1 / 2) (by norm_num) (by norm_num)
      ψ₁.toState ψ₂.toState = (mixPairEnsemble ψ₁ ψ₂).toState := by
    have hop : (mixPairEnsemble ψ₁ ψ₂).toState.op
        = ∑ i : Fin 2, ((mixPairEnsemble ψ₁ ψ₂).prob i : ℂ)
            • ((mixPairEnsemble ψ₁ ψ₂).states i).toState.op := Ensemble.toState_op _
    apply State.ext
    rw [State.mixPair_op, hop, Fin.sum_univ_two]
    simp only [mixPairEnsemble, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hA : (State.mixPair (p := 1 / 2) (by norm_num) (by norm_num)
      ψ₁.toState ψ₂.toState).vonNeumannEntropy = σ.vonNeumannEntropy := by
    rw [hmix, hσ]
    exact Ensemble.vonNeumannEntropy_toState_eq_reducedRight (mixPairEnsemble ψ₁ ψ₂)
  -- Step B: the reference marginal is the Bloch state with vector `r = (Re z, Im z, 0)`.
  have hbridge : σ.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.blochMatrix r) := by
    have hop : σ.op = ∑ i : Fin 2, ∑ j : Fin 2,
        (↑(Real.sqrt ((mixPairEnsemble ψ₁ ψ₂).prob i))
            * ↑(Real.sqrt ((mixPairEnsemble ψ₁ ψ₂).prob j))
            * inner ℂ ((mixPairEnsemble ψ₁ ψ₂).states j).vec
                ((mixPairEnsemble ψ₁ ψ₂).states i).vec)
          • (InnerProductSpace.rankOne ℂ ((EuclideanSpace.basisFun (Fin 2) ℂ) i))
              ((EuclideanSpace.basisFun (Fin 2) ℂ) j) := by
      rw [hσ]; exact Ensemble.purify_reducedRight_op _
    have hself₁ : inner ℂ ψ₁.vec ψ₁.vec = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, ψ₁.normalized]; norm_num
    have hself₂ : inner ℂ ψ₂.vec ψ₂.vec = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, ψ₂.normalized]; norm_num
    have hconj : inner ℂ ψ₂.vec ψ₁.vec = (starRingEnd ℂ) z := by
      rw [hz, inner_conj_symm]
    have hhalfC : (↑(Real.sqrt (1 / 2)) : ℂ) * ↑(Real.sqrt (1 / 2)) = 1 / 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]; norm_num
    rw [hop, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [mixPairEnsemble, Matrix.cons_val_zero, Matrix.cons_val_one,
      rankOne_basisFun_eq_toEuclideanCLM, hself₁, hself₂, hconj, hhalfC, mul_one]
    rw [← map_smul, ← map_smul, ← map_smul, ← map_smul, ← map_add, ← map_add, ← map_add]
    congr 1
    -- The coefficient matrix (the Gram matrix) is the Bloch matrix of `r`.
    rw [Concrete.blochMatrix_eq]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, hrdef, smul_eq_mul, Fin.isValue,
        Fin.zero_eta, Fin.mk_one, and_self, and_true, ite_true, mul_one] <;>
      (apply Complex.ext <;>
        simp [Complex.mul_re, Complex.mul_im, Complex.sub_re,
          Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.conj_re, Complex.conj_im] <;> ring)
  have hBstate : σ = blochState r hr := by
    apply State.ext
    rw [hbridge, blochState_op]
  rw [hA, hBstate]
  -- Step C: read off the entropy of the Bloch state (`‖r‖ = ‖z‖ = c` via `hSq`).
  rcases (norm_nonneg z).eq_or_lt with hz0 | hzpos
  · -- Orthogonal case `c = 0`: the marginal is the maximally mixed qubit.
    have hz00 : z = 0 := norm_eq_zero.mp hz0.symm
    have hr0 : r = (0 : Fin 3 → ℝ) := by
      funext i; fin_cases i <;> simp [hrdef, hz00]
    have hstate : blochState r hr = maximallyMixedState qubit := by
      apply State.ext
      rw [blochState_op, hr0, Concrete.blochMatrix_zero, map_smul, map_one]
      exact maximallyMixedState_qubit_op.symm
    have hval : (blochState r hr).vonNeumannEntropy = Real.log 2 := by
      rw [hstate]
      exact (State.vonNeumannEntropy_maximallyMixed qubit).trans
        (by rw [finrank_qubit_space]; norm_num)
    refine hval.trans ?_
    rw [← hz0]
    simp only [Real.entropy, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      add_zero, sub_zero, Real.negMulLog_eq_neg]
    have hlog : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [hlog]; ring
  · -- Non-orthogonal case `0 < c`: read off the two Bloch eigenvalues `(1 ± c)/2`.
    have hpos : (0 : ℝ) < r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 := by rw [hSq]; exact pow_pos hzpos 2
    refine (blochState_vonNeumannEntropy r hr hpos).trans ?_
    rw [hSq, Real.sqrt_sq (norm_nonneg z)]

end AxQM
