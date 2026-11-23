/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SchmidtDecomposition
import AxQM.Postulates.API.EntropySpectral
import AxQM.Postulates.PartialTrace
import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract

/-!
# AxQM — equal marginal entropies of a pure bipartite state (`S(A) = S(B)`)

For a pure state `ψ` of a composite system `A ⊗ B`, the two reduced states have equal von Neumann
entropy: `S(A) = S(B)`. This is Nielsen & Chuang **Theorem 11.8, part (3)** (eq. (11.88)).

Both reduced density operators are read off a single Schmidt decomposition
`|ψ⟩ = ∑ᵢ λᵢ |aᵢ⟩ ⊗ |bᵢ⟩` in already-diagonal form — `ρᴬ = ∑ᵢ λᵢ² |aᵢ⟩⟨aᵢ|` and
`ρᴮ = ∑ᵢ λᵢ² |bᵢ⟩⟨bᵢ|` — sharing the one weight list `λ²`, so the orthonormal-eigenfamily engine
evaluates both entropies to `H(λ²)`.

## The proof

The proof needs the Schmidt decomposition (`PureState.exists_schmidt_decomposition`), the
partial-trace-of-a-Schmidt-sum identities, and the orthonormal-rank-one entropy engine
(`State.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum`). The statement of Theorem 11.8 is
in `AxQM/NC/Ch11/Theorem11_8.lean`. The equality `S(A) = S(B)` is also used in Exercise 11.14 (the
negative-conditional-entropy characterisation of entanglement) and Theorem 11.10 (the entropy of a
mixture, reverse direction).

## Main result

* `AxQM.PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight` — `S(A) = S(B)` for a pure
  bipartite state.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The reduced states of a pure composite are isentropic** (Nielsen–Chuang Theorem 11.8, part
(3)): if a composite system `AB` is in a pure state `ψ`, then `S(A) = S(B)`, where `A = tr_B|ψ⟩⟨ψ|`
and `B = tr_A|ψ⟩⟨ψ|` are the two reduced states.

N&C's proof: the Schmidt decomposition shows the two reduced density operators have the *same*
eigenvalues, and the entropy is a function of the eigenvalues alone. Formally, take any Schmidt
decomposition `|ψ⟩ = ∑ᵢ λᵢ |aᵢ⟩ ⊗ |bᵢ⟩` (`PureState.exists_schmidt_decomposition`) with strictly
positive coefficients `λᵢ` and orthonormal families `a`, `b`. Tracing out one factor of the
rank-one projector `|ψ⟩⟨ψ|`
(`LinearMap.partialTrace{Right,Left}_rankOne_eq_sum_rankOne_of_schmidt`) gives the
reduced operators in already-diagonal form, `ρᴬ = ∑ᵢ λᵢ² |aᵢ⟩⟨aᵢ|` and `ρᴮ = ∑ᵢ λᵢ² |bᵢ⟩⟨bᵢ|`, with
the *shared* weight list `λ²`. The orthonormal-eigenfamily engine
`State.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum` then evaluates both entropies to the
Shannon entropy `H(λ²)` of that one list, so they are equal. -/
theorem PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight {T : QSystem}
    (ψ : PureState (S.compose T)) :
    ψ.toState.reducedLeft.vonNeumannEntropy = ψ.toState.reducedRight.vonNeumannEntropy := by
  obtain ⟨n, l, a, b, _hpos, ha, hb, _hnorm, hvec⟩ := ψ.exists_schmidt_decomposition
  -- `ρᴬ = ∑ᵢ λᵢ² |aᵢ⟩⟨aᵢ|`: trace out the right factor of `|ψ⟩⟨ψ|`.
  have hAop : ψ.toState.reducedLeft.op
      = ∑ i, (((l i) ^ 2 : ℝ) : ℂ) • (InnerProductSpace.rankOne ℂ (a i)) (a i) := by
    apply ContinuousLinearMap.coe_injective
    rw [State.reducedLeft_op, LinearMap.coe_toContinuousLinearMap, PureState.toState_op]
    refine (LinearMap.partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt
      (stdOrthonormalBasis ℂ T.space) l a b hb hvec).trans ?_
    rw [ContinuousLinearMap.toLinearMap_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.toLinearMap_smul]
    norm_cast
  -- `ρᴮ = ∑ᵢ λᵢ² |bᵢ⟩⟨bᵢ|`: trace out the left factor of `|ψ⟩⟨ψ|`.
  have hBop : ψ.toState.reducedRight.op
      = ∑ i, (((l i) ^ 2 : ℝ) : ℂ) • (InnerProductSpace.rankOne ℂ (b i)) (b i) := by
    apply ContinuousLinearMap.coe_injective
    rw [State.reducedRight_op, LinearMap.coe_toContinuousLinearMap, PureState.toState_op]
    refine (LinearMap.partialTraceLeft_rankOne_eq_sum_rankOne_of_schmidt
      (stdOrthonormalBasis ℂ S.space) l a b
      (fun i j _ _ => orthonormal_iff_ite.mp ha i j) hvec).trans ?_
    rw [ContinuousLinearMap.toLinearMap_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.toLinearMap_smul]
    norm_cast
  rw [ψ.toState.reducedLeft.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum ha
      (fun i => (l i) ^ 2) hAop,
    ψ.toState.reducedRight.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum hb
      (fun i => (l i) ^ 2) hBop]

end AxQM
