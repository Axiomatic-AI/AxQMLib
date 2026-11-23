/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Entropy
import AxQM.Postulates.API.MaximallyMixed
import AxQM.Postulates.Composite

/-!
# AxQM — von Neumann entropy of product and maximally mixed states

Two basic values of the von Neumann entropy generator `State.vonNeumannEntropy`
(`AxQM/Postulates/API/Entropy.lean`), needed throughout Nielsen & Chuang Chapter 11:

* **Additivity over a product state** `S(ρ ⊗ σ) = S(ρ) + S(σ)` (N&C Exercise 11.13):
  the entropy of an uncorrelated composite is the sum of the parts. Lifts the operator-level
  theorem `ContinuousLinearMap.IsDensityOp.vonNeumannEntropy_tensorMap` to the `State`
  abstraction through `State.tmul`.
* **The maximally mixed value** `S(I/d) = log d` (N&C Theorem 11.8): the maximally mixed
  state `maximallyMixedState S` attains the `log d` upper bound
  (`State.vonNeumannEntropy_le_log_finrank`), since all `d` eigenvalues of `I/d` equal `1/d`
  and `H(1/d, …, 1/d) = log d`.

They are the two entropy values used in the counterexamples and computations of
the chapter (e.g. Problem 11.3).

## Main results

* `AxQM.State.vonNeumannEntropy_tmul` — `S(ρ ⊗ σ) = S(ρ) + S(σ)`.
* `AxQM.State.vonNeumannEntropy_maximallyMixed` — `S(I/d) = log d`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **Additivity of the von Neumann entropy over a product state** (Nielsen & Chuang,
Exercise 11.13): for states `ρ : State S` and `σ : State T`, the entropy of the uncorrelated
composite `ρ ⊗ σ` is the sum of the entropies,

`S(ρ ⊗ σ) = S(ρ) + S(σ)`.

Proved by unfolding the entropy to its density operator `State.tmul_op`
(`(ρ ⊗ σ).op = ρ.op ⊗ σ.op`) and applying the operator-level theorem
`ContinuousLinearMap.IsDensityOp.vonNeumannEntropy_tensorMap`, using the density-operator
witnesses `ρ.isDensity` / `σ.isDensity`. -/
theorem State.vonNeumannEntropy_tmul (ρ : State S) (σ : State T) :
    (ρ.tmul σ).vonNeumannEntropy = ρ.vonNeumannEntropy + σ.vonNeumannEntropy := by
  rw [State.vonNeumannEntropy_def, State.vonNeumannEntropy_def, State.vonNeumannEntropy_def,
    State.tmul_op]
  have hkey : (TensorProduct.mapL ρ.op σ.op).vonNeumannEntropy
      = ρ.op.vonNeumannEntropy + σ.op.vonNeumannEntropy := by
    rw [← ContinuousLinearMap.vonNeumannEntropy_toLinearMap (T := TensorProduct.mapL ρ.op σ.op),
      TensorProduct.toLinearMap_mapL]
    exact ρ.isDensity.vonNeumannEntropy_tensorMap σ.isDensity
  exact hkey

/-- **Von Neumann entropy of the maximally mixed state** (Nielsen & Chuang, Theorem 11.8): the
maximally mixed state `I/d = maximallyMixedState S` has entropy

`S(I/d) = log d`, where `d = dim S.space`,

attaining the upper bound `State.vonNeumannEntropy_le_log_finrank`. A thin lift of the
operator-level lemma `ContinuousLinearMap.vonNeumannEntropy_finrank_inv_smul_one` (the pure spectral
computation that every eigenvalue of `(1/d) • I` equals `1/d`, so the entropy is the Shannon
entropy of the uniform spectrum `log d`) through `maximallyMixedState_op`. -/
theorem State.vonNeumannEntropy_maximallyMixed (S : QSystem) [Nontrivial S.space] :
    (maximallyMixedState S).vonNeumannEntropy = Real.log (Module.finrank ℂ S.space) := by
  rw [State.vonNeumannEntropy_def, maximallyMixedState_op,
    ContinuousLinearMap.vonNeumannEntropy_finrank_inv_smul_one]

end AxQM
