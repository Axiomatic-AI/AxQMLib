/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Observable

/-!
# AxQM.Postulates.API — eigenstates of an observable (general)

Definitions and lemmas for the **eigenstates** of an observable, gate-agnostic and
reusable across every Nielsen–Chuang item that needs them (Exercise 2.53's Hadamard
eigendecomposition, Exercise 2.58's average/standard deviation in an eigenstate, …).

* `Observable.HasEigenstate A μ ψ` — the pure-state eigenvalue equation `A ψ = μ ψ` of an
  observable, with the eigenvalue `μ : ℝ` explicit (an observable's eigenvalues are its real
  possible measurement values).
* `Observable.hasEigenstate_of_smul` — an eigenstate is unchanged by rescaling the underlying
  vector, so the eigenvalue equation may be checked on an unnormalized representative and
  transported to the normalized `PureState`.
* `PureState.expectation_of_hasEigenstate` — the expectation value of an observable in one of its
  eigenstates *is* the eigenvalue: `⟪A⟫_ψ = μ`. The physical meaning of an eigenvalue as the
  measurement outcome obtained with certainty.

These three declarations were first introduced for Exercise 2.53 in
`AxQM/Postulates/API/HadamardEigen.lean`; they are reused, for instance, by the statistics
definitions in `AxQM/Postulates/API/Variance.lean` for Exercise 2.58.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **`ψ` is an eigenstate of the observable `A` with eigenvalue `μ`.** The pure-state eigenvalue
equation `A ψ = μ ψ` of an observable, with the eigenvalue `μ : ℝ` explicit (an observable's
eigenvalues are real — its possible measurement values). -/
def Observable.HasEigenstate (A : Observable S) (μ : ℝ) (ψ : PureState S) : Prop :=
  A.op ψ.vec = (μ : ℂ) • ψ.vec

/-- An eigenstate is unchanged by rescaling the underlying vector: if `A v = μ v` and `ψ`'s vector
is a scalar multiple `c • v` of `v`, then `ψ` is an eigenstate of `A` with eigenvalue `μ`. This lets
the eigenvalue equation be verified on an unnormalized representative and transported to the
normalized `PureState`. -/
theorem Observable.hasEigenstate_of_smul {A : Observable S} {μ : ℝ} {ψ : PureState S}
    {c : ℂ} {v : S} (hψ : ψ.vec = c • v) (hv : A.op v = (μ : ℂ) • v) :
    A.HasEigenstate μ ψ := by
  rw [Observable.HasEigenstate, hψ, map_smul, hv, smul_comm]

/-- **The expectation value of an observable in one of its eigenstates equals the eigenvalue.** If
`ψ` is an eigenstate of `A` with eigenvalue `μ`, then `⟪A⟫_ψ = μ`: measuring `A` in `ψ` yields `μ`
with certainty. This is the physical meaning of an eigenvalue as a measurement outcome. -/
theorem PureState.expectation_of_hasEigenstate {A : Observable S} {μ : ℝ} {ψ : PureState S}
    (h : A.HasEigenstate μ ψ) : ψ.expectation A = μ := by
  have hop : A.op ψ.vec = (μ : ℂ) • ψ.vec := h
  rw [PureState.expectation, hop, inner_smul_right, inner_self_eq_norm_sq_to_K, ψ.normalized]
  simp

end AxQM
