/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.KitaevPhaseEstimation
import AxQM.Postulates.API.CascadedMeasurement
import AxQM.Postulates.API.CompositeMeasurement

/-!
# AxQM — phase estimation on a superposition input (N&C Exercise 5.8)

Nielsen & Chuang, §5.2.1, Exercise 5.8. The phase estimation algorithm run on a *single* eigenstate
`|u⟩` of `U` (eigenvalue `e^{2πiϕ_u}`) takes `|0⟩|u⟩` to `|φ̃_u⟩|u⟩`, and — for `t` control qubits
chosen per (5.35) — measuring the control register produces an estimate `φ̃_u` accurate to `n` bits
with probability `≥ 1 - ε`. By linearity, on the superposition input `|0⟩ ∑ᵤ c_u |u⟩` the algorithm
outputs the entangled state `∑ᵤ c_u |φ̃_u⟩|u⟩`. Exercise 5.8 asks to show that the probability of
measuring `φ̃_u` accurate to `n` bits is then at least `‖c_u‖² (1 - ε)`.

The physical content the exercise asks one to *show* is the extra factor `‖c_u‖²`: because the
eigenstates `|u⟩` are **orthonormal**, the branches of the entangled output decouple under a joint
readout, so the joint probability of (control estimate accurate for `u`) and (target register equal
to the eigenstate `u`) factorises as `‖c_u‖²` times the single-eigenstate success probability. The
single-eigenstate `≥ 1 - ε` bound (the analysis (5.23)–(5.35)) enters as the hypothesis "`t` is
chosen according to (5.35)", exactly as the exercise states it.

## What is formalised

For a control register `C`, a target register `S`, an orthonormal family `vb` in `S` (the eigenbasis
of `U`), amplitudes `c`, and per-branch control-output states `φ` (the first-register states
`|φ̃_u⟩`), with the entangled output `Ψ = ∑ⱼ cⱼ (φⱼ ⊗ vbⱼ)`:

* `Measurement.leftAndBasisRight m vb` — the **joint readout** of `C ⊗ S`: measure the control
  register with an arbitrary measurement `m` (in phase estimation, the computational-basis readout
  after the inverse QFT) and the target register in the orthonormal basis `vb`, recording the
  pair of outcomes. Built from `Measurement.onLeft` / `Measurement.onRight` /
  `Measurement.cascade` / `Measurement.ofOrthonormalBasis`.
* `Measurement.leftAndBasisRight_op_apply` — the key computation: the readout operator for outcome
  `(i, k)` sends `Ψ.vec` to `cₖ · (Mᵢ φₖ ⊗ vbₖ)`. The right register's projector `|vbₖ⟩⟨vbₖ|` kills
  every branch `j ≠ k` by orthonormality; `Mᵢ = m.op i` acts on the surviving left factor.
* `Measurement.bornProb_leftAndBasisRight` — **the "show":** the joint Born probability
  `p(i, k) = ‖cₖ‖² · p_m(i | φₖ)` factorises, the orthonormal tag `vbₖ` decoupling the branches.
* `phaseEstimationSuperposition_accuracy_ge` — **Exercise 5.8:** summing over a success set `G` of
  control outcomes for eigenstate `k`, the joint probability of measuring `φ̃ₖ` accurately is
  at least `‖cₖ‖² (1 - ε)`, given the single-eigenstate accuracy `1 - ε ≤ ∑_{i ∈ G} p_m(i | φₖ)`.

## Design notes

* **Statement.** The statement of Exercise 5.8 is in `AxQM/NC/Ch5/Exercise5_8.lean`.
* **Faithful generality.** `C`, `S`, `m`, `vb`, `c`, `φ` are all arbitrary: the readout `m` on the
  control register is any measurement (never assumed to be a specific QFT-based circuit), the target
  system and its eigenbasis are arbitrary, and the branch states `φⱼ` are arbitrary pure states — no
  eigenstate structure of `U` is used, only orthonormality of the tag family `vb`. The single-
  eigenstate accuracy bound is a hypothesis, matching the exercise's "if `t` is chosen according to
  (5.35)". The "accurate to `n` bits" event is modelled abstractly as an arbitrary success set
  `G : Finset μ` of control outcomes, so the statement is independent of the concrete
  `|m − b| ≤ 2^{t−n} − 1` tolerance.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {C S : QSystem} {μ ι : Type*} [Fintype μ] [Fintype ι]

/-- **Joint readout of a bipartite register.** Measure the left factor `C` with an arbitrary
measurement `m` and the right factor `S` in the orthonormal basis `vb`, recording the pair of
outcomes `(i, k) ∈ μ × ι`. Realised as the cascade of `m.onLeft S` (measure the control register)
and `(Measurement.ofOrthonormalBasis vb).onRight C` (measure the target in `vb`); the two operators
act on disjoint factors, so their order is immaterial. In phase estimation `C` is the `t`-qubit
control register read out after the inverse QFT, and `vb` is the eigenbasis of `U` on the target. -/
def Measurement.leftAndBasisRight (m : Measurement μ C) (vb : OrthonormalBasis ι ℂ S.space) :
    Measurement (μ × ι) (C ⊗ S) :=
  (m.onLeft S).cascade ((Measurement.ofOrthonormalBasis vb).onRight C)

/-- **The joint readout operator selects a single branch.** For the entangled output
`Ψ = ∑ⱼ cⱼ (φⱼ ⊗ vbⱼ)`, the readout operator for outcome `(i, k)` sends `Ψ.vec` to
`cₖ · (Mᵢ φₖ ⊗ vbₖ)`, where `Mᵢ = m.op i`. The right register's projector `|vbₖ⟩⟨vbₖ|` fixes the
`k`-th branch (`⟨vbₖ, vbₖ⟩ = 1`) and annihilates every branch `j ≠ k` (`⟨vbₖ, vbⱼ⟩ = 0`), while `Mᵢ`
acts on the surviving left factor. The key step of Exercise 5.8. -/
theorem Measurement.leftAndBasisRight_op_apply (m : Measurement μ C)
    (vb : OrthonormalBasis ι ℂ S.space) (c : ι → ℂ) (φ : ι → PureState C)
    (Ψ : PureState (C ⊗ S)) (hΨ : Ψ.vec = ∑ j, c j • ((φ j).vec ⊗ₜ[ℂ] vb j)) (i : μ) (k : ι) :
    (m.leftAndBasisRight vb).op (i, k) Ψ.vec = c k • ((m.op i) (φ k).vec ⊗ₜ[ℂ] vb k) := by
  classical
  -- First measure the control register: `m.op i ⊗ I` sends `Ψ.vec` to `∑ⱼ cⱼ (Mᵢ φⱼ ⊗ vbⱼ)`.
  have h1 : (m.onLeft S).op i Ψ.vec = ∑ j, c j • ((m.op i) (φ j).vec ⊗ₜ[ℂ] vb j) := by
    rw [Measurement.onLeft_op, hΨ]
    erw [TensorProduct.mapL_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
      one_apply_eq_self]
  -- Then measure the target in `vb`: `I ⊗ |vbₖ⟩⟨vbₖ|` keeps only branch `k`.
  rw [Measurement.leftAndBasisRight, Measurement.cascade_op, ContinuousLinearMap.comp_apply, h1,
    Measurement.onRight_op, Measurement.ofOrthonormalBasis_op]
  erw [TensorProduct.mapL_apply, map_sum]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
  · rw [map_smul, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
      one_apply_eq_self, InnerProductSpace.rankOne_apply,
      orthonormal_iff_ite.mp vb.orthonormal k k, ite_eq_left rfl, one_smul]
  · intro j _ hj
    rw [map_smul, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp vb.orthonormal k j,
      ite_eq_right (Ne.symm hj), zero_smul, TensorProduct.tmul_zero, smul_zero]

/-- **Orthonormal-tag decoupling of the Born rule (the content of Exercise 5.8).** For the entangled
output `Ψ = ∑ⱼ cⱼ (φⱼ ⊗ vbⱼ)` over an orthonormal family `vb` in the target register, the joint
probability of reading control outcome `i` and target outcome `k` factorises as
`p(i, k) = ‖cₖ‖² · p_m(i | φₖ)`. The target register's orthonormality decouples the branches, so
only branch `k` survives, weighted by `‖cₖ‖²`; `p_m(i | φₖ) = ‖Mᵢ φₖ‖²` is the single-eigenstate
probability. -/
theorem Measurement.bornProb_leftAndBasisRight (m : Measurement μ C)
    (vb : OrthonormalBasis ι ℂ S.space) (c : ι → ℂ) (φ : ι → PureState C)
    (Ψ : PureState (C ⊗ S)) (hΨ : Ψ.vec = ∑ j, c j • ((φ j).vec ⊗ₜ[ℂ] vb j)) (i : μ) (k : ι) :
    (m.leftAndBasisRight vb).bornProb Ψ.toState (i, k)
      = ‖c k‖ ^ 2 * m.bornProb (φ k).toState i := by
  rw [Measurement.bornProb_toState_eq_normSq, Measurement.leftAndBasisRight_op_apply m vb c φ Ψ hΨ,
    Measurement.bornProb_toState_eq_normSq]
  -- Ascribe the raw tensor type so the canonical `TensorProduct` norm instance is used, matching
  -- `norm_smul` / `TensorProduct.norm_tmul` (cf. `KitaevPhaseEstimation`).
  change ‖(c k • ((m.op i) (φ k).vec ⊗ₜ[ℂ] vb k) : C.space ⊗[ℂ] S.space)‖ ^ 2
      = ‖c k‖ ^ 2 * ‖(m.op i) (φ k).vec‖ ^ 2
  rw [norm_smul, TensorProduct.norm_tmul, vb.orthonormal.1 k, mul_one, mul_pow]

/-- **Nielsen & Chuang, Exercise 5.8.** Phase estimation on a superposition input. Given the
entangled output `Ψ = ∑ᵤ cᵤ (φ̃ᵤ ⊗ uᵤ)` of phase estimation over the orthonormal eigenbasis `vb` of
`U` (`uᵤ = vb u` the `u`-th eigenstate, `φ̃ᵤ = φ u` its first-register estimate state), a control-
register readout `m`, a chosen eigenstate `k`, and a success set `G` of control outcomes counting as
"accurate to `n` bits" for eigenstate `k` whose single-eigenstate probability satisfies
`1 - ε ≤ ∑_{i ∈ G} p_m(i | φ̃ₖ)` (guaranteed by choosing `t` per (5.35)), the joint probability of
measuring `φ̃ₖ` accurately — control outcome in `G` **and** the target register collapsing to the
`k`-th eigenstate — is at least `‖cₖ‖² (1 - ε)`.

This is the exercise's conclusion: the single-eigenstate guarantee propagates to the superposition
input weighted by `‖cₖ‖²`, the probability that the target register is found in the eigenstate `k`.
The factor `‖cₖ‖²` is supplied by `Measurement.bornProb_leftAndBasisRight` (orthonormal-tag
decoupling); the sum over `G` then carries the `1 - ε` bound through, `‖cₖ‖² ≥ 0`. -/
theorem phaseEstimationSuperposition_accuracy_ge (m : Measurement μ C)
    (vb : OrthonormalBasis ι ℂ S.space) (c : ι → ℂ) (φ : ι → PureState C)
    (Ψ : PureState (C ⊗ S)) (hΨ : Ψ.vec = ∑ j, c j • ((φ j).vec ⊗ₜ[ℂ] vb j))
    (k : ι) (G : Finset μ) (ε : ℝ) (hacc : 1 - ε ≤ ∑ i ∈ G, m.bornProb (φ k).toState i) :
    ‖c k‖ ^ 2 * (1 - ε) ≤ ∑ i ∈ G, (m.leftAndBasisRight vb).bornProb Ψ.toState (i, k) := by
  have hsum : ∑ i ∈ G, (m.leftAndBasisRight vb).bornProb Ψ.toState (i, k)
      = ‖c k‖ ^ 2 * ∑ i ∈ G, m.bornProb (φ k).toState i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Measurement.bornProb_leftAndBasisRight m vb c φ Ψ hΨ i k
  rw [hsum]
  exact mul_le_mul_of_nonneg_left hacc (sq_nonneg _)

end AxQM
