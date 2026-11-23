/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PhaseEstimationSuperposition

/-!
# Nielsen & Chuang, Exercise 5.8 — phase estimation on a superposition input

*(N&C p. 225.)*

Show phase estimation on superposition input measures phi_u accurate to n bits with prob >=
|c_u|^2(1-eps).

The single-eigenstate phase estimation analysis (§5.2.1) shows that measuring the control register
after the inverse QFT yields `φ̃_u` accurate to `n` bits with probability `≥ 1 − ε`, provided `t` is
chosen per (5.35). By linearity the algorithm sends the superposition input `|0⟩ ∑ᵤ c_u|u⟩` to the
entangled output `∑ᵤ c_u|φ̃_u⟩|u⟩`. The physical content Exercise 5.8 asks one to *show* is the
factor `‖c_u‖²`: because the eigenstates `|u⟩` are **orthonormal**, the branches of the entangled
output decouple, so the joint probability of (control estimate accurate for `u`) and (target
register found in the eigenstate `u`) factorises as `‖c_u‖²` times the single-eigenstate probability
`≥ 1 − ε`, giving `≥ ‖c_u‖²(1 − ε)`.

Every statement of the exercise concerns the eigenbasis of the target register
(`OrthonormalBasis ι ℂ S.space`) and the amplitude decomposition of the output vector
(`Ψ.vec = ∑ⱼ cⱼ (φⱼ.vec ⊗ₜ vbⱼ)`); compare the closely analogous `Ensemble` reference-measurement
family for Exercise 2.82 (`AxQM/NC/Ch2/Exercise2_82.lean`).

## What is formalised

The formalisation is in `AxQM/Postulates/API/PhaseEstimationSuperposition.lean`, for a control
register `C`, a target register `S`, an orthonormal family `vb` in `S` (the eigenbasis of `U`),
amplitudes `c`, per-branch first-register estimate states `φ` (the states `|φ̃_u⟩`), and the
entangled output `Ψ = ∑ⱼ cⱼ (φⱼ ⊗ vbⱼ)`:

* `AxQM.Measurement.leftAndBasisRight` — the **joint readout** of `C ⊗ S`: measure the
  control register with an arbitrary measurement `m` (in phase estimation, the computational-basis
  readout after the inverse QFT) and the target register in the orthonormal basis `vb`, recording
  the pair of outcomes. Built from `Measurement.onLeft` / `Measurement.onRight` /
  `Measurement.cascade` / `Measurement.ofOrthonormalBasis`.
* `AxQM.Measurement.leftAndBasisRight_op_apply` — the key computation: the readout operator
  for outcome `(i, k)` sends `Ψ.vec` to `cₖ · (Mᵢ φₖ ⊗ vbₖ)`, the right register's projector
  `|vbₖ⟩⟨vbₖ|` annihilating every branch `j ≠ k` by orthonormality.
* `AxQM.Measurement.bornProb_leftAndBasisRight` — **the "show":** the joint Born
  probability factorises as `p(i, k) = ‖cₖ‖² · p_m(i | φₖ)`, the orthonormal tag `vbₖ` decoupling
  the branches.
* `AxQM.phaseEstimationSuperposition_accuracy_ge` — **the exercise's conclusion:** for a
  chosen eigenstate `k` and a success set `G` of control outcomes counting as "accurate to `n` bits"
  for `k`, with single-eigenstate accuracy `1 − ε ≤ ∑_{i ∈ G} p_m(i | φₖ)` (the "`t` chosen per
  (5.35)" hypothesis), the joint probability of measuring `φ̃ₖ` accurately is `≥ ‖cₖ‖²(1 − ε)`.

## Design notes

* **Faithful generality.** The control readout `m` is an arbitrary measurement (never a fixed
  QFT-based circuit), the target system and its eigenbasis are arbitrary, and the branch states `φⱼ`
  are arbitrary pure states — only orthonormality of the tag family `vb` is used, matching the
  exercise, which supplies the entangled output `∑ᵤ c_u|φ̃_u⟩|u⟩` and asks only for the `‖c_u‖²`
  factor. The single-eigenstate `≥ 1 − ε` bound (the analysis (5.23)–(5.35)) enters as the
  hypothesis, exactly as the exercise phrases it ("if `t` is chosen according to (5.35)"). The
  "accurate to `n` bits" event is modelled as an arbitrary success set `G : Finset μ` of control
  outcomes, so the statement is independent of the concrete `|m − b| ≤ 2^{t−n} − 1` tolerance.
* **Relation to Exercise 5.7.** This is the superposition-input companion of Exercise 5.7
  (`AxQM/NC/Ch5/Exercise5_7.lean`), which shows that the controlled-`U` sequence acts as `|j⟩|u⟩ ↦
  |j⟩Uʲ|u⟩` for an arbitrary target state — the same "no eigenstate assumption" spirit is what makes
  the output linear in the eigenbasis expansion of the input here.
-/
