/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.InverseQuantumFourierTransform

/-!
# Nielsen & Chuang, Exercise 5.5 — a quantum circuit for the inverse quantum Fourier transform

*(N&C p. 221.)*

Give a quantum circuit to perform the inverse quantum Fourier transform.

## The answer

The quantum Fourier transform `F` (N&C eq. 5.2) is a *unitary* transformation, so its inverse
`F⁻¹ = F†` is unitary too and is therefore itself an implementable quantum circuit: the **adjoint
of the QFT circuit**. Gate for gate this is the QFT circuit (Figure 5.1) run **in reverse order
with every gate replaced by its adjoint** — the general reversal principle `(g_L ∘ ⋯ ∘ g_1)† = g_1†
∘ ⋯ ∘ g_L†` (`Evolution.adjoint_comp`). This is exactly how N&C use it: "the inverse quantum
Fourier transform … is obtained by reversing the circuit for the quantum Fourier transform" (§5.2,
phase estimation).

In this library the QFT is realized as the monolithic unitary `Evolution` `qftEvolution d`
(Problem 5.1); its inverse circuit is `qftInverseEvolution d = (qftEvolution d).adjoint`
(`AxQM/Postulates/API/InverseQuantumFourierTransform.lean`). The *gate-level* decomposition
(reverse the Hadamards, controlled-`R_k`, and swaps of Fig 5.1, each daggered) is an efficiency /
gate-count annotation on this unitary — the same cost-model claim that is not expressed here,
exactly as for the forward circuit in Problem 5.1. What
is a theorem is the unitary the inverse circuit realizes and its defining properties, formalised in
full below.

## What is formalised

The inverse transform is defined in `AxQM/Postulates/API/InverseQuantumFourierTransform.lean`:
`qftInverseEvolution d` (the circuit), `qftInverseEvolution_op_apply_quditBasis`
(`F⁻¹|k⟩ = ∑ⱼ (1/√d)·e^{−2πijk/d}|j⟩`), the image state `qftInverseFourierImage`, and
`qftInverseEvolution_adjoint` (its inverse is the QFT). The statements of the exercise are:

* `qftInverseEvolution_evolvePure_quditBasis` — the **inverse discrete Fourier transform**:
  `F⁻¹|k⟩ = ∑ⱼ (1/√d)·e^{−2πijk/d} |j⟩`, the conjugate of the forward action (5.2), confirming the
  circuit performs the *inverse* transform.
* `qftInverseEvolution_comp_qftEvolution` / `qftEvolution_comp_qftInverseEvolution` — the two-sided
  inversion `F⁻¹ ∘ F = id` and `F ∘ F⁻¹ = id`: the inverse circuit undoes the QFT circuit (and vice
  versa) as a *gate identity*.
* `qftInverseEvolution_evolvePure_qftEvolution_evolvePure` /
  `qftEvolution_evolvePure_qftInverseEvolution_evolvePure` — the operational round-trips
  `F⁻¹(F|ψ⟩) = |ψ⟩` and `F(F⁻¹|ψ⟩) = |ψ⟩` on an arbitrary pure state: running the QFT then the
  inverse QFT (in either order) returns any input state unchanged.

-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 5.5 — the inverse discrete Fourier transform.** The inverse QFT
circuit sends the computational-basis state `|k⟩` of the register `qudit d` to the inverse-Fourier
superposition `∑ⱼ (1/√d)·e^{−2πijk/d} |j⟩`:
`evolvePure F⁻¹ |k⟩ = qftInverseFourierImage d k`.

The amplitudes are the conjugates of the forward QFT amplitudes (5.2), the defining sign flip of the
inverse transform. The amplitude computation is in
`AxQM/Postulates/API/InverseQuantumFourierTransform.lean`. -/
theorem qftInverseEvolution_evolvePure_quditBasis (d : ℕ) [NeZero d] (k : Fin d) :
    (qftInverseEvolution d).evolvePure (quditBasis k) = qftInverseFourierImage d k := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, qftInverseFourierImage_vec,
    qftInverseEvolution_op_apply_quditBasis]

/-- **Nielsen & Chuang, Exercise 5.5 — the inverse circuit undoes the QFT circuit** (gate identity):
`F⁻¹ ∘ F = id`. Applying the QFT circuit and then the inverse-QFT circuit is the identity gate.
Since `F⁻¹ = F†` and `F` is unitary, this is the isometry identity `F† F = 1`
(`Evolution.adjoint_comp_self`). -/
theorem qftInverseEvolution_comp_qftEvolution (d : ℕ) [NeZero d] :
    (qftInverseEvolution d).comp (qftEvolution d) = Evolution.id := by
  apply Evolution.ext
  rw [Evolution.comp_op, Evolution.id_op]
  exact (qftEvolution d).adjoint_comp_self

/-- **Nielsen & Chuang, Exercise 5.5 — the QFT circuit undoes the inverse circuit** (gate identity):
`F ∘ F⁻¹ = id`, the companion of `qftInverseEvolution_comp_qftEvolution` with the two circuits in
the opposite order. Since `F⁻¹ = F†` and `F` is unitary, this is the co-isometry identity
`F F† = 1` (`Evolution.comp_adjoint_self'`). Together they show `F⁻¹` is a two-sided inverse. -/
theorem qftEvolution_comp_qftInverseEvolution (d : ℕ) [NeZero d] :
    (qftEvolution d).comp (qftInverseEvolution d) = Evolution.id :=
  (qftEvolution d).comp_adjoint_self'

/-- **Nielsen & Chuang, Exercise 5.5 — operational round-trip** `F⁻¹(F|ψ⟩) = |ψ⟩`: running the QFT
circuit and then the inverse-QFT circuit returns any pure state `|ψ⟩` unchanged. The pure-state form
of `qftInverseEvolution_comp_qftEvolution`; since `F⁻¹ = F†`, it is the QFT's
`Evolution.evolvePure_adjoint_evolvePure`. -/
theorem qftInverseEvolution_evolvePure_qftEvolution_evolvePure (d : ℕ) [NeZero d]
    (ψ : PureState (qudit d)) :
    (qftInverseEvolution d).evolvePure ((qftEvolution d).evolvePure ψ) = ψ :=
  (qftEvolution d).evolvePure_adjoint_evolvePure ψ

/-- **Nielsen & Chuang, Exercise 5.5 — operational round-trip** `F(F⁻¹|ψ⟩) = |ψ⟩`: running the
inverse-QFT circuit and then the QFT circuit returns any pure state `|ψ⟩` unchanged. The companion
of `qftInverseEvolution_evolvePure_qftEvolution_evolvePure` with the circuits in the opposite order;
since `F⁻¹ = F†`, it is the QFT's `Evolution.evolvePure_adjoint_evolvePure'`. -/
theorem qftEvolution_evolvePure_qftInverseEvolution_evolvePure (d : ℕ) [NeZero d]
    (ψ : PureState (qudit d)) :
    (qftEvolution d).evolvePure ((qftInverseEvolution d).evolvePure ψ) = ψ :=
  (qftEvolution d).evolvePure_adjoint_evolvePure' ψ

end AxQM
