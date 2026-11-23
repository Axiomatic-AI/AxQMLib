/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ControlledPowerSequence
import AxQM.Concrete.BitStringValue

/-!
# Nielsen & Chuang, Exercise 5.7 — the phase-estimation controlled-`U` sequence

*(N&C p. 222.)*

Show the controlled-U sequence takes |j>|u> to |j>U^j|u>, not depending on |u> being eigenstate.

Figure 5.2 is the first stage of phase estimation: a `t`-qubit control register, then, for each
control wire, a controlled power of `U` acting on the target register `S`. The top wire (the
most-significant bit `j₁`) controls `U^{2^{t-1}}`, and the bottom wire (`j_t`) controls `U^{2^0}=U`.
On a computational-basis control `|j⟩ = |j₁…j_t⟩` the wire `jₛ` therefore applies `U^{jₛ·2^{t-s}}`,
and, since powers of `U` commute, the whole sequence applies `U^{∑ₛ jₛ 2^{t-s}} = Uʲ`.

## What is formalised

The exercise is stated using the following pieces:

* `seqCtrlPow U t` (`AxQM/Core/ControlledPowerSequence.lean`) — the sequence of controlled-`U`
  operations of Figure 5.2 as an `Evolution` on the register `qtower t S` (`t` control qubits
  wrapping the target `S`), and `qtowerKet t b u` (same file) — the input state `|b₀…b_{t-1}⟩ ⊗
  |u⟩`.
* `Concrete.bitsToNat t b` (`AxQM/Concrete/BitStringValue.lean`) — the big-endian integer value
  `j = ∑ₛ bₛ 2^{t-1-s}` of the control register (`b 0` the most-significant bit).
* `seqCtrlPow_evolvePure` (**this file**) — **the exercise:** `seqCtrlPow U t` takes `|j⟩|u⟩` to
  `|j⟩ Uʲ|u⟩`, where `j = bitsToNat t b`. The target state `u` is fully general (never assumed an
  eigenstate of `U`), which is exactly the "does not depend on `|u⟩` being an eigenstate" clause of
  the exercise.

## Design notes

* **The first stage of phase estimation.** The register ket `qtowerKet`, the gate sequence
  `seqCtrlPow`, and the idle-wrap action lemma `unCtrl_evolvePure_qtowerKet` (the
  arbitrary-inner-system analogs of `towerKet`/`unCtrl`) are in
  `AxQM/Core/ControlledPowerSequence.lean`; the register
  value `bitsToNat` is in `AxQM/Concrete/BitStringValue.lean`. Exercises 5.8 and 5.9 build on
  these. The exercise itself is `seqCtrlPow_evolvePure`.
* **Faithful generality.** `U` is a unitary on an *arbitrary* target system `S` and `u` an
  *arbitrary* pure state, matching N&C. The exercise's parenthetical — that the identity holds with
  no eigenstate hypothesis — is captured by `u` being a free variable: no `HasEigenstate` assumption
  is ever made. When `u` *is* an eigenstate the action specialises to the phase
  `Uʲ|u⟩ = e^{2πiϕj}|u⟩` of the first-register state (5.20), but that is a corollary, not the
  content.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 5.7.** The sequence of controlled-`U` operations of Figure 5.2
takes `|j⟩|u⟩` to `|j⟩ Uʲ|u⟩`: on the control register in the computational-basis state `|j⟩ = |b⟩`
(with `j = bitsToNat t b` the integer it encodes) and an **arbitrary** target pure state `u`,
`seqCtrlPow U t` leaves the control register unchanged and applies `U` raised to `j` to the target.

The target `u` is a free variable — no eigenstate hypothesis — which is precisely the "does not
depend on `|u⟩` being an eigenstate of `U`" clause of the exercise.

Proof by induction on the number of controls `t`. The outermost wire `b 0` is peeled with
`Evolution.onRight` (inner sequence, inductive hypothesis) and `controlledUnitary` (outer gate);
when `b 0 = 1` the outer gate applies `U^{2^t}` to the target through
`unCtrl_evolvePure_qtowerKet`, and `U^{2^t}·U^{bitsToNat t (tail b)} = U^{bitsToNat (t+1) b}` by
`pow_add` and the leading-bit recursion of `bitsToNat`. -/
theorem seqCtrlPow_evolvePure (U : Evolution S) :
    ∀ (t : ℕ) (b : Fin t → Fin 2) (u : PureState S),
      (seqCtrlPow U t).evolvePure (qtowerKet t b u)
        = qtowerKet t b ((U ^ Concrete.bitsToNat t b).evolvePure u)
  | 0, b, u => by
    simp only [seqCtrlPow_zero, qtowerKet_zero, Concrete.bitsToNat_zero, pow_zero,
      Evolution.one_def]
    exact Evolution.id_evolvePure u
  | (t + 1), b, u => by
    simp only [qtower, seqCtrlPow_succ, qtowerKet_succ, Evolution.evolvePure_comp,
      Evolution.onRight_evolvePure, seqCtrlPow_evolvePure U t (Fin.tail b) u,
      Concrete.bitsToNat_succ]
    obtain h | h : b 0 = 0 ∨ b 0 = 1 := by omega
    · rw [h, controlledUnitary_evolvePure_ketZero]
      simp
    · rw [h, controlledUnitary_evolvePure_ketOne, unCtrl_evolvePure_qtowerKet,
        ← Evolution.evolvePure_comp, ← Evolution.mul_def, ← pow_add]
      simp

end AxQM
