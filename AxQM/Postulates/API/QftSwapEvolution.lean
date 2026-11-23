/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuditGate
import AxQM.Concrete.QftGateCircuit
import ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# The Figure 5.1 swap layer as an `Evolution`, and its computational-basis action (N&C Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) reads the Figure 5.1 QFT circuit on the
`(n+1)`-qubit control tower `qtower n qubit` as a **product of wire-addressed tower gates**
(`qftTowerEvolution_eq_map_congr_prod`), so each transported Figure 5.1 gate must be re-expressed as
such a tower gate. The Figure 5.1 gates come in three shapes — the wire-reversal **swap** layer, the
**Hadamards**, and the **controlled-`Rₖ`** rotations. This file supplies the ingredient the *swap*
re-expression needs: the swap layer as a named `Evolution` on the single `2ⁿ`-level register, with
its action on the computational basis computed.

## What is formalised

* `quditGate_permGate_evolvePure_quditBasis` — a **reusable bridge**: the `quditGate` promotion of a
  `permGate` (a classical reversible / basis-permutation matrix) realises that permutation on the
  computational basis, `quditGate (permGate enc σ) |enc x⟩ = |enc (σ x)⟩`. Proved from the column
  action of `Matrix.toEuclideanCLM` on a standard basis vector
  (`Matrix.toEuclideanCLM_apply_single`) and the entry form of `permGate` (`permGate_apply`): the
  `enc x`-column of `permGate enc σ` is the indicator of `enc (σ x)`.
* `qftSwapEvolution n` — the **Figure 5.1 swap (wire-reversal) layer as an `Evolution`**: the
  `quditGate` promotion of the Concrete swap matrix
  `permGate finFunctionFinEquiv (qftBitReversal n)` (the first gate of `Concrete.qftGateSequence`).
* `qftSwapEvolution_evolvePure_quditBasis` — its **computational-basis action**: it reverses the
  wire labels of a basis ket,
  `qftSwapEvolution n |finFunctionFinEquiv f⟩ = |finFunctionFinEquiv (f ∘ Fin.rev)⟩`
  (`qftBitReversal` is the wire reversal `f ↦ f ∘ Fin.rev`). The instance of the reusable bridge at
  `σ = qftBitReversal n`, `enc = finFunctionFinEquiv`. This is the register-side action the tower
  re-expression (`AxQM/Core/QftTowerSwap.lean`) reads through the bridge.

-/

open Matrix

namespace AxQM

noncomputable section

open AxQM.Concrete

/-- **A `quditGate`-promoted permutation matrix permutes the computational basis.** For an encoding
`enc : (Fin m → Fin 2) ≃ Fin d` of the bit-strings and a permutation `σ` of them, the gate
`quditGate (permGate enc σ)` sends the basis ket `|enc x⟩` to `|enc (σ x)⟩` — the
postulate-`Evolution` realisation of the classical reversible gate whose action on bit-strings is
`σ`. Proved from the column action of `Matrix.toEuclideanCLM` on a standard basis vector
(`Matrix.toEuclideanCLM_apply_single`, giving the `enc x`-column `∑ⱼ (permGate enc σ)ⱼ,ₑₙ𝒸ₓ |j⟩`)
and the entry form `permGate_apply` (that column is the indicator of `enc (σ x)`). Reused by every
Figure 5.1 basis-permutation gate — here the swap layer `qftSwapEvolution`. -/
theorem quditGate_permGate_evolvePure_quditBasis {m d : ℕ} [NeZero d]
    (enc : (Fin m → Fin 2) ≃ Fin d) (σ : Equiv.Perm (Fin m → Fin 2)) (x : Fin m → Fin 2) :
    (quditGate (permGate_mem_unitaryGroup enc σ)).evolvePure (quditBasis (enc x))
      = quditBasis (enc (σ x)) := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, quditGate_op, quditBasis_vec, quditBasis_vec]
  refine (Matrix.toEuclideanCLM_apply_single (permGate enc σ) (enc x)).trans ?_
  rw [Finset.sum_eq_single (enc (σ x))]
  · rw [permGate_apply, Equiv.symm_apply_apply, ite_eq_left rfl, one_smul]
  · intro j _ hj
    rw [permGate_apply, Equiv.symm_apply_apply, ite_eq_right hj, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The Figure 5.1 swap (wire-reversal) layer as an `Evolution`** on `qudit (2ⁿ)`: the `quditGate`
promotion of the Concrete swap matrix `permGate finFunctionFinEquiv (qftBitReversal n)` — the first
gate of `Concrete.qftGateSequence`, realising the wire-reversing permutation of the QFT circuit's
swap layer. It is unitary (a permutation gate), so `quditGate` applies. It is used in
`AxQM/Core/QftTowerSwap.lean`; its basis action is `qftSwapEvolution_evolvePure_quditBasis`. -/
def qftSwapEvolution (n : ℕ) : Evolution (qudit (2 ^ n)) :=
  quditGate (permGate_mem_unitaryGroup finFunctionFinEquiv (qftBitReversal n))

/-- **The swap layer reverses the wire labels of a computational-basis ket.**
`qftSwapEvolution n |finFunctionFinEquiv f⟩ = |finFunctionFinEquiv (f ∘ Fin.rev)⟩`: the bit-string
`f` addressing the wires is precomposed with the wire reversal `Fin.rev` (wire `i` receives what
wire `i.rev` carried), because `qftBitReversal n f = f ∘ Fin.rev`. The instance of
`quditGate_permGate_evolvePure_quditBasis` at `σ = qftBitReversal n`, `enc = finFunctionFinEquiv`
(the final step `qftBitReversal n f = fun i => f i.rev` holds definitionally). This is the
register-side action the tower re-expression reads through the register bridge `quditPowTower`. -/
theorem qftSwapEvolution_evolvePure_quditBasis (n : ℕ) (f : Fin n → Fin 2) :
    (qftSwapEvolution n).evolvePure (quditBasis (finFunctionFinEquiv f))
      = quditBasis (finFunctionFinEquiv (fun i => f i.rev)) := by
  rw [qftSwapEvolution, quditGate_permGate_evolvePure_quditBasis]; rfl

end

end AxQM
