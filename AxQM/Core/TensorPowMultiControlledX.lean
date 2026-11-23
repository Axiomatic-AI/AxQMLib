/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QtowerTensorPow
import AxQM.Postulates.API.LeftPairGate

/-!
# `Cⁿ(X)` on the symmetric tensor-power register (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of Toffoli,
`CNOT` and single-qubit gates implementing the `n`-controlled `NOT` `Cⁿ(X)`. The postulate-grounded
`Cⁿ(X) = mcCtrl n pauliXGate` lives on the **right-nested** control tower `qtower n qubit`
(`Core/MultiControlledReduction`). The arbitrary-wire gate-placement combinator
`Evolution.onWires` (`AxQM/Postulates/API/WireGatePlacement.lean`) — the surgery that bottoms a
multiply-controlled-`NOT` block to genuine two-control gates on chosen, non-contiguous wires — lives
instead on the **symmetric** power `qubit ^⊗ₛ (n+1)` (the `n+1`-fold `PiTensorProduct`, where a wire
relabelling is a clean `reindexₗᵢ`). Assembling an `onWires`-built circuit and comparing it to
`Cⁿ(X)` therefore needs the grounded gate carried onto that same symmetric register.

This file performs that transport, once, and reads off its computational-basis truth table.

## What is formalised

* `Evolution.tensorPowMcCtrlX n` — the **symmetric-register form of `Cⁿ(X)`**: the grounded gate
  `mcCtrl n pauliXGate` transported onto `qubit ^⊗ₛ (n+1)` through the `qtower ↔ tensor-power`
  bridge `qtowerQubitTensorPow n` by `Evolution.congr`. A genuine closed-system
  `Evolution` on
  exactly the `(n+1)`-wire register — no work qubit — equal to `Cⁿ(X)` up to the (isometric) change
  of register description.
* `tensorPowMcCtrlX_evolvePure_piTensor` — its **computational-basis truth table**: on the symmetric
  product basis state `⨂ᵢ |b i⟩` it produces `⨂ᵢ |mcNot (cnxControls n) (Fin.last n) b i⟩`, i.e. it
  acts exactly as the classical multiply-controlled `NOT` `Concrete.mcNot` with controls the first
  `n` wires and target the last. This is the truth table the `onWires`-assembled circuit is compared
  against, in the register the circuit is built on.

## Design notes

* **Why transport `Cⁿ(X)` to the symmetric register, not the placement gates to `qtower`.** The
  two objects live on different registers: the target `Cⁿ(X)` on the right-nested
  `qtower n qubit`, and the placement combinators (`Evolution.permWires`,
  `Evolution.onBlock`, `Evolution.onWires`) on the symmetric
  `qubit ^⊗ₛ (a+b)`. Only one of the two needs to move. Carrying a *placement* gate
  `Evolution.onWires _ b σ : Evolution (qubit ^⊗ₛ (a+b))` onto `qtower` would require the bridge at
  `qtower (a+b-1) qubit`, and `(a+b-1)+1 = a+b` holds only *propositionally* (not by `rfl`) — a
  `cast`. Carrying the *single target* `Cⁿ(X) : Evolution (qtower n qubit)` onto
  `qubit ^⊗ₛ (n+1)` is `Evolution.congr (qtowerQubitTensorPow n) ·` — no subtraction, no `cast` —
  and it is transported once rather than once per placement gate. The two framings are
  interchangeable
  (`Evolution.congr` is an isomorphism), so a `Cⁿ(X) = circuit` claim on the symmetric
  register pulls back to the grounded `qtower` gate by the same iso.
* **The truth-table proof.** By the transport law `Evolution.congr_evolvePure_congr`, evolving a
  transported state by the transported gate equals the transport of the original action. The input
  `⨂ᵢ |b i⟩` is rewritten as `PureState.congr (bridge n) (towerKet n b)` via the forward basis
  dictionary `qtowerQubitTensorPow_congr_towerKet`; the grounded action
  `mcCtrl_pauliXGate_evolvePure_towerKet` (the Exercise 4.29 quantum–classical bridge) sends
  `towerKet n b ↦ towerKet n (mcNot …)`; and the same dictionary (forwards) folds the result back to
  `⨂ᵢ |mcNot … b i⟩`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **The multiply-controlled `NOT` `Cⁿ(X)` on the symmetric tensor-power register.** The grounded
gate `mcCtrl n pauliXGate : Evolution (qtower n qubit)` transported onto the symmetric `(n+1)`-fold
power `qubit ^⊗ₛ (n+1)` through the `qtower ↔ tensor-power` bridge `qtowerQubitTensorPow n`
by `Evolution.congr`. It acts on exactly the `(n+1)`-wire register — no work qubit — and
equals
`Cⁿ(X)` up to the isometric change of register description; its computational-basis action is
`tensorPowMcCtrlX_evolvePure_piTensor`. This is the object an `Evolution.onWires`-assembled Toffoli
circuit (which lives natively on `qubit ^⊗ₛ (n+1)`) is compared against. -/
def Evolution.tensorPowMcCtrlX (n : ℕ) : Evolution (qubit ^⊗ₛ (n + 1)) :=
  Evolution.congr (qtowerQubitTensorPow n) (mcCtrl n pauliXGate)

/-- Definitional unfolding of `Evolution.tensorPowMcCtrlX` as the transported grounded `Cⁿ(X)`. -/
theorem Evolution.tensorPowMcCtrlX_def (n : ℕ) :
    Evolution.tensorPowMcCtrlX n
      = Evolution.congr (qtowerQubitTensorPow n) (mcCtrl n pauliXGate) :=
  rfl

/-- **Computational-basis truth table of `Cⁿ(X)` on the symmetric register.** The symmetric-register
`Cⁿ(X)` gate `Evolution.tensorPowMcCtrlX n` acts on the computational product basis state `⨂ᵢ |b i⟩`
(`PureState.piTensor fun i => qubitBasis (b i)`) exactly as the classical multiply-controlled `NOT`
`Concrete.mcNot` with controls the first `n` wires (`cnxControls n`) and target the last
(`Fin.last n`):
`tensorPowMcCtrlX n (⨂ᵢ |b i⟩) = ⨂ᵢ |mcNot (cnxControls n) (Fin.last n) b i⟩`.

So on the symmetric register too, the quantum `Cⁿ(X)` **is** the reversible bit-string permutation
whose `O(n²)` no-work-qubit circuit the `Concrete/MultiControlledNot*` development exhibits — now
stated on the register where an arbitrary-wire (`Evolution.onWires`) Toffoli circuit is assembled.
Proved from the transport law `Evolution.congr_evolvePure_congr`, the forward basis dictionary
`qtowerQubitTensorPow_congr_towerKet` (used both to feed the input and to fold the output), and the
grounded quantum–classical bridge `mcCtrl_pauliXGate_evolvePure_towerKet` (Exercise 4.29). -/
theorem tensorPowMcCtrlX_evolvePure_piTensor (n : ℕ) (b : Fin (n + 1) → Fin 2) :
    (Evolution.tensorPowMcCtrlX n).evolvePure (PureState.piTensor fun i => qubitBasis (b i))
      = PureState.piTensor fun i =>
          qubitBasis (Concrete.mcNot (cnxControls n) (Fin.last n) b i) := by
  rw [Evolution.tensorPowMcCtrlX_def, ← qtowerQubitTensorPow_congr_towerKet n b,
    Evolution.congr_evolvePure_congr, mcCtrl_pauliXGate_evolvePure_towerKet,
    qtowerQubitTensorPow_congr_towerKet]

end AxQM
