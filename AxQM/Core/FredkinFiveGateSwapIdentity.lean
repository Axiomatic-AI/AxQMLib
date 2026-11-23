/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.FredkinFiveGateCircuit
import AxQM.Postulates.API.ControlledUnitaryDecomposition
import AxQM.Postulates.API.CnotXBasis
import AxQM.Postulates.API.PhaseGateEigenbasis

/-!
# The two-qubit `SWAP`-conjugation identity for the swap-diagonalizing gate (N&C Ex 4.25.4)

The control-branch reduction `twoQubitCircuit_pair_ctrl_eq_fredkinGate`
(`Core.FredkinFiveGateCircuit`) reduces "the five-two-qubit-gate circuit
`[pair B†, ctrl 0 W₃, ctrl 1 W₂, pair B, ctrl 0 W₁]` equals the Fredkin gate" to a single
**two-qubit `SWAP` identity**,
`B† · (W₃ on the first) · (W₂ on the second) · B · (W₁ on the first) = SWAP`.
This file proves that identity for the concrete gates of the Smolin–DiVincenzo
construction: `B = swapDiagonalizingGate`, `W₁ = X`, `W₂ = Z`, `W₃ = S`.

## The identity

`swapDiagonalizingGate_swapConjugation` proves
`B† · S_a · Z_b · B · X_a = SWAP`,
where `S_a = S ⊗ 1`, `Z_b = 1 ⊗ Z`, `X_a = X ⊗ 1` and `B = (I ⊗ H) · revC(S) · (H ⊗ I) · CNOT` is
the swap-diagonalizing gate. This identity is the input to the five-two-qubit-gate Fredkin
construction (N&C Exercise 4.25 part 4), assembled in `AxQM/NC/Ch4/Exercise4_25.lean`.

## Proof: peel off the adjoint, then a basis computation

Multiplying by `B` moves the identity to the equivalent form that never mentions `B†`,
`hkey :  S_a · Z_b · B · X_a  =  B · SWAP`,
because `B† · (B · SWAP) = (B† · B) · SWAP = SWAP` (`Evolution.adjoint_comp_self'`). The point of
`hkey` is that `B` maps each computational basis state `|x⟩ ⊗ |y⟩` to a **product** state
`Sⁱ(H|x⟩) ⊗ H|y⊕x⟩` (the control of every internal gate is a basis state, so no entanglement is
created), so both sides evaluate — factor by factor — to concrete `|±⟩`/`|±i⟩` products. `hkey` is
therefore discharged by two-qubit computational-basis extensionality (`twoQubit_evolution_ext`):
`fin_cases` on the two input bits, then a single `simp only` unfolding `B` through the constituent
`evolvePure` action laws (`cnotGate_evolvePure_qubitBasis`, `Evolution.onLeft_evolvePure`,
`reversedControlledUnitary_evolvePure_ketZero`/`ketOne`, `Evolution.onRight_evolvePure`,
`Evolution.swap_evolvePure_tmul`) and the single-qubit truth tables for `H`, `S`, `Z` on `|±⟩`,
`|±i⟩` (`Postulates.API.PhaseGateEigenbasis`, `hadamardGate_evolvePure_qubitBasis_*`).

The `X`/`Y`-eigenstate superposition bookkeeping that the constituent single-qubit truth tables
require is in `AxQM/Postulates/API/PhaseGateEigenbasis.lean`.
-/

namespace AxQM

/-- **The two-qubit `SWAP`-conjugation identity for the swap-diagonalizing gate** (N&C Exercise 4.25
part 4). For `B = swapDiagonalizingGate`,
`B† · (S ⊗ 1) · (1 ⊗ Z) · B · (X ⊗ 1) = SWAP`,
i.e. `swapDiagonalizingGate.adjoint.comp ((sGate.onLeft qubit).comp ((pauliZGate.onRight qubit).comp
(swapDiagonalizingGate.comp (pauliXGate.onLeft qubit)))) = Evolution.swap`. This is the concrete
two-qubit hypothesis consumed by `twoQubitCircuit_pair_ctrl_eq_fredkinGate` to obtain the
five-two-qubit-gate Fredkin construction.

Proof: the equivalent `B†`-free form `hkey : S_a · Z_b · B · X_a = B · SWAP` holds pointwise on the
four computational basis states (`B` sends each to a product of `|±⟩`/`|±i⟩` factors), proved by
`twoQubit_evolution_ext`; conjugating back through `B† B = 1` gives the stated identity. -/
theorem swapDiagonalizingGate_swapConjugation :
    swapDiagonalizingGate.adjoint.comp
        ((sGate.onLeft qubit).comp ((pauliZGate.onRight qubit).comp
          (swapDiagonalizingGate.comp (pauliXGate.onLeft qubit))))
      = Evolution.swap := by
  have hkey : (sGate.onLeft qubit).comp ((pauliZGate.onRight qubit).comp
      (swapDiagonalizingGate.comp (pauliXGate.onLeft qubit)))
      = swapDiagonalizingGate.comp Evolution.swap := by
    refine twoQubit_evolution_ext (fun i j => ?_)
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.mk_zero, Fin.mk_one, swapDiagonalizingGate, Evolution.evolvePure_comp,
        pauliXGate_evolvePure_qubitBasis, Evolution.onLeft_evolvePure,
        cnotGate_evolvePure_qubitBasis,
        Evolution.onRight_evolvePure, Evolution.swap_evolvePure_tmul,
        reversedControlledUnitary_evolvePure_ketZero, reversedControlledUnitary_evolvePure_ketOne,
        hadamardGate_evolvePure_qubitBasis_zero, hadamardGate_evolvePure_qubitBasis_one,
        sGate_evolvePure_qubitPlus, sGate_evolvePure_qubitMinus, sGate_evolvePure_qubitPlusI,
        sGate_evolvePure_qubitMinusI, pauliZGate_evolvePure_qubitPlus,
        pauliZGate_evolvePure_qubitMinus, Fin.reduceAdd, Fin.isValue]
  rw [hkey, ← Evolution.comp_assoc, Evolution.adjoint_comp_self', Evolution.id_comp]

end AxQM
