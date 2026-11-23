/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QftTowerCircuit
import AxQM.Core.QtowerTensorPow
import AxQM.Core.EvolutionQubitBasisExt

/-!
# Computational-basis extensionality for tower evolutions (N&C Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) reads the Figure 5.1 QFT circuit on the
`(n+1)`-qubit control tower `qtower n qubit` and must re-express each of its transported gates —
`Evolution.congr (quditPowTower n) (quditGate M)` — as a **wire-addressed tower `Evolution`** (a
Hadamard on a wire `Evolution.qtowerSingleWire`, a controlled-`Rₖ` on a wire pair). Every such
re-expression is an **`Evolution` identity**, and the way each is proved is by checking the two
gates agree on every computational tower basis state `towerKet n b` — the form in which the reader
`quditPowTower_congr_evolvePure_towerKet` and the placement gates'
actions (`qtowerSingleWire_evolvePure_towerKet`, `qtowerPermWires_evolvePure_towerKet`) are all
stated. This file proves the bridge from *"agree on every `towerKet n b`"* to *"equal as
`Evolution`s"* on the tower, and gives the combinator that turns a transported-gate
re-expression into exactly that basis-ket check.

## What is formalised

* `Evolution.ext_towerKet` — **two evolutions of `qtower n qubit` agreeing on every computational
  tower basis state are equal.** The `qtower` analogue of `Evolution.ext_qubitBasis` (which lives on
  the *symmetric* register `qubit ^⊗ₛ (n+1)`): it lets a computational-basis truth table on the
  right-nested control tower be upgraded to an honest `Evolution` identity. Proved by
  transporting both gates across the `qtower ↔ tensor-power` bridge `qtowerQubitTensorPow n` and
  invoking `Evolution.ext_qubitBasis` there, then pulling the equality back through the transport
  roundtrip `Evolution.congr_symm_congr`.
* `quditPowTower_congr_eq_of_evolvePure_towerKet` — **the transported-gate re-expression
  combinator.** To prove a transported register gate `Evolution.congr (quditPowTower n) U` equals a
  wire-addressed tower gate `V`, it suffices to check, for every bit-string `b`, that `V` sends
  `towerKet n b` to the transport of `U`'s action on the register ket
  `|finFunctionFinEquiv (b ∘ Fin.rev)⟩` — i.e. exactly the right-hand side the tower reader
  `quditPowTower_congr_evolvePure_towerKet` computes for the transported gate. This packages
  `Evolution.ext_towerKet` with the reader into the single tool each Figure 5.1 gate's
  wire-addressed re-expression is discharged by.

It is assembled from the bridge `AxQM/Core/QtowerTensorPow.lean`, the tower reader in
`AxQM/Core/QftTowerCircuit.lean`, and the sibling qubit-register extensionality in
`AxQM/Core/EvolutionQubitBasisExt.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Computational-basis extensionality for evolutions of the control tower.** Two evolutions
`A B : Evolution (qtower n qubit)` are equal once they agree on every computational tower basis
state `towerKet n b` (`b : Fin (n+1) → Fin 2`). This is the `qtower` analogue of
`Evolution.ext_qubitBasis` (the same fact on the symmetric register `qubit ^⊗ₛ (n+1)`): it upgrades
a computational-basis truth table on the grounded, right-nested control tower to an honest
`Evolution` identity — the step every wire-addressed re-expression of a Figure 5.1 gate (Problem
5.2) closes with.

Proved by transporting `A` and `B` across the `qtower ↔ tensor-power` bridge
`qtowerQubitTensorPow n` via `Evolution.congr`: the bridge carries `towerKet n b` to the product
`⨂ᵢ |b i⟩` (`qtowerQubitTensorPow_congr_towerKet`) and intertwines the actions
(`Evolution.congr_evolvePure_congr`), so the transported gates agree on every `⨂ᵢ |b i⟩` and hence
are equal by `Evolution.ext_qubitBasis`; the transport roundtrip `Evolution.congr_symm_congr` pulls
that equality back to `A = B`. -/
theorem Evolution.ext_towerKet {n : ℕ} {A B : Evolution (qtower n qubit)}
    (h : ∀ b : Fin (n + 1) → Fin 2,
      A.evolvePure (towerKet n b) = B.evolvePure (towerKet n b)) :
    A = B := by
  -- `Evolution.congr (qtowerQubitTensorPow n)` is injective (the transport roundtrip
  -- `Evolution.congr_symm_congr` is a `LeftInverse`), so it suffices that the two transports onto
  -- `qubit ^⊗ₛ (n+1)` agree — and they do on the product basis `⨂ᵢ |b i⟩` (the bridge image of
  -- `towerKet n b`), hence everywhere by `ext_qubitBasis`.
  refine Function.LeftInverse.injective (Evolution.congr_symm_congr (qtowerQubitTensorPow n)) ?_
  apply Evolution.ext_qubitBasis
  intro b
  rw [← qtowerQubitTensorPow_congr_towerKet n b, Evolution.congr_evolvePure_congr,
    Evolution.congr_evolvePure_congr, h b]

/-- **Re-expressing a transported register gate as a wire-addressed tower gate.** To prove that the
register gate `U : Evolution (qudit (2ⁿ⁺¹))` transported onto the tower,
`Evolution.congr (quditPowTower n) U`, equals a wire-addressed tower gate `V : Evolution
(qtower n qubit)`, it suffices to check on every computational tower basis state `towerKet n b`:

  `V.evolvePure (towerKet n b)
     = quditPowTower n • (U.evolvePure |finFunctionFinEquiv (b ∘ Fin.rev)⟩)`.

The right-hand side is exactly what the tower reader `quditPowTower_congr_evolvePure_towerKet`
computes for the *transported* gate `Evolution.congr (quditPowTower n) U` on
`towerKet n b` (the `Fin.rev` reconciling the big-endian register bridge with the little-endian
`finFunctionFinEquiv` wire-indexing of the Figure 5.1 matrix gates). So this combinator —
`Evolution.ext_towerKet` composed with the reader — is the single tool each Figure 5.1 gate's
wire-addressed re-expression (the Hadamard as `Evolution.qtowerSingleWire`, the
controlled-`Rₖ` on a wire pair) is discharged by: compute `V`'s basis action, compute `U`'s
register-ket action, and match. -/
theorem quditPowTower_congr_eq_of_evolvePure_towerKet {n : ℕ}
    (U : Evolution (qudit (2 ^ (n + 1)))) (V : Evolution (qtower n qubit))
    (h : ∀ b : Fin (n + 1) → Fin 2,
      V.evolvePure (towerKet n b)
        = PureState.congr (quditPowTower n)
            (U.evolvePure (quditBasis (finFunctionFinEquiv (fun i => b i.rev))))) :
    Evolution.congr (quditPowTower n) U = V := by
  apply Evolution.ext_towerKet
  intro b
  rw [quditPowTower_congr_evolvePure_towerKet, h b]

end AxQM
