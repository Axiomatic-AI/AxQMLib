/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuditDimCongr
import AxQM.Postulates.API.QftGateEvolution
import AxQM.Postulates.API.SystemIsoComm
import AxQM.Postulates.API.LeftPairGate
import AxQM.Core.MultiControlledReduction

/-!
# The measured-QFT register bridge `qudit (2ⁿ⁺¹) ≃ₛ qtower n qubit` (N&C Problem 5.2)

The quantum Fourier transform enters the postulate layer on the *single* register `qudit (2ⁿ)`
(as `qftEvolution (2ⁿ)`, and as the Figure 5.1 gate composition
`qftCircuitEvolution n`). The whole-circuit measured-QFT reduction (Problem 5.2) instead needs the
QFT on an explicit **`n`-qubit tensor register**, so that a terminal per-wire computational-basis
measurement can be deferred wire by wire (the deferred-measurement cascade lives on
`controlMeasurement (qubit ⊗ S)`, i.e. the *right-nested* control tower `qtower n qubit`). This file
supplies that structural bridge and transports the QFT across it.

## What is formalised

* `quditPowTower n` — the **register bridge** `qudit (2ⁿ⁺¹) ≃ₛ qtower n qubit`, identifying the
  `2ⁿ⁺¹`-level register with the right-nested `(n+1)`-qubit control tower. Built by induction on `n`
  by iterating the tensor-factorisation iso `quditProdIso 2 (2ⁿ⁺¹) : qudit (2·2ⁿ⁺¹) ≃ₛ qubit ⊗
  qudit (2ⁿ⁺¹)` — the **big-endian** split peeling the leading qubit `j₁` off the front
  of N&C's `|j₁…jₙ⟩` register (§5.1) — after a `quditDimCongr` dimension cast reconciling
  `2ⁿ⁺² = 2·2ⁿ⁺¹` (`pow_succ'`). The base `qudit (2¹) = qubit = qtower 0 qubit` is the identity.
* `quditPowTower_zero` / `quditPowTower_succ` — the recursion unfoldings (definitional), exposing
  the peel structure that the inductive proofs use.
* `quditPowTower_congr_quditBasis_succ` — the **basis peel**: on a computational-basis ket the
  bridge splits off the leading qubit, `Φ |x·2ⁿ⁺¹ + y⟩ = |x⟩ ⊗ Φ' |y⟩` (`Φ = quditPowTower (n+1)`,
  `Φ' = quditPowTower n`, `x : Fin 2` the leading bit). The recursive correctness of the bridge as
  the computational-basis identification, from `quditProdIso_congr_quditBasis`.
* `qftTowerEvolution n` — the **QFT transported onto the tower**, `Evolution.congr (quditPowTower n)
  (qftEvolution (2ⁿ⁺¹))`: the quantum Fourier transform as an `Evolution` on `qtower n qubit`.
* `qftTowerEvolution_eq_congr_qftCircuitEvolution` — it is equally the transport of the Figure 5.1
  gate circuit `qftCircuitEvolution (n+1)` (via `qftEvolution_eq_qftCircuitEvolution`), the
  form the wire-addressed reduction rewrites each gate of.
* `qftTowerEvolution_evolvePure_congr` — the bridge **intertwines** the two QFTs: running
  `qftTowerEvolution` on a transported input equals transporting the `qudit (2ⁿ⁺¹)` QFT output, so
  the transported operator genuinely *is* the QFT read through the register identification.

## Design notes

* **Why `qtower`, and why big-endian.** `qtower (n+1) qubit = qubit ⊗ qtower n qubit`
  *definitionally* (the outer control peels off on the left), so the successor bridge
  `(Iso.refl qubit).tmul (quditPowTower n)` — of domain `qubit ⊗ qudit (2ⁿ⁺¹)` — matches the tower
  with no `cast`. Peeling the *leading* (most-significant) qubit demands the big-endian split
  `quditProdIso 2 (2ⁿ⁺¹)`, whose source dimension is `2·2ⁿ⁺¹`; the only friction is that
  `2ⁿ⁺² = 2ⁿ⁺¹·2` reduces definitionally but `2·2ⁿ⁺¹` does not, absorbed by the one `quditDimCongr`
  cast per step (via `pow_succ'`).
* **Scope.** This file gives the bridge (with its recursive basis peel) and the QFT transport; the
  *closed* digit-form basis action `Φ |j⟩ = towerKet n (bits j)` — a global binary-expansion
  dictionary — and the wire-addressed re-expression of each Figure 5.1 gate are in
  `AxQM/Core/QftTowerBasis.lean` and the other `AxQM/Core/QftTower*.lean` files.

The bridge is assembled from the isomorphisms `quditProdIso`, `quditDimCongr` and `qftEvolution`;
compare the sibling bridge `qtowerQubitTensorPow`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The measured-QFT register bridge** `qudit (2ⁿ⁺¹) ≃ₛ qtower n qubit`: the system isomorphism
identifying the `2ⁿ⁺¹`-level register (on which the quantum Fourier transform `qftEvolution (2ⁿ⁺¹)`
lives) with the right-nested `(n+1)`-qubit control tower `qtower n qubit`. Built by induction on
`n`: the base `qudit (2¹) = qubit = qtower 0 qubit` is the identity, and each step peels the leading
qubit off the front with the tensor-factorisation iso `quditProdIso 2 (2ⁿ⁺¹)` — after the
`quditDimCongr` cast reconciling `2ⁿ⁺² = 2·2ⁿ⁺¹` (`pow_succ'`) — then tensors the identity on that
qubit with the tail bridge. Its action on the computational basis peels wire by wire
(`quditPowTower_congr_quditBasis_succ`); `qftTowerEvolution` transports the QFT across it. -/
def quditPowTower : (n : ℕ) → (qudit (2 ^ (n + 1))) ≃ₛ (qtower n qubit)
  | 0 => QSystem.Iso.refl qubit
  | n + 1 =>
      (quditDimCongr (pow_succ' 2 (n + 1))).trans
        ((quditProdIso 2 (2 ^ (n + 1))).trans
          ((QSystem.Iso.refl qubit).tmul (quditPowTower n)))

/-- Base unfolding of the register bridge: the single-qubit register `qudit (2¹)` is
`qtower 0 qubit` under the identity. -/
@[simp] theorem quditPowTower_zero : quditPowTower 0 = QSystem.Iso.refl qubit := rfl

/-- Step unfolding of the register bridge: cast `2ⁿ⁺² = 2·2ⁿ⁺¹`, peel the leading qubit with
`quditProdIso 2 (2ⁿ⁺¹)`, then tensor the identity on that qubit with the tail bridge. -/
theorem quditPowTower_succ (n : ℕ) :
    quditPowTower (n + 1)
      = (quditDimCongr (pow_succ' 2 (n + 1))).trans
          ((quditProdIso 2 (2 ^ (n + 1))).trans
            ((QSystem.Iso.refl qubit).tmul (quditPowTower n))) :=
  rfl

/-- **Basis peel for the register bridge.** On a computational-basis ket the bridge splits off the
leading (most-significant) qubit: writing the register index big-endian as `x·2ⁿ⁺¹ + y`
(`finProdFinEquiv (x, y)`, cast into `Fin (2ⁿ⁺²)`), the transported state is `|x⟩ ⊗ Φₙ |y⟩` with
`Φₙ = quditPowTower n` the tail bridge and `x : Fin 2` the leading bit. The recursive
computational-basis correctness of `quditPowTower`, obtained by feeding the tensor-factorisation
action `quditProdIso_congr_quditBasis` through the successor unfolding. -/
theorem quditPowTower_congr_quditBasis_succ (n : ℕ) (x : Fin 2) (y : Fin (2 ^ (n + 1))) :
    PureState.congr (quditPowTower (n + 1))
        (quditBasis ((finCongr (pow_succ' 2 (n + 1))).symm (finProdFinEquiv (x, y))))
      = (quditBasis x).tmul (PureState.congr (quditPowTower n) (quditBasis y)) := by
  -- Unfold one step, then push `PureState.congr` through the three iso factors using their action
  -- lemmas. `erw` is needed for the `congr_trans` steps: the composite's codomain
  -- `qubit ⊗ qtower n qubit` is only *definitionally* `qtower (n+1) qubit`, so keyed `rw` matching
  -- of the shared system metavariable fails; `rfl` closes the final `qudit 2` vs `qubit` defeq.
  rw [quditPowTower_succ]
  erw [PureState.congr_trans, quditDimCongr_congr_quditBasis, Equiv.apply_symm_apply,
    PureState.congr_trans, quditProdIso_congr_quditBasis, PureState.congr_tmul,
    PureState.congr_refl]
  rfl

/-- **The quantum Fourier transform transported onto the qubit tower.** The QFT
`qftEvolution (2ⁿ⁺¹)` of the single register `qudit (2ⁿ⁺¹)`, carried onto the right-nested
`(n+1)`-qubit control tower
`qtower n qubit` along the register bridge `quditPowTower n`. This is the QFT as an `Evolution` on
the tensor register the whole-circuit measured-QFT reduction (Problem 5.2) operates over. -/
def qftTowerEvolution (n : ℕ) : Evolution (qtower n qubit) :=
  Evolution.congr (quditPowTower n) (qftEvolution (2 ^ (n + 1)))

/-- **The transported QFT is the transported Figure 5.1 circuit.** `qftTowerEvolution n` equals the
transport of the wire-addressed gate composition `qftCircuitEvolution (n+1)` (Hadamards,
controlled-`Rₖ` rotations, swap layer), because on the single register the two agree
(`qftEvolution_eq_qftCircuitEvolution`). This is the form the wire-addressed reduction
rewrites gate by gate. -/
theorem qftTowerEvolution_eq_congr_qftCircuitEvolution (n : ℕ) :
    qftTowerEvolution n = Evolution.congr (quditPowTower n) (qftCircuitEvolution (n + 1)) := by
  rw [qftTowerEvolution, qftEvolution_eq_qftCircuitEvolution]

/-- **The register bridge intertwines the two QFTs.** Running the transported QFT
`qftTowerEvolution n` on a transported input `Φ ψ` equals transporting the single-register QFT
output `Φ (qftEvolution (2ⁿ⁺¹) ψ)` (`Φ = quditPowTower n`): the transported operator genuinely *is*
the quantum Fourier transform read through the register identification, not merely some unitary on
the tower. The specialisation of `Evolution.congr_evolvePure_congr` to the QFT and the bridge. -/
theorem qftTowerEvolution_evolvePure_congr (n : ℕ) (ψ : PureState (qudit (2 ^ (n + 1)))) :
    (qftTowerEvolution n).evolvePure (PureState.congr (quditPowTower n) ψ)
      = PureState.congr (quditPowTower n) ((qftEvolution (2 ^ (n + 1))).evolvePure ψ) :=
  Evolution.congr_evolvePure_congr (quditPowTower n) (qftEvolution (2 ^ (n + 1))) ψ

end AxQM
