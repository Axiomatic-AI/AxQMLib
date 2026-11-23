/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Fredkin

/-!
# AxQM.Postulates.API — the Toffoli gate-teleportation coupling (N&C Exercise 10.68)

The **data↔ancilla coupling** of the fault-tolerant Toffoli circuit of Nielsen & Chuang Exercise
10.68 (the Figure on p. 488, part (2)), and the **pre-measurement gate-teleportation state** it
produces — the Toffoli analogue of the π/8-gate circuit output `Concrete.piEighthCircuitOut` (whose
measured branches `Concrete.piEighthCircuitOut_measure_zero / _measure_one` are the reduction
core of Exercise 10.66).

## The construction

After "moving the final Toffoli all the way back to the left side" (part (2)), the ancilla block is
prepared *offline* in the entangled resource state

  `|Θ_T⟩ = ½ (|000⟩ + |010⟩ + |100⟩ + |111⟩) = ½ Σ_{a,b} |a, b, a·b⟩`   (`toffoliAncilla`),

the AND magic state (`a·b` = the AND of the two controls). The data block `|xyz⟩` is then
**coupled** to the ancilla by three `CNOT`s read off the Figure — control ancillas onto the data
controls, data target onto the ancilla target:

  `CNOT(a₁ → d_x) · CNOT(a₂ → d_y) · CNOT(d_z → a₃)`   (`toffoliTeleportCoupling`),

after which the three data qubits are measured (`d_x, d_y` in the computational basis, `d_z` in the
`X` basis) and classically-controlled Clifford corrections — exactly the propagated byproducts
`B = X₁·CNOT₂₃ · X₂·CNOT₁₃ · Z₃·CZ₁₂` of `NC/Ch10/Exercise10_68_FTToffoli`
(`toffoliSwapByproductsPropagated`) — recover `Toffoli|xyz⟩` on the ancilla block.

## What is formalised here

Working on the **coupled-pairs register** `(a₁ ⊗ d_x) ⊗ ((a₂ ⊗ d_y) ⊗ (a₃ ⊗ d_z))` — the three
data↔ancilla pairs laid out adjacently, so the coupling is a product of three ordinary two-qubit
gates placed by `Evolution.onLeft`/`onRight`:

* `toffoliTeleportCoupling` — the coupling `Evolution` `CNOT(a₁→d_x) · CNOT(a₂→d_y) · CNOT(d_z→a₃)`.
  The two control couplings are `cnotGate` (ancilla = control); the target coupling is
  `reversedCnotGate` (data = control), matching the Figure's reversed arrow on the target wire.
* `toffoliTeleportCoupling_evolvePure_qubitBasis` — its computational-basis truth table:
  `|a,x⟩|b,y⟩|c,z⟩ ↦ |a, x⊕a⟩|b, y⊕b⟩|c⊕z, z⟩`. The data qubits pick up the ancilla controls
  (`x ↦ x⊕a`, `y ↦ y⊕b`) and the ancilla target picks up the data target (`c ↦ c⊕z`).
* `toffoliTeleportCoupling_op_qubitBasisVec` — the same truth table at the level of `.op` on
  `.vec`, the linear per-branch fact the superposition identity below sums over.
* `toffoliTeleportReshapedInput` — the resource-consuming input `|Θ_T⟩ ⊗ |xyz⟩`, laid out on the
  coupled-pairs register as the explicit AND-magic superposition
  `½ Σ_{a,b} |a,x⟩|b,y⟩|a·b, z⟩` (the `reshape(|Θ_T⟩ ⊗ |xyz⟩)` whose reshape-isometry realisation is
  built in `Postulates/API/ToffoliGateTeleportReshape`).
* `toffoliTeleportCoupling_op_toffoliTeleportReshapedInput` — **the pre-measurement
  gate-teleportation state** (the eq.-10.119 analogue): coupling the AND magic state to the data
  yields `½ Σ_{a,b} |a, x⊕a⟩|b, y⊕b⟩|a·b ⊕ z, z⟩`. Measuring the data controls `x⊕a`, `y⊕b`
  (computational basis) collapses the sum to the single `(a,b) = (x⊕m₁, y⊕m₂)` branch, leaving the
  ancilla block in `|x⊕m₁, y⊕m₂, (x⊕m₁)(y⊕m₂) ⊕ z⟩`, which the propagated-byproduct correction
  `B_m` turns into `Toffoli|xyz⟩ = |x, y, z ⊕ xy⟩` — the content assembled in the companion
  `ToffoliGateTeleport*` files (the data measurements collapsing the eight branches, then the
  corrected identity).

## Design notes

* **Coupled-pairs register.** The three coupling gates act on the pairs `(aᵢ, dᵢ)`, which are on
  opposite sides of the physical `(ancilla block) ⊗ (data block)` split. Rather than build three
  cross-block gates on the nested 64-dimensional register, they are placed on the register that lays
  the pairs adjacently — mirroring the CNOT gate-teleportation development, which co-locates the
  coupled qubits with the reshape `gateTeleportProtocolReshape` before placing `cnotGate.onRight`.
  The reshape isometry `reshape(|Θ_T⟩ ⊗ |ψ⟩) = toffoliTeleportReshapedInput` connecting this
  register to the physical `swapThenToffoli` register is built in
  `Postulates/API/ToffoliGateTeleportReshape`.
* **Why `reversedCnotGate` on the target pair.** The Figure couples the two control ancillas *onto*
  the data (`•` on the ancilla wire, `⊕` on the data wire — ancilla is the control), but couples the
  data target *onto* the ancilla (`•` on the data wire `d_z`, `⊕` on the ancilla wire `a₃`). So the
  target pair uses `reversedCnotGate` (second qubit = control), whose truth table `|a,b⟩ ↦ |a⊕b, b⟩`
  supplies `|c, z⟩ ↦ |c⊕z, z⟩`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

set_option maxHeartbeats 800000 in
-- The coupling `Evolution` lives on the 64-dimensional coupled-pairs register; composing the three
-- blockwise gates there exceeds the default elaboration budget (as for the library's other
-- large-composite `Evolution`s, e.g. `swapThenToffoli`, `toffoliAncillaPrep`).
/-- **The Toffoli gate-teleportation coupling** (Nielsen & Chuang, Exercise 10.68 part (2), the
three `CNOT`s of the Figure on p. 488): on the coupled-pairs register
`(a₁ ⊗ d_x) ⊗ ((a₂ ⊗ d_y) ⊗ (a₃ ⊗ d_z))` — the three ancilla↔data pairs laid adjacently — apply

  `CNOT(a₁ → d_x)` on the first pair, `CNOT(a₂ → d_y)` on the second, and `CNOT(d_z → a₃)` on the
  third.

The two control pairs use `cnotGate` (ancilla = control, data = target); the target pair uses
`reversedCnotGate` (data `d_z` = control, ancilla `a₃` = target), matching the reversed arrow on the
target wire of the Figure. Applied to the resource-consuming input `toffoliTeleportReshapedInput` it
produces the pre-measurement gate-teleportation state
(`toffoliTeleportCoupling_op_toffoliTeleportReshapedInput`). -/
def toffoliTeleportCoupling :
    Evolution ((qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))) :=
  (cnotGate.onLeft ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).comp
    (((cnotGate.onLeft (qubit ⊗ qubit)).onRight (qubit ⊗ qubit)).comp
      ((reversedCnotGate.onRight (qubit ⊗ qubit)).onRight (qubit ⊗ qubit)))

set_option maxHeartbeats 800000 in
-- Unfolding `toffoliTeleportCoupling` on the 64-dimensional register exceeds the default budget.
/-- **The Toffoli-teleportation coupling truth table.** On a computational-basis state of the
coupled-pairs register,

  `toffoliTeleportCoupling |a,x⟩|b,y⟩|c,z⟩ = |a, x⊕a⟩ |b, y⊕b⟩ |c⊕z, z⟩`.

Each data control is XORed with its ancilla control (`x ↦ x⊕a`, `y ↦ y⊕b`, from the two
`cnotGate`s), and the ancilla target is XORed with the data target (`c ↦ c⊕z`, from the
`reversedCnotGate`). Proved by pushing each blockwise gate through the product state with
`Evolution.onLeft_evolvePure` / `onRight_evolvePure` and the `cnotGate` / `reversedCnotGate` truth
tables. -/
theorem toffoliTeleportCoupling_evolvePure_qubitBasis (a x b y c z : Fin 2) :
    toffoliTeleportCoupling.evolvePure
        (((qubitBasis a).tmul (qubitBasis x)).tmul
          (((qubitBasis b).tmul (qubitBasis y)).tmul ((qubitBasis c).tmul (qubitBasis z))))
      = ((qubitBasis a).tmul (qubitBasis (x + a))).tmul
          (((qubitBasis b).tmul (qubitBasis (y + b))).tmul
            ((qubitBasis (c + z)).tmul (qubitBasis z))) := by
  simp only [toffoliTeleportCoupling, Evolution.evolvePure_comp, Evolution.onLeft_evolvePure,
    Evolution.onRight_evolvePure, reversedCnotGate_evolvePure_qubitBasis,
    cnotGate_evolvePure_qubitBasis]

set_option maxHeartbeats 800000 in
-- The `.op`/`.vec` bridge on the 64-dimensional register exceeds the default budget.
/-- **The coupling truth table on vectors** (`.op` on `.vec`): the linear per-branch fact
`toffoliTeleportCoupling.op |a,x⟩|b,y⟩|c,z⟩ = |a, x⊕a⟩|b, y⊕b⟩|c⊕z, z⟩` that
`toffoliTeleportCoupling_op_toffoliTeleportReshapedInput` sums over. The `.op`/`.vec` reading of
`toffoliTeleportCoupling_evolvePure_qubitBasis` (via `Evolution.evolvePure_vec`). -/
theorem toffoliTeleportCoupling_op_qubitBasisVec (a x b y c z : Fin 2) :
    toffoliTeleportCoupling.op
        (((qubitBasis a).tmul (qubitBasis x)).tmul
          (((qubitBasis b).tmul (qubitBasis y)).tmul ((qubitBasis c).tmul (qubitBasis z)))).vec
      = (((qubitBasis a).tmul (qubitBasis (x + a))).tmul
          (((qubitBasis b).tmul (qubitBasis (y + b))).tmul
            ((qubitBasis (c + z)).tmul (qubitBasis z)))).vec := by
  rw [← Evolution.evolvePure_vec, toffoliTeleportCoupling_evolvePure_qubitBasis]

set_option maxHeartbeats 800000 in
-- The `.vec` tensors on the 64-dimensional register exceed the default elaboration budget.
/-- **The resource-consuming input `reshape(|Θ_T⟩ ⊗ |xyz⟩)`**, on the coupled-pairs register: the
AND magic state `|Θ_T⟩ = ½ Σ_{a,b} |a, b, a·b⟩` tensored with the data `|xyz⟩` and reshaped so each
ancilla qubit `aᵢ` sits beside its data partner `dᵢ`,

  `½ Σ_{a,b} |a, x⟩ |b, y⟩ |a·b, z⟩`.

This is the vector fed into the coupling in the gate-teleportation circuit of Exercise 10.68
part (2) (the ancilla prepared offline in the leftmost dotted box, beside the data). The realisation
of this vector as the reshape isometry applied to `toffoliAncilla.tmul` the data state is built in
`Postulates/API/ToffoliGateTeleportReshape`. -/
def toffoliTeleportReshapedInput (x y z : Fin 2) :
    ((qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).space :=
  (2⁻¹ : ℂ) • ∑ a : Fin 2, ∑ b : Fin 2,
    (((qubitBasis a).tmul (qubitBasis x)).tmul
      (((qubitBasis b).tmul (qubitBasis y)).tmul
        ((qubitBasis (a * b)).tmul (qubitBasis z)))).vec

set_option maxHeartbeats 800000 in
-- Pushing `.op` through the double sum on the 64-dimensional register exceeds the default budget.
/-- **The pre-measurement gate-teleportation state** (Nielsen & Chuang, Exercise 10.68 part (2); the
Toffoli analogue of the π/8 eq. 10.119 / `Concrete.piEighthCircuitOut`). Coupling the AND magic
state to the data yields

  `toffoliTeleportCoupling (½ Σ_{a,b} |a,x⟩|b,y⟩|a·b, z⟩)
      = ½ Σ_{a,b} |a, x⊕a⟩ |b, y⊕b⟩ |a·b ⊕ z, z⟩`.

Measuring the two data controls `x⊕a`, `y⊕b` (computational basis) collapses the sum to the single
`(a,b) = (x⊕m₁, y⊕m₂)` branch, leaving the ancilla block in `|x⊕m₁, y⊕m₂, (x⊕m₁)(y⊕m₂) ⊕ z⟩`; the
propagated-byproduct correction `B_m` (`toffoliSwapByproductsPropagated`) then turns it into
`Toffoli|xyz⟩ = |x, y, z ⊕ xy⟩`. Proved by pushing the linear `toffoliTeleportCoupling.op` through
the scalar and the double sum and firing the per-branch truth table
`toffoliTeleportCoupling_op_qubitBasisVec`. -/
theorem toffoliTeleportCoupling_op_toffoliTeleportReshapedInput (x y z : Fin 2) :
    toffoliTeleportCoupling.op (toffoliTeleportReshapedInput x y z)
      = (2⁻¹ : ℂ) • ∑ a : Fin 2, ∑ b : Fin 2,
          (((qubitBasis a).tmul (qubitBasis (x + a))).tmul
            (((qubitBasis b).tmul (qubitBasis (y + b))).tmul
              ((qubitBasis (a * b + z)).tmul (qubitBasis z)))).vec := by
  simp only [toffoliTeleportReshapedInput, map_smul, map_sum,
    toffoliTeleportCoupling_op_qubitBasisVec]

end AxQM
