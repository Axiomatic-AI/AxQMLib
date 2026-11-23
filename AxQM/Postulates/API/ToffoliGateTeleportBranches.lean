/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ToffoliGateTeleportReshape
import AxQM.Postulates.API.MeasureObservable
import AxQM.Postulates.API.RzThreeFifthsCircuit

/-!
# AxQM.Postulates.API — the Toffoli gate-teleportation outcome branches (N&C Ex 10.68)

The **eight-outcome branch decomposition** of the pre-measurement gate-teleportation state of the
fault-tolerant Toffoli circuit of Nielsen & Chuang Exercise 10.68 (the Figure on p. 488, part (2)) —
the vector identity that exhibits the three data-qubit measurements: the two control data qubits
`d_x, d_y` measured in the *computational* (`Z`) basis and the target data qubit `d_z` measured in
the `X` basis. It is the Toffoli analogue of the CNOT teleportation's correction-free branch form
`gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_teleport` (Problem 4.6): the pure superposition
that the joint measurement then reads out, one outcome branch at a time.

## Role in Exercise 10.68

After the offline resource `toffoliAncilla = |Θ_T⟩ = ½ Σ_{a,b} |a, b, a·b⟩` is coupled to the data
by `toffoliTeleportCoupling`, the pre-measurement state on the coupled-pairs register
`(a₁ ⊗ d_x) ⊗ ((a₂ ⊗ d_y) ⊗ (a₃ ⊗ d_z))` is
`toffoliTeleportCoupling_op_toffoliTeleportReshapedInput`,

  `½ Σ_{a,b} |a, x⊕a⟩ |b, y⊕b⟩ |a·b ⊕ z, z⟩`.

The circuit then measures the three **data** qubits `d_x, d_y, d_z` (the second qubit of each pair).
The two control data qubits `d_x = x⊕a`, `d_y = y⊕b` are read in the computational basis; the target
data qubit `d_z` is Hadamarded and read (equivalently, measured in the `X` basis) — matching the `H`
on the target wire before the measurement in the Figure. Expanding `d_z = |z⟩` over the `X`
eigenbasis `{H|0⟩, H|1⟩}` (`qubitBasis_vec_eq_invSqrt2_sum_hadamard`) turns the four-branch sum into
the manifest **eight-branch** superposition

  `2⁻³ᐟ² Σ_{a,b,m₃} (-1)^{m₃·z} |a, x⊕a⟩ |b, y⊕b⟩ |a·b ⊕ z, H|m₃⟩⟩`,

one branch per joint outcome `(d_x, d_y, d_z^X) = (x⊕a, y⊕b, m₃)`. Reading a branch (Born rule)
leaves the ancilla block `(a₁, a₂, a₃) = (a, b, a·b⊕z)` in the state that the propagated-byproduct
correction `B_m` (`toffoliSwapByproductsPropagated`, `NC/Ch10/Exercise10_68_FTToffoli`) turns into
`Toffoli|xyz⟩ = |x, y, z⊕xy⟩` — the corrected identity assembled in
`Postulates/API/ToffoliGateTeleportCorrection`.

## What is formalised

* `qubitBasis_vec_eq_invSqrt2_sum_hadamard` — the general **`X`-basis (Hadamard) expansion of a
  computational-basis qubit**: `|z⟩ = 2⁻¹ᐟ² Σ_{m} (-1)^{m·z} H|m⟩` (`H|m⟩` the `m`-th `X`
  eigenstate). The residual state of an `X`-basis measurement of `|z⟩` with outcome `m` is `H|m⟩`
  with amplitude `2⁻¹ᐟ² (-1)^{m·z}`. Proved from the Hadamard involution `H·H = 1` and the binary
  Hadamard action `hadamardGate_evolvePure_qubitBasis_vec_binary`.

* `toffoliTeleportCoupling_op_toffoliTeleportReshapedInput_hadamardBranches` — **the eight-outcome
  branch decomposition** of the pre-measurement state (on the abstract coupling input
  `toffoliTeleportReshapedInput`), the display above. The two control data qubits carry the
  `Z`-basis outcomes `x⊕a`, `y⊕b`; the target data qubit carries the `X`-basis outcome `H|m₃⟩` with
  the sign `(-1)^{m₃·z}`. Proved from the pre-measurement identity by expanding the target `|z⟩`
  over the `X` eigenbasis and distributing the coupling through the resulting triple sum.

* `toffoliTeleportCoupling_op_reshape_toffoliAncilla_tmul` — **the same, on the honest prepared
  resource**: the coupling applied to `reshape(toffoliAncilla ⊗ |xyz⟩)` (the offline resource beside
  the data) equals the eight-branch superposition. The `reshape(|Θ_T⟩ ⊗ |xyz⟩) =
  toffoliTeleportReshapedInput` realisation
  (`toffoliTeleportReshape_toIsometry_toffoliAncilla_tmul`) makes this the pre-measurement state of
  the *physical* circuit, not merely of an abstract input.

## Design notes

* **Why `X`-basis on the target.** For a general (superposition) data target, a computational-basis
  measurement of `d_z` would collapse `z` and destroy the teleported information; the gate
  teleportation must measure `d_z` in the `X` basis so that the target is teleported into the
  ancilla `a₃` (up to a `Z^{m₃}` correction), exactly as the Figure Hadamards the target wire before
  measuring it. The branch's residual `d_z` state is therefore the `X` eigenstate `H|m₃⟩`, and the
  branch carries the phase `(-1)^{m₃·z}` — the seed of the `Z^{m₃}` byproduct on `a₃`.

* **Branch labelling.** The sum is indexed by the two ancilla control values `(a, b)` and the target
  outcome `m₃`; the two control *outcomes* are `(d_x, d_y) = (x⊕a, y⊕b)`, so the ancilla holds
  `(a₁, a₂) = (a, b)` and `a₃ = a·b ⊕ z` — displaying the ancilla output directly. Re-indexing to
  the outcomes `(m₁, m₂) = (x⊕a, y⊕b)` is the trivial substitution `a = x⊕m₁`, `b = y⊕m₂`.

* **Distribution across the composite system.** Expanding the target `|z⟩` introduces a scalar•sum
  on the innermost (deepest) tensor factor, which must be pushed out through the two surrounding
  composite tensors. The generic `TensorProduct.tmul_smul` / `tmul_sum` rewrites are blocked at the
  composite-system level by the `QSystem`-projected module-instance diamond (the standing issue on
  this development); so the fixed left factors are bundled as a single ℂ-linear map `φ` (nested
  `TensorProduct.mk`s) and the scalar / sum are pushed through `φ` by `map_smul` / `map_sum` — the
  same idiom used for the CNOT teleportation reshape.

The statement of Exercise 10.68 is in `AxQM/NC/Ch10/Exercise10_68_FTToffoli.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The `X`-basis (Hadamard) expansion of a computational-basis qubit.** For `z : Fin 2`,

  `|z⟩ = 2⁻¹ᐟ² Σ_{m} (-1)^{m·z} H|m⟩`,

where `H|m⟩ = hadamardGate.evolvePure |m⟩` is the `m`-th `X` eigenstate (`|+⟩` for `m = 0`, `|−⟩`
for `m = 1`). Equivalently, an `X`-basis measurement of `|z⟩` yields outcome `m` with residual state
`H|m⟩` and amplitude `2⁻¹ᐟ² (-1)^{m·z}` — the fact consumed when the target data qubit `d_z` of the
Toffoli gate-teleportation circuit is measured in the `X` basis. Proved from the Hadamard involution
`H·H = 1` (`hadamardGate_comp_self`): `|z⟩ = H(H|z⟩)`, then the binary Hadamard action
`hadamardGate_evolvePure_qubitBasis_vec_binary` (`H|z⟩ = 2⁻¹ᐟ²(|0⟩ + (-1)^z|1⟩)`) with `H` applied
termwise. -/
theorem qubitBasis_vec_eq_invSqrt2_sum_hadamard (z : Fin 2) :
    (qubitBasis z).vec = Concrete.invSqrt2 • ∑ m : Fin 2,
      ((-1 : ℂ) ^ (m.val * z.val)) • (hadamardGate.evolvePure (qubitBasis m)).vec := by
  have hH : (qubitBasis z).vec
      = hadamardGate.op ((hadamardGate.evolvePure (qubitBasis z)).vec) := by
    rw [Evolution.evolvePure_vec, ← ContinuousLinearMap.comp_apply, ← Evolution.comp_op,
      hadamardGate_comp_self, Evolution.id_op, one_apply_eq_self]
  rw [hH, hadamardGate_evolvePure_qubitBasis_vec_binary, Fin.sum_univ_two]
  simp only [map_smul, map_add, Evolution.evolvePure_vec, Fin.val_zero, Fin.val_one,
    zero_mul, one_mul, pow_zero, one_smul]

set_option maxHeartbeats 1600000 in
-- Distributing the coupling output over the `X`-expansion triple sum on the 64-dimensional
-- coupled-pairs register exceeds the default heartbeat budget.
/-- **The eight-outcome branch decomposition of the pre-measurement gate-teleportation state**
(Nielsen & Chuang, Exercise 10.68 part (2); the Toffoli analogue of the CNOT correction-free branch
form `gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_teleport`). Expanding the target data
qubit `d_z = |z⟩` of the pre-measurement state
`toffoliTeleportCoupling_op_toffoliTeleportReshapedInput`
over the `X` eigenbasis exhibits the three data-qubit measurements as an eight-branch superposition:

  `toffoliTeleportCoupling (½ Σ_{a,b} |a,x⟩|b,y⟩|a·b, z⟩)
      = 2⁻³ᐟ² Σ_{a,b,m₃} (-1)^{m₃·z} |a, x⊕a⟩ |b, y⊕b⟩ |a·b ⊕ z, H|m₃⟩⟩`.

The two control data qubits carry the computational-basis outcomes `d_x = x⊕a`, `d_y = y⊕b`; the
target data qubit carries the `X`-basis outcome `H|m₃⟩` with the sign `(-1)^{m₃·z}` — one branch per
joint outcome `(x⊕a, y⊕b, m₃)`. Reading a branch (Born rule) leaves the ancilla block in
`|a, b, a·b⊕z⟩`, which the propagated-byproduct correction `B_m` turns into `Toffoli|xyz⟩`. Proved
by expanding `|z⟩` via `qubitBasis_vec_eq_invSqrt2_sum_hadamard` and pushing the coupling output
through the resulting triple sum (the fixed left tensor factors bundled as a ℂ-linear map to cross
the composite-system module diamond). -/
theorem toffoliTeleportCoupling_op_toffoliTeleportReshapedInput_hadamardBranches (x y z : Fin 2) :
    toffoliTeleportCoupling.op (toffoliTeleportReshapedInput x y z)
      = Concrete.invSqrt2 ^ 3 • ∑ a : Fin 2, ∑ b : Fin 2, ∑ m : Fin 2,
          ((-1 : ℂ) ^ (m.val * z.val)) •
            (((qubitBasis a).tmul (qubitBasis (x + a))).tmul
              (((qubitBasis b).tmul (qubitBasis (y + b))).tmul
                ((qubitBasis (a * b + z)).tmul (hadamardGate.evolvePure (qubitBasis m))))).vec := by
  -- Per (a, b), expand the target `|z⟩` and distribute through the bundled left factors.
  have hbranch : ∀ a b : Fin 2,
      (((qubitBasis a).tmul (qubitBasis (x + a))).tmul
        (((qubitBasis b).tmul (qubitBasis (y + b))).tmul
          ((qubitBasis (a * b + z)).tmul (qubitBasis z)))).vec
      = Concrete.invSqrt2 • ∑ m : Fin 2, ((-1 : ℂ) ^ (m.val * z.val)) •
          (((qubitBasis a).tmul (qubitBasis (x + a))).tmul
            (((qubitBasis b).tmul (qubitBasis (y + b))).tmul
              ((qubitBasis (a * b + z)).tmul (hadamardGate.evolvePure (qubitBasis m))))).vec := by
    intro a b
    -- `φ w = |a,x⊕a⟩ ⊗ (|b,y⊕b⟩ ⊗ (|a·b⊕z⟩ ⊗ w))`, the fixed prefix as a ℂ-linear map in the
    -- target slot `w`; both branches are `φ` of the residual target state.
    let φ : qubit.space →ₗ[ℂ]
        ((qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).space :=
      (TensorProduct.mk ℂ (qubit ⊗ qubit).space ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space
          ((qubitBasis a).tmul (qubitBasis (x + a))).vec).comp
        ((TensorProduct.mk ℂ (qubit ⊗ qubit).space (qubit ⊗ qubit).space
            ((qubitBasis b).tmul (qubitBasis (y + b))).vec).comp
          (TensorProduct.mk ℂ qubit.space qubit.space (qubitBasis (a * b + z)).vec))
    have hL : (((qubitBasis a).tmul (qubitBasis (x + a))).tmul
        (((qubitBasis b).tmul (qubitBasis (y + b))).tmul
          ((qubitBasis (a * b + z)).tmul (qubitBasis z)))).vec = φ (qubitBasis z).vec := rfl
    have hR : ∀ m : Fin 2, (((qubitBasis a).tmul (qubitBasis (x + a))).tmul
        (((qubitBasis b).tmul (qubitBasis (y + b))).tmul
          ((qubitBasis (a * b + z)).tmul (hadamardGate.evolvePure (qubitBasis m))))).vec
        = φ (hadamardGate.evolvePure (qubitBasis m)).vec := fun m => rfl
    rw [hL, qubitBasis_vec_eq_invSqrt2_sum_hadamard z, map_smul, map_sum]
    simp only [map_smul, ← hR]
  rw [toffoliTeleportCoupling_op_toffoliTeleportReshapedInput]
  simp only [hbranch, ← Finset.smul_sum, smul_smul]
  congr 1
  rw [pow_succ, pow_two, Concrete.invSqrt2_mul_self]

set_option maxHeartbeats 800000 in
-- The `.op`/reshape/`.vec` bridge on the 64-dimensional register exceeds the default budget.
/-- **The pre-measurement branch decomposition on the honest prepared resource** (Nielsen & Chuang,
Exercise 10.68 part (2)). Coupling the *prepared* offline resource `toffoliAncilla` (reshaped beside
the data `|xyz⟩`) to the data and expanding the target in the `X` basis yields the eight-outcome
branch superposition:

  `toffoliTeleportCoupling (reshape(|Θ_T⟩ ⊗ |xyz⟩))
      = 2⁻³ᐟ² Σ_{a,b,m₃} (-1)^{m₃·z} |a, x⊕a⟩ |b, y⊕b⟩ |a·b ⊕ z, H|m₃⟩⟩`.

This upgrades `toffoliTeleportCoupling_op_toffoliTeleportReshapedInput_hadamardBranches` from the
abstract coupling input `toffoliTeleportReshapedInput` to the honest reshape of the prepared
resource `toffoliAncilla ⊗ |xyz⟩` (via `toffoliTeleportReshape_toIsometry_toffoliAncilla_tmul`), so
the
eight-branch form is the pre-measurement state of the *physical* fault-tolerant Toffoli circuit
(offline ancilla prep, then data↔ancilla coupling), ready for the three data-qubit measurements. -/
theorem toffoliTeleportCoupling_op_reshape_toffoliAncilla_tmul (x y z : Fin 2) :
    toffoliTeleportCoupling.op
        (toffoliTeleportReshape.toIsometry (toffoliAncilla.tmul (qubitThreeBasis (x, y, z))).vec)
      = Concrete.invSqrt2 ^ 3 • ∑ a : Fin 2, ∑ b : Fin 2, ∑ m : Fin 2,
          ((-1 : ℂ) ^ (m.val * z.val)) •
            (((qubitBasis a).tmul (qubitBasis (x + a))).tmul
              (((qubitBasis b).tmul (qubitBasis (y + b))).tmul
                ((qubitBasis (a * b + z)).tmul (hadamardGate.evolvePure (qubitBasis m))))).vec := by
  rw [toffoliTeleportReshape_toIsometry_toffoliAncilla_tmul,
    toffoliTeleportCoupling_op_toffoliTeleportReshapedInput_hadamardBranches]

end AxQM
