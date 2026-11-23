/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.FourGateReachableCircuitDensity
import AxQM.Core.FourGateReachableCircuitTower

/-!
# The grounded tower circuit `Evolution` operators are dense up to a global phase
(N&C Exercise 4.43, four-gate bridge — density transport onto the control tower)

The four-gate universality bridge (Exercise 4.43) established the **operator-level density on the
register**: `exists_phase_smul_op_mem_closure_op_reachableCircuitEvolutions`
(`AxQM/Postulates/API/FourGateReachableCircuitDensity.lean`) states that, for the reachability
angle `θ` (`cos θ = 3/5`) and any unitary matrix `U ∈ U(2ⁿ⁺¹)`, some global phase `e^{iα}` makes
`e^{iα} • Matrix.toEuclideanCLM U` a limit of the operators of the register circuit submonoid
`reachableCircuitEvolutions n θ` (an `Evolution (qudit 2ⁿ⁺¹)` submonoid). Separately, the whole
register submonoid lifts onto the control tower:
`congr_quditPowTower_mem_reachableTowerCircuitEvolutions`
(`AxQM/Core/FourGateReachableCircuitTower.lean`) transports each register member onto
`Evolution (qtower n qubit)` via the register bridge `quditPowTower n`, landing it in the
grounded tower gate submonoid `reachableTowerCircuitEvolutions n θ`.

This file **transports the operator density from the register onto the control tower**: it pushes
the register operator density through the transport `⋆`-algebra isomorphism
`e.toIsometry.conjStarAlgEquiv` (`e := quditPowTower n`) — the conjugation that `Evolution.congr e`
enacts on operators (`Evolution.congr_op`) — so that, up to a global phase, *every* tower evolution
`T : Evolution (qtower n qubit)` is a limit of the operators of the grounded tower circuit submonoid
`reachableTowerCircuitEvolutions n θ`.

## What is formalised

* `exists_unitaryGroup_toEuclideanCLM_eq_op` — every `Evolution (qudit d)` operator is
  `Matrix.toEuclideanCLM` of a unitary matrix: for `T : Evolution (qudit d)` there is
  `U ∈ Matrix.unitaryGroup (Fin d) ℂ` with `Matrix.toEuclideanCLM U = T.op`. The matrix is
  `U := Matrix.toEuclideanCLM.symm T.op`; it is unitary because the `⋆`-algebra isomorphism
  `Matrix.toEuclideanCLM.symm` carries the operator unitarity `T.unitary` back to matrix unitarity
  (`map_star`/`map_mul`/`map_one`). This is what lets the matrix-indexed register density be applied
  to an *arbitrary* register evolution.
* `exists_phase_smul_op_mem_closure_op_reachableCircuitEvolutions'` — the register operator density,
  restated over an arbitrary register evolution `T : Evolution (qudit 2ⁿ⁺¹)` (rather than
  `Matrix.toEuclideanCLM U`): for `cos θ = 3/5`, some `e^{iα}` makes `e^{iα} • T.op` a limit of the
  operators of `reachableCircuitEvolutions n θ`. Immediate from the matrix-indexed form via
  `exists_unitaryGroup_toEuclideanCLM_eq_op`.
* `exists_phase_smul_op_mem_closure_op_reachableTowerCircuitEvolutions` — **the tower operator
  density**: for `cos θ = 3/5` and *any* tower evolution `T : Evolution (qtower n qubit)`, some
  global phase `e^{iα}` makes

    `e^{iα} • T.op ∈ closure ((·.op) '' ↑(reachableTowerCircuitEvolutions n θ))`.

  Proof: pull `T` back to the register (`T' := Evolution.congr e.symm T`, `e := quditPowTower n`),
  apply the register density (over the arbitrary `T'`) to get the phase `α` and
  `e^{iα} • T'.op ∈ closure ((·.op) '' reachableCircuitEvolutions n θ)`, then transport that
  membership through the continuous transport isomorphism `Φ := e.toIsometry.conjStarAlgEquiv`
  (continuous as a `ℂ`-linear map between the finite-dimensional operator spaces,
  `LinearMap.continuous_of_finiteDimensional`, so `image_closure_subset_closure_image` carries
  closure into closure; `ℂ`-linear, so it commutes with the phase, `map_smul`). Two identities close
  it: `Φ (T'.op) = (Evolution.congr e T').op = T.op` (`Evolution.congr_op`,
  `Evolution.congr_congr_symm`), pinning the transported point to `e^{iα} • T.op`; and for every
  register member `E ∈ reachableCircuitEvolutions n θ`, `Φ (E.op) = (Evolution.congr e E).op`
  (`Evolution.congr_op`) with `Evolution.congr e E ∈ reachableTowerCircuitEvolutions n θ`
  (`congr_quditPowTower_mem_reachableTowerCircuitEvolutions`), so `Φ` carries the register operator
  image inside the tower operator image (`closure_mono`).

Every generator of `reachableTowerCircuitEvolutions n θ` is a grounded gate on a tower wire
(single-qubit reachable rotations `Evolution.qtowerSingleWire n i E` and the `≤ 2`-control
reversible gates `mcNotTowerGate n S t ht`), so this is the density statement on the grounded tower
gate submonoid. Re-expressing those grounded tower generators over the four **named** gates
`hadamardGate, sGate, cnotGate, toffoliGate` (and the measurement-realised `rzThreeFifthsCircuit`
for the irrational `R_z(θ)`, at `θ = rzThreeFifthsAngle`) is in
`AxQM/Postulates/API/FourGateNamedTowerDensity.lean` and `AxQM/Core/FourGateNamedTower.lean`; it
must carry the essential measurement gadget, since the four *unitary* gates alone cannot generate
the irrational rotation `R_z(θ)`.
-/

open Matrix

namespace AxQM

noncomputable section

/-- **Every `Evolution (qudit d)` operator is `Matrix.toEuclideanCLM` of a unitary matrix.** For
`T : Evolution (qudit d)` there is a matrix `U ∈ Matrix.unitaryGroup (Fin d) ℂ` with
`Matrix.toEuclideanCLM U = T.op`. Take `U := Matrix.toEuclideanCLM.symm T.op`; the reconstruction
identity is `StarAlgEquiv.apply_symm_apply`, and `U` is unitary because the `⋆`-algebra isomorphism
`Matrix.toEuclideanCLM.symm` carries the operator unitarity `T.op * (T.op)⋆ = 1` (`T.unitary`) back
to `U * U⋆ = 1` (`map_star`/`map_mul`/`map_one`). This lets the matrix-indexed register density be
applied to an arbitrary register evolution. -/
theorem exists_unitaryGroup_toEuclideanCLM_eq_op {d : ℕ} (T : Evolution (qudit d)) :
    ∃ U, U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ Matrix.toEuclideanCLM (𝕜 := ℂ) U = T.op := by
  have hUeq : Matrix.toEuclideanCLM (𝕜 := ℂ) ((Matrix.toEuclideanCLM (𝕜 := ℂ)).symm T.op) = T.op :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply T.op
  refine ⟨(Matrix.toEuclideanCLM (𝕜 := ℂ)).symm T.op, ?_, hUeq⟩
  rw [Matrix.mem_unitaryGroup_iff]
  apply EquivLike.injective (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d))
  rw [map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ)), map_star (Matrix.toEuclideanCLM (𝕜 := ℂ)), hUeq,
    map_one (Matrix.toEuclideanCLM (𝕜 := ℂ))]
  exact (Unitary.mem_iff.mp T.unitary).2

/-- **The register operator density, over an arbitrary register evolution.** For the reachability
angle `θ` (`cos θ = 3/5`) and *any* `T : Evolution (qudit 2ⁿ⁺¹)`, some global phase `e^{iα}` makes
`e^{iα} • T.op` a limit of the operators of the register circuit submonoid
`reachableCircuitEvolutions n θ`. Immediate from the matrix-indexed form
`exists_phase_smul_op_mem_closure_op_reachableCircuitEvolutions` by writing `T.op` as
`Matrix.toEuclideanCLM U` for a unitary matrix `U` (`exists_unitaryGroup_toEuclideanCLM_eq_op`). -/
theorem exists_phase_smul_op_mem_closure_op_reachableCircuitEvolutions'
    {n : ℕ} {θ : ℝ} (hθ : Real.cos θ = 3 / 5) (T : Evolution (qudit (2 ^ (n + 1)))) :
    ∃ α : ℝ, Complex.exp ((α : ℂ) * Complex.I) • T.op ∈
      closure ((fun E : Evolution (qudit (2 ^ (n + 1))) => E.op) ''
        (reachableCircuitEvolutions n θ : Set (Evolution (qudit (2 ^ (n + 1)))))) := by
  obtain ⟨U, hU, hUeq⟩ := exists_unitaryGroup_toEuclideanCLM_eq_op T
  obtain ⟨α, hα⟩ := exists_phase_smul_op_mem_closure_op_reachableCircuitEvolutions hθ hU
  rw [hUeq] at hα
  exact ⟨α, hα⟩

/-- **The grounded tower circuit `Evolution` operators are dense up to a global phase.** For the
reachability angle `θ` (`cos θ = 3/5`) and *any* tower evolution `T : Evolution (qtower n qubit)`,
some global phase `e^{iα}` makes `e^{iα} • T.op` a limit of the operators of the grounded tower
circuit submonoid `reachableTowerCircuitEvolutions n θ`:

  `e^{iα} • T.op ∈ closure ((·.op) '' ↑(reachableTowerCircuitEvolutions n θ))`.

The register operator density (over an arbitrary register evolution,
`exists_phase_smul_op_mem_closure_op_reachableCircuitEvolutions'`), applied to the pull-back
`T' := Evolution.congr (quditPowTower n).symm T`, supplies the phase `α` with
`e^{iα} • T'.op ∈ closure ((·.op) '' reachableCircuitEvolutions n θ)`. Transporting this membership
through the continuous transport `⋆`-algebra isomorphism
`Φ := (quditPowTower n).toIsometry.conjStarAlgEquiv`
— continuous as a `ℂ`-linear map between the finite-dimensional operator spaces
(`LinearMap.continuous_of_finiteDimensional`), so it carries closure into closure
(`image_closure_subset_closure_image`), and being `ℂ`-linear it commutes with the phase (`map_smul`)
— lands `e^{iα} • T.op` (using `Φ (T'.op) = (Evolution.congr e T').op = T.op`, i.e.
`Evolution.congr_op` and `Evolution.congr_congr_symm`) in the closure of the `Φ`-image of the
register operator image. Finally `Φ (E.op) = (Evolution.congr e E).op` (`Evolution.congr_op`) with
`Evolution.congr e E ∈ reachableTowerCircuitEvolutions n θ`
(`congr_quditPowTower_mem_reachableTowerCircuitEvolutions`), so that `Φ`-image sits inside the tower
operator image and `closure_mono` concludes.

Every generator of `reachableTowerCircuitEvolutions n θ` is a grounded gate on a tower wire, so this
is the density statement on the grounded tower gate submonoid; re-expressing those generators over
the four *named* gates `hadamardGate, sGate, cnotGate, toffoliGate` (with the measurement-realised
`R_z(θ)`) is in `AxQM/Postulates/API/FourGateNamedTowerDensity.lean`. -/
theorem exists_phase_smul_op_mem_closure_op_reachableTowerCircuitEvolutions
    {n : ℕ} {θ : ℝ} (hθ : Real.cos θ = 3 / 5) (T : Evolution (qtower n qubit)) :
    ∃ α : ℝ, Complex.exp ((α : ℂ) * Complex.I) • T.op ∈
      closure ((fun E : Evolution (qtower n qubit) => E.op) ''
        (reachableTowerCircuitEvolutions n θ : Set (Evolution (qtower n qubit)))) := by
  set e := quditPowTower n with he
  obtain ⟨α, hα⟩ :=
    exists_phase_smul_op_mem_closure_op_reachableCircuitEvolutions' hθ (Evolution.congr e.symm T)
  refine ⟨α, ?_⟩
  set Φ := e.toIsometry.conjStarAlgEquiv with hΦ
  have hcont : Continuous ⇑Φ :=
    LinearMap.continuous_of_finiteDimensional Φ.toAlgEquiv.toLinearMap
  have h1 := image_closure_subset_closure_image hcont (Set.mem_image_of_mem Φ hα)
  have hΦeq : Φ (Complex.exp ((α : ℂ) * Complex.I) • (Evolution.congr e.symm T).op)
      = Complex.exp ((α : ℂ) * Complex.I) • T.op := by
    rw [map_smul, ← Evolution.congr_op e (Evolution.congr e.symm T), Evolution.congr_congr_symm]
  rw [hΦeq] at h1
  refine closure_mono ?_ h1
  rintro _ ⟨_, ⟨E, hE, rfl⟩, rfl⟩
  exact ⟨Evolution.congr e E, congr_quditPowTower_mem_reachableTowerCircuitEvolutions hE,
    (Evolution.congr_op e E).symm⟩

end

end AxQM
