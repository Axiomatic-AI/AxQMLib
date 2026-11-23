/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.FourGateReachableCircuit
import ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM

/-!
# The register circuit `Evolution` operators are dense up to a global phase
(N&C Exercise 4.43, four-gate bridge — density transport through `Matrix.toEuclideanCLM`)

The four-gate universality bridge (Exercise 4.43) starts from the *matrix* density theorem
`Concrete.exists_phase_smul_mem_closure_reachableCircuits`: for the reachability angle `θ`
(`cos θ = 3/5`) and any `U ∈ U(2ⁿ⁺¹)`, some global phase `e^{iα}` makes `e^{iα} • U` a limit of the
reachable circuit matrices `Concrete.reachableCircuits finFunctionFinEquiv θ`, in the
(finite-dimensional product) topology on `Matrix (Fin 2ⁿ⁺¹) (Fin 2ⁿ⁺¹) ℂ`. Its register-level
counterpart, the submonoid `reachableCircuitEvolutions n θ` of `Evolution (qudit 2ⁿ⁺¹)`
(`AxQM/Postulates/API/FourGateReachableCircuit.lean`), was identified operator-by-operator with
the reachable circuit matrices (`exists_reachableCircuitEvolution_op_eq`: every reachable circuit
matrix is the operator of a member of the register submonoid).

This file **transports the matrix density onto the register `Evolution` operators**: it pushes the
matrix density statement through the continuous `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`, so
that up to a global phase every unitary operator `Matrix.toEuclideanCLM U` is a limit of the
*operators* `E.op` of the register circuit submonoid `reachableCircuitEvolutions n θ`.

## What is formalised

* `exists_phase_smul_op_mem_closure_op_reachableCircuitEvolutions` — **the operator-level density**:
  for `cos θ = 3/5` and any `U ∈ U(2ⁿ⁺¹)`, some global phase `e^{iα}` makes
  `e^{iα} • Matrix.toEuclideanCLM U` lie in the closure of the operator image
  `(·.op) '' reachableCircuitEvolutions n θ`:

    `e^{iα} • Matrix.toEuclideanCLM U ∈ closure ((·.op) '' ↑(reachableCircuitEvolutions n θ))`.

  The transport is by three moves: (1) the matrix density
  `Concrete.exists_phase_smul_mem_closure_reachableCircuits` supplies the phase `α` and the matrix
  membership `e^{iα} • U ∈ closure (reachableCircuits finFunctionFinEquiv θ)`; (2)
  `Matrix.toEuclideanCLM` is **continuous** (`Matrix.continuous_toEuclideanCLM`, in `ToMathlib/` — a
  `ℂ`-linear map between finite-dimensional spaces) — so it carries closure into
  closure (`image_closure_subset_closure_image`), and being `ℂ`-linear it commutes with the phase
  (`map_smul`), landing `e^{iα} • Matrix.toEuclideanCLM U` in the closure of the *matrix* image
  `Matrix.toEuclideanCLM '' reachableCircuits`; (3) that image sits inside the operator image of the
  register submonoid, because every reachable circuit matrix is `E.op` for some
  `E ∈ reachableCircuitEvolutions n θ` (`exists_reachableCircuitEvolution_op_eq`), so `closure_mono`
  finishes.

This is the density half of the four-gate bridge. The register submonoid members it produces are, by
the whole-submonoid register lift `congr_quditPowTower_mem_reachableTowerCircuitEvolutions`
(`AxQM/Core/FourGateReachableCircuitTower.lean`), grounded `H, S, CNOT, Toffoli` circuits on the
control tower; transporting this operator density along that lift gives the density of the grounded
tower gate submonoid.

The statement is in terms of the reachable circuit matrices (`Concrete.reachableCircuits`) via
`Matrix.toEuclideanCLM`, and `Evolution.op`. It consumes the register submonoid and the
matrix→operator bridge of `AxQM/Postulates/API/FourGateReachableCircuit.lean`.
-/

open Matrix

namespace AxQM

noncomputable section

/-- **The register circuit `Evolution` operators are dense up to a global phase.** For the
reachability angle `θ` (`cos θ = 3/5`) and any unitary `U ∈ U(2ⁿ⁺¹)`, some global phase `e^{iα}`
makes `e^{iα} • Matrix.toEuclideanCLM U` a limit of the operators of the register circuit submonoid
`reachableCircuitEvolutions n θ`:

  `e^{iα} • Matrix.toEuclideanCLM U ∈ closure ((·.op) '' ↑(reachableCircuitEvolutions n θ))`.

The matrix density `Concrete.exists_phase_smul_mem_closure_reachableCircuits` (at the register
encoding `finFunctionFinEquiv`, whose nontriviality holds since the register has `n+1 ≥ 1` qubits)
supplies `α` with `e^{iα} • U ∈ closure (reachableCircuits finFunctionFinEquiv θ)`. Pushing this
through the continuous `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`
(`Matrix.continuous_toEuclideanCLM`, `image_closure_subset_closure_image`) — which, being
`ℂ`-linear, commutes with the phase (`map_smul`) — lands `e^{iα} • Matrix.toEuclideanCLM U` in the
closure of the matrix image `Matrix.toEuclideanCLM '' reachableCircuits`. Finally every reachable
circuit matrix is the operator of a member of the register submonoid
(`exists_reachableCircuitEvolution_op_eq`), so that image lies inside the operator image of
`reachableCircuitEvolutions n θ` and `closure_mono` concludes.

The register submonoid members produced here are, by the whole-submonoid register lift
`congr_quditPowTower_mem_reachableTowerCircuitEvolutions`, grounded `H, S, CNOT, Toffoli` circuits
on the control tower — the density this bridge promotes onto the grounded four-gate gate set. -/
theorem exists_phase_smul_op_mem_closure_op_reachableCircuitEvolutions
    {n : ℕ} {θ : ℝ} (hθ : Real.cos θ = 3 / 5)
    {U : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ (n + 1))) ℂ) :
    ∃ α : ℝ, Complex.exp ((α : ℂ) * Complex.I) • Matrix.toEuclideanCLM (𝕜 := ℂ) U ∈
      closure ((fun E : Evolution (qudit (2 ^ (n + 1))) => E.op) ''
        (reachableCircuitEvolutions n θ : Set (Evolution (qudit (2 ^ (n + 1)))))) := by
  have : Nontrivial (Fin (n + 1) → Fin 2) := Function.nontrivial
  obtain ⟨α, hα⟩ :=
    Concrete.exists_phase_smul_mem_closure_reachableCircuits hθ finFunctionFinEquiv hU
  refine ⟨α, ?_⟩
  -- Transport the matrix membership through the continuous map `Matrix.toEuclideanCLM`.
  have h1 := image_closure_subset_closure_image
    (Matrix.continuous_toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ (n + 1))))
    (Set.mem_image_of_mem (fun M => Matrix.toEuclideanCLM (𝕜 := ℂ) M) hα)
  -- `toEuclideanCLM` is `ℂ`-linear, so it commutes with the global phase.
  simp only [map_smul] at h1
  -- Every reachable circuit matrix is the operator of a register-submonoid member.
  refine closure_mono ?_ h1
  rintro _ ⟨M, hM, rfl⟩
  exact exists_reachableCircuitEvolution_op_eq hM

end

end AxQM
