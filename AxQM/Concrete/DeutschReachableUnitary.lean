/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DeutschCompressedReachable
import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Concrete: the reachable `G`-placement matrices are unitary (matrix level, N&C Ex 4.44)

Every statement is about matrices — the Deutsch target orbit `deutschTargetOrbit`, its two-control
placements `deutschWirePlacedReachable`, the ancilla-preserving reachable gate set
`deutschAncillaReachableGates` — and the matrix unitary group `Matrix.unitaryGroup`.

## Unitarity of the reachable gates

The `Evolution`-level version of Exercise 4.44 (`Postulates/API/DeutschReachableEvolutions.lean`)
promotes each reachable full-register matrix `N ∈ deutschAncillaReachableCircuits` to a
closed-system `Evolution` `quditGate hN` of `qudit D`. The promotion `quditGate` consumes a
*unitarity witness* `hN : N ∈ Matrix.unitaryGroup (Fin D) ℂ`; this file supplies it.

The chain is elementary:

* `deutschTargetOrbit_subset_unitaryGroup` — each orbit element `iⁿ · R_x(nπα)` is a modulus-one
  scalar `iⁿ` (`iⁿ · star(iⁿ) = (i · star i)ⁿ = 1`) times the unitary `R_x(nπα)`, hence unitary.
* `deutschWirePlacedReachable_subset_unitaryGroup` — placing a unitary two-control gate keeps it
  unitary (`mcCtrlSingleQubit_mem_unitaryGroup`).
* `deutschAncillaReachableGates_subset_unitaryGroup` — a gate is a **topological limit** of such
  placements (the phase gate `S` is reachable only as a limit; hence the closure in
  `deutschAncillaReachableGates`), and the unitary group is closed (`isClosed_unitary`), so the
  limit is again unitary.

`deutschAncillaReachableGates` is the generating set of the circuit submonoid
`deutschAncillaReachableCircuits`, so `Submonoid.closure_induction` promotes the gate unitarity to
every reachable circuit in the `Evolution` op-identification.

This certifies that the gate set of `DeutschCompressedReachable` is unitary.
-/

namespace AxQM.Concrete

open Matrix

/-- **The Deutsch target orbit consists of unitary matrices.** Each element
`iⁿ · R_x(nπα)` (`n : ℤ`) of `deutschTargetOrbit α` is the modulus-one scalar `iⁿ`
(`iⁿ · star(iⁿ) = (i · star i)ⁿ = 1ⁿ = 1`, so `iⁿ ∈ unitary ℂ`) times the unitary rotation
`R_x(nπα)`, hence unitary by `Unitary.smul_mem_of_mem`. -/
theorem deutschTargetOrbit_subset_unitaryGroup (α : ℝ) :
    deutschTargetOrbit α ⊆ (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  rintro g ⟨n, rfl⟩
  refine Unitary.smul_mem_of_mem (Unitary.mem_iff.mpr ?_) (rotX_mem_unitaryGroup _)
  constructor <;> simp [star_zpow₀, ← mul_zpow, Complex.I_mul_I, mul_comm]

/-- **The placed Deutsch iterates are unitary.** A member of `deutschWirePlacedReachable enc a b j`
is `mcCtrlSingleQubit enc {a, b} j g` for an orbit element `g` (unitary by
`deutschTargetOrbit_subset_unitaryGroup`), and placing a unitary two-control block keeps it unitary
(`mcCtrlSingleQubit_mem_unitaryGroup`). -/
theorem deutschWirePlacedReachable_subset_unitaryGroup {m d : ℕ} (enc : (Fin m → Fin 2) ≃ Fin d)
    (a b j : Fin m) (α : ℝ) :
    deutschWirePlacedReachable enc a b j α ⊆
      (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) := by
  rintro P ⟨g, hg, rfl⟩
  exact mcCtrlSingleQubit_mem_unitaryGroup enc {a, b} j
    (deutschTargetOrbit_subset_unitaryGroup α hg)

/-- **The reachable ancilla-preserving gates are unitary.** A gate in
`deutschAncillaReachableGates`
is a topological limit of placed Deutsch iterates (`N ∈ closure (deutschWirePlacedReachable …)`; the
closure is needed because the phase gate `S` is reachable only as a limit). Each iterate is unitary
(`deutschWirePlacedReachable_subset_unitaryGroup`) and the unitary group is closed
(`isClosed_unitary`), so the limit is unitary too. -/
theorem deutschAncillaReachableGates_subset_unitaryGroup {M m n D d : ℕ}
    (fullEnc : (Fin M → Fin 2) ≃ Fin D) (dataEnc : (Fin m → Fin 2) ≃ Fin d)
    (e : Fin M ≃ Fin m ⊕ Fin n) (α : ℝ) :
    deutschAncillaReachableGates fullEnc dataEnc e α ⊆
      (Matrix.unitaryGroup (Fin D) ℂ : Set (Matrix (Fin D) (Fin D) ℂ)) := by
  rintro N ⟨-, a, b, j, hNmem⟩
  have := closure_mono (deutschWirePlacedReachable_subset_unitaryGroup fullEnc a b j α) hNmem
  rwa [isClosed_unitary.closure_eq] at this

end AxQM.Concrete
