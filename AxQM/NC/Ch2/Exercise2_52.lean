/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HadamardGate

/-!
# Nielsen & Chuang, Exercise 2.52

Verify H^2 = I.

In Section 2.2.2 the Hadamard gate is a closed-system evolution of a
single qubit (Postulate 2), so its square is again such an evolution and the identity `H² = I`
means: **applying `H` twice is the do-nothing gate.** The faithful physics statement is therefore
the involution of the *gate object* — `hadamardGate ^ 2 = 1` in the evolution monoid `Evolution
qubit` (with `1 = Evolution.id` the identity gate) — rather than the bare matrix identity.

## The formalisation

* `AxQM.hadamardGate_sq` — **the exercise:** `hadamardGate ^ 2 = 1`, i.e. `H² = I` at the
  level of the gate as an `Evolution qubit`.
* `AxQM.hadamardGate_evolvePure_involutive` — the physical reading: the gate's action on
  pure states, `ψ ↦ H ψ`, is an involution (`H (H ψ) = ψ`), so `H` is its own inverse.

## Design notes

* **Gate level, not matrix level.** The Hadamard gate is `hadamardGate : Evolution qubit` (built in
  `AxQM/Postulates/API/HadamardGate.lean` for Exercise 2.51). `H² = I` is read as
  `hadamardGate ^ 2 = 1`, whereas the underlying matrix identity `Concrete.hadamardC_mul_self`
  (`H * H = 1`) is the fact that Exercise 2.51 already established in `AxQM/Concrete/Hadamard.lean`.
  The proof applies that fact through the gate.
* **Proof.** `Evolution` is a monoid under `comp`, so `^ 2 = 1` reduces (`Evolution.ext`) to the
  operator identity `H.op ∘ H.op = 1`; the `⋆`-algebra bridge `Matrix.toEuclideanCLM`
  (`hadamardGate_op`, `map_mul`, `map_one`) transports `Concrete.hadamardC_mul_self` to close it —
  no operator-level entrywise computation. The pure-state corollary then follows from
  `Evolution.evolvePure_comp` and `hadamardGate_sq`.
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.52: `H² = I`.** The Hadamard gate `hadamardGate : Evolution
qubit` squares to the identity evolution in the gate monoid: `hadamardGate ^ 2 = 1`. Reducing
(`Evolution.ext`) to the operator identity `H.op ∘ H.op = 1` and transporting the matrix involution
`Concrete.hadamardC_mul_self` (`H * H = 1`) across the `⋆`-algebra isomorphism
`Matrix.toEuclideanCLM` (`map_mul`/`map_one`) closes it. -/
theorem hadamardGate_sq : hadamardGate ^ 2 = 1 := by
  rw [sq, Evolution.mul_def]
  apply Evolution.ext
  -- Reduce to the operator identity `H.op ∘ H.op = 1` (defeq to the `.op` goal via
  -- `comp_op`, `hadamardGate_op`, `id_op`), then transport `hadamardC_mul_self`.
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC).comp
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC) = 1
  rw [← ContinuousLinearMap.mul_def, ← map_mul, Concrete.hadamardC_mul_self, map_one]

/-- The Hadamard gate is its own inverse: its action on pure states `ψ ↦ H ψ` is an involution,
`hadamardGate (hadamardGate ψ) = ψ`. The physical reading of `H² = I` — applying the Hadamard gate
twice returns any qubit pure state unchanged. Immediate from `hadamardGate_sq` via
`Evolution.evolvePure_comp`. -/
theorem hadamardGate_evolvePure_involutive :
    Function.Involutive hadamardGate.evolvePure := by
  intro ψ
  rw [← Evolution.evolvePure_comp, ← Evolution.mul_def, ← sq, hadamardGate_sq]
  apply PureState.ext
  simp

end AxQM
