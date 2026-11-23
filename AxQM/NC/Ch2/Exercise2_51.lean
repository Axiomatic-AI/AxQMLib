/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HadamardGate

/-!
# Nielsen & Chuang, Exercise 2.51

Verify the Hadamard gate H is unitary.

The Hadamard gate is introduced (Section 2.2.2) as an example of a *unitary operator* on a
single qubit — a legitimate closed-system evolution under Postulate 2. A value of type
`Evolution qubit` cannot be formed without discharging the unitarity obligation
`op ∈ unitary (…)`. The formalisation is the Hadamard **gate object** together with its
matrix-level unitarity.

## The formalisation

* `AxQM.hadamardGate` (in `AxQM/Postulates/API/HadamardGate.lean`) — the
  **Hadamard gate as an `Evolution qubit`**. Constructing it discharges the `Evolution` unitarity
  obligation `hadamardGate.op ∈ unitary (…)`, so its mere well-formedness *is* the verification
  that `H` is unitary. `AxQM.hadamardGate_op` exposes its operator
  `= Matrix.toEuclideanCLM Concrete.hadamardC`.
* `AxQM.Concrete.hadamardC_mem_unitaryGroup` (in `AxQM/Concrete/Hadamard.lean`)
  — the underlying matrix fact `H ∈ Matrix.unitaryGroup (Fin 2) ℂ`, i.e. `Hᴴ H = I` (N&C's
  definition of unitary), from `hadamardC_isHermitian` and the involution `hadamardC_mul_self`
  (`H² = I`) via `Matrix.IsHermitian.mem_unitaryGroup`. This is the fact transported through the
  `⋆`-algebra bridge `Matrix.toEuclideanCLM` to build `hadamardGate`.

The gate object and its `_op` bridge are used by the other N&C items about the Hadamard gate — the
involution `H² = I` (Exercise 2.52) and its eigenvalues/eigenvectors (Exercise 2.53).
-/
