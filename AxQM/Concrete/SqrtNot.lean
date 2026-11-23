/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli

/-!
# Concrete: the `√NOT` gate — Barenco's `V` (with `V² = X`) for the tight-register `Cⁿ(X)`

This file introduces the **square-root-of-`NOT`** gate

`√X = V = ½ !![1 + i, 1 − i; 1 − i, 1 + i]`,

a fixed `2 × 2` unitary with `V² = X` (the Pauli/`NOT` gate). It is the elementary building block
of Nielsen & Chuang's *no-work-qubit* multiply-controlled-`NOT` construction (Exercise 4.30 /
Barenco *et al.* Lemma 7.5): a `Cⁿ(X)` on a **tight** register of exactly `n + 1` qubits (`n`
controls, one target, no spare/work wire) is reduced using controlled-`V`/controlled-`V†` gates
together with two smaller `Cⁿ⁻¹(X)` gates.

## Why a genuine single-qubit gate is unavoidable here (parity)

On a tight `n + 1`-wire register (`n ≥ 3`), `Cⁿ(X)` — with control set *all* `n` other wires and a
single target — is, as a permutation of the `2^{n+1}` computational basis states, a **single
transposition** (it swaps only the two strings with every control set to `1`), hence an **odd**
permutation. Every gate with at most two controls (`Toffoli`, `CNOT`, `NOT`) on `≥ 4` wires is, by
contrast, an **even** permutation (it swaps `2^{k}` disjoint pairs with `k ≥ 1`). A product of even
permutations is even, so `Cⁿ(X)` on the tight register is **provably not** a product of
`Toffoli`/`CNOT`/`NOT` *permutation* gates: N&C's "single-qubit gates" in Exercise 4.29 are
essential and cannot be replaced by classical `NOT`s. `√X` is the non-permutation single-qubit gate
that resolves the parity obstruction — its off-diagonal-plus-diagonal complex entries make it a true
unitary rotation, not a basis permutation.

This is the matrix-level counterpart of the Evolution-level `sqrtChain`/`barencoNCircuit`
development (`AxQM.cnx_eq_barencoNCircuit`); the `Cⁿ(X)` reduction driving Exercise 4.43
runs on the encoded-basis matrix gates (`ctrlSingleQubit enc`, `singleQubitOnWire enc`), so it needs
a *matrix* `√X`.

Everything here is pure `2 × 2` complex-matrix algebra. The proofs mirror
`AxQM/Concrete/Pauli.lean`: reduce to the closed `!!`-form and compute entrywise.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The **`√NOT` gate** `V = ½ !![1 + i, 1 − i; 1 − i, 1 + i]`, a fixed square root of the Pauli
`X`/`NOT` gate (`V² = X`, `sqrtNot_mul_self`). It is unitary but *not* Hermitian and *not* a
permutation matrix; it is Barenco's `V` for the tight-register `Cⁿ(X)` reduction (Exercise 4.30). -/
noncomputable def sqrtNot : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 + I) / 2, (1 - I) / 2; (1 - I) / 2, (1 + I) / 2]

/-- **The defining Barenco property**: `V² = X`. The diagonal entries are
`((1 ± i)/2)² + ((1 ∓ i)/2)² = i/2 − i/2 = 0` and the off-diagonal entries are
`2 · (1 + i)(1 − i)/4 = 1`, so `V · V = !![0, 1; 1, 0] = X`. -/
theorem sqrtNot_mul_self : sqrtNot * sqrtNot = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sqrtNot, pauliX, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;> norm_num

/-- The conjugate transpose of `V` in closed form: `Vᴴ = ½ !![1 − i, 1 + i; 1 + i, 1 − i]`. Since
`V` is symmetric, `Vᴴ` is its entrywise complex conjugate. -/
theorem sqrtNot_conjTranspose :
    sqrtNotᴴ = !![(1 - I) / 2, (1 + I) / 2; (1 + I) / 2, (1 - I) / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sqrtNot, Matrix.conjTranspose_apply, Complex.ext_iff]

/-- `V` is unitary: `Vᴴ V = I`. With `Vᴴ = ½ !![1 − i, 1 + i; 1 + i, 1 − i]`, each diagonal entry of
`Vᴴ V` is `2 · (1 + i)(1 − i)/4 = 1` and each off-diagonal entry is
`((1 ∓ i)² + (1 ± i)²)/4 = 0`. -/
theorem sqrtNot_conjTranspose_mul_self : sqrtNotᴴ * sqrtNot = 1 := by
  rw [sqrtNot_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sqrtNot, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;> norm_num

/-- `V` is unitary: `V Vᴴ = I` (companion of `sqrtNot_conjTranspose_mul_self`, flipped through
`mul_eq_one_comm` rather than recomputed). -/
theorem sqrtNot_mul_conjTranspose : sqrtNot * sqrtNotᴴ = 1 :=
  mul_eq_one_comm.mpr sqrtNot_conjTranspose_mul_self

/-- **`V` is unitary** (`V ∈ Matrix.unitaryGroup`), so the `√NOT` gate is a legitimate single-qubit
gate — the target family the tight-register `Cⁿ(X)` reduction places on individual wires. -/
theorem sqrtNot_mem_unitaryGroup : sqrtNot ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (by
    rw [Matrix.star_eq_conjTranspose]; exact sqrtNot_conjTranspose_mul_self)

/-- **`Vᴴ` is unitary** (`Vᴴ ∈ Matrix.unitaryGroup`) — the adjoint of a unitary is unitary. Since
`Matrix.unitaryGroup` is `unitary (Matrix …)` and `Vᴴ = star V`, this is the general structural
`Unitary.star_mem` applied to `sqrtNot_mem_unitaryGroup`. The controlled-`V†` factor of the Barenco
tight-register `Cⁿ(X)` recursion is therefore a legitimate single-qubit gate. -/
theorem sqrtNot_conjTranspose_mem_unitaryGroup : sqrtNotᴴ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Unitary.star_mem sqrtNot_mem_unitaryGroup

/-- `Vᴴ` is also a square root of `X`: `(Vᴴ)² = X`. Indeed `(Vᴴ)² = (V²)ᴴ = Xᴴ = X`, since `X` is
Hermitian; it is the controlled-`V†` factor of the Barenco reduction. -/
theorem sqrtNot_conjTranspose_mul_self_eq_pauliX : sqrtNotᴴ * sqrtNotᴴ = pauliX := by
  rw [← Matrix.conjTranspose_mul, sqrtNot_mul_self]; exact pauliX_isHermitian

end AxQM.Concrete
