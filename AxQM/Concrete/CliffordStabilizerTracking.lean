/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCliffordCircuit
import AxQM.Concrete.StabilizerCodeDimension

/-!
# Concrete: Clifford stabilizer tracking — N&C §10.5.2, Eq. (10.87) for Clifford circuits

The **correctness of the "keep track of the generators" simulation** for the unitary part of the
Gottesman–Knill theorem (Nielsen & Chuang Theorem 10.7, §10.5.2, p. 459).

N&C's Eq. (10.87) observes that if `|ψ⟩` lies in the stabilized subspace `V_S` (`g|ψ⟩ = |ψ⟩` for a
generator `g`) and a unitary `U` is applied, then `U|ψ⟩` is stabilized by `U g U†`: "so to compute
the change in the stabilizer we need only compute how it affects the generators". For a **Clifford
circuit** `U`, the backbone `CliffordCircuit.conj_pauliString` computes that conjugate
*classically*, `U · P_g · U† = U.sign g • P_{U.act g}` — the updated generator is again a (signed)
Pauli string, whose check-matrix row `U.act g` and `±1` sign `U.sign g` are read off by the composed
column operations. That is an identity of **operators**; this file closes the loop to the **state**,
proving the classically-updated generator really does fix the evolved vector `U ·ᵥ v`.

* `conj_mulVec_toMatrix_mulVec` — the general unitary step (Eq. 10.87, matrix form): for any unitary
  `U` (`U · Uᴴ = 1`) and any `P` fixing `v`, the conjugate `U · P · Uᴴ` fixes `U ·ᵥ v`.
* `CliffordCircuit.updatedGenerator_mulVec_toMatrix_mulVec` — the Clifford instance for a single
  generator: `P_g ·ᵥ v = v ⟹ (U.sign g • P_{U.act g}) ·ᵥ (U ·ᵥ v) = U ·ᵥ v`.
* `CliffordCircuit.updatedGenerator_mulVec_toMatrix_mulVec_of_mem` — the whole generator family of a
  stabilized subspace `V_S` is carried through: every classically-updated signed generator
  `U.sign (g i) • P_{U.act (g i)}` fixes the evolved vector `U ·ᵥ v`.

This is the precise sense in which "the classical computer performs the simulation … simply to keep
track of the generators of the stabilizer" (N&C §10.5.4) is **correct** for the Clifford operations:
the tracked list of check-matrix rows and signs `(U.act (g i), U.sign (g i))ᵢ` is a genuine
stabilizer description of the evolved state.
-/

open scoped Matrix

namespace AxQM.Concrete

variable {n m : ℕ}

/-- **N&C Eq. (10.87), matrix form — the general unitary step.** If `P` fixes `v` (`P ·ᵥ v = v`) and
`U` is unitary (`U · Uᴴ = 1`), then the conjugate `U · P · Uᴴ` fixes the evolved vector `U ·ᵥ v`:
`(U · P · Uᴴ) ·ᵥ (U ·ᵥ v) = U ·ᵥ v`. This is the linear-algebra content of "the state `U|ψ⟩` is
stabilized by `U g U†`". Proof: slide the outer `Uᴴ` against the `U` in `U ·ᵥ v` using `Uᴴ · U = 1`
(the two-sided inverse of a square unitary, `Matrix.mul_eq_one_comm`), then apply `P ·ᵥ v = v`. -/
theorem conj_mulVec_toMatrix_mulVec
    {U P : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ} (hU : U * Uᴴ = 1)
    {v : (Fin n → Fin 2) → ℂ} (hv : P.mulVec v = v) :
    (U * P * Uᴴ).mulVec (U.mulVec v) = U.mulVec v := by
  have hUadjU : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hUadjU, Matrix.mul_one,
    ← Matrix.mulVec_mulVec, hv]

namespace CliffordCircuit

/-- **Gottesman–Knill, Clifford tracking (single generator).** If the phase-free Pauli string `P_g`
fixes `v` (`P_g ·ᵥ v = v` — `g` is a stabilizer generator of `v`), then the **classically-updated**
generator `U.sign g • P_{U.act g}` — the check-matrix row `U.act g` with sign `U.sign g` produced by
the Clifford circuit `U` — fixes the evolved vector `U ·ᵥ v`. Immediate from
`CliffordCircuit.conj_pauliString` (which identifies `U.sign g • P_{U.act g}` with `U · P_g · Uᴴ`)
and `conj_mulVec_toMatrix_mulVec` (Eq. 10.87, using unitarity `U · Uᴴ = 1`). -/
theorem updatedGenerator_mulVec_toMatrix_mulVec (U : CliffordCircuit n) (g : Fin n → Fin 4)
    {v : (Fin n → Fin 2) → ℂ} (hv : (pauliString g).mulVec v = v) :
    (U.sign g • pauliString (U.act g)).mulVec (U.toMatrix.mulVec v) = U.toMatrix.mulVec v := by
  rw [← U.conj_pauliString g]
  exact conj_mulVec_toMatrix_mulVec U.mul_conjTranspose hv

/-- **Gottesman–Knill, Clifford tracking (the whole stabilizer).** If `v` lies in the stabilized
subspace `V_S = ⟨g₀, …, g_{m-1}⟩`, then for every generator index `i` the classically-updated signed
generator `U.sign (g i) • P_{U.act (g i)}` fixes the evolved vector `U ·ᵥ v`. So the tracked
description `(U.act (g i), U.sign (g i))ᵢ` is a genuine stabilizer of `U ·ᵥ v`: the Clifford circuit
`U` maps `V_S` into the subspace stabilized by the updated generators. Per-generator instance of
`updatedGenerator_mulVec_toMatrix_mulVec` via `mem_stabilizedSubspace`. -/
theorem updatedGenerator_mulVec_toMatrix_mulVec_of_mem (U : CliffordCircuit n)
    {g : Fin m → Fin n → Fin 4} {v : (Fin n → Fin 2) → ℂ}
    (hv : v ∈ stabilizedSubspace g) (i : Fin m) :
    (U.sign (g i) • pauliString (U.act (g i))).mulVec (U.toMatrix.mulVec v) = U.toMatrix.mulVec v :=
  updatedGenerator_mulVec_toMatrix_mulVec U (g i) (mem_stabilizedSubspace.mp hv i)

end CliffordCircuit

end AxQM.Concrete
