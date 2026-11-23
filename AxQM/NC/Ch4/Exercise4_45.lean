/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Sqrt2IntegerMatrix
import AxQM.Concrete.Sqrt2CyclotomicMatrix

/-!
# Nielsen & Chuang, Exercise 4.45 (`2⁻ᵏ⸍² M` form of `{H, S, CNOT, Toffoli}` / `T` circuits)

*(N&C p. 198.)*

Show U from H,S,CNOT,Toffoli has form 2^{-k/2}M with integer entries; T-gate variant.

## The statement

Since the library has no gate-set / circuit datatype, a circuit's unitary is literally a product of
gate matrices, and a gate acting on chosen wires is a Kronecker embedding of a small gate into the
`n`-qubit register. The exercise is therefore an **algebraic closure** statement: the matrices of
the form `2⁻ᵏ⸍² M` (single common scale `k`, `M` over a fixed entry subring `R ⊆ ℂ`) are closed
under matrix product (circuit composition) and Kronecker product (wire embedding), the identity has
this form, and each generating gate has it — so any circuit unitary does.

## The formalisation

**The reusable engine and the `H, S, CNOT, Toffoli` (Gaussian) variant** —
`AxQM/Concrete/Sqrt2IntegerMatrix.lean`:

* `AxQM.Concrete.IsSqrt2ScaledIn R U` — the predicate `∃ k, ∃ M over R, U = (√2)⁻ᵏ • M`,
  i.e. N&C's `2⁻ᵏ⸍² M` (`sqrt_two_inv_pow_eq_rpow` identifies `(√2)⁻ᵏ = 2⁻ᵏ⸍²`).
* Its closure lemmas `IsSqrt2ScaledIn.mul` / `.kron` / `.submatrix`, packaged as the submonoid
  `sqrt2ScaledMatrixSubmonoid` and circuit statement `isSqrt2ScaledIn_list_prod` (a whole circuit
  — a product of embedded gates — is `√2`-scaled).
* The Gaussian ring `gaussianIntSubring = ℤ[i] = {a + b·i : a, b ∈ ℤ}` (N&C's "complex integers")
  and the gate memberships `isSqrt2ScaledIn_hadamardC` (`k = 1`), `isSqrt2ScaledIn_sMatrix`,
  `isSqrt2ScaledIn_cnotMatrix`, `isSqrt2ScaledIn_toffoliMatrix` (`k = 0`).
* Main results `exists_two_pow_neg_half_smul_gaussian` and `exists_circuit_form_gaussian`, giving
  N&C's
  explicit `2⁻ᵏ⸍² • M` form with `M` certified `∃ a b : ℤ, M i j = a + b·i`.

**The `T`-gate variant and the refutation of the literal reading** —
`AxQM/Concrete/Sqrt2CyclotomicMatrix.lean`:

* `AxQM.Concrete.not_isSqrt2ScaledIn_gaussian_tMatrix` — **the fidelity point**: taken
  verbatim (`M` over `ℤ[i]`), the `T`-variant is *false* for `T = diag(1, e^{iπ/4})`; the two
  diagonal entries force `√2` to be rational, contradicting `irrational_sqrt_two`. N&C's exercise is
  refuted rather than silently repaired.
* `AxQM.Concrete.cyclotomicIntSubring = ℤ[ζ₈]` (`ζ₈ = e^{iπ/4}`, `zeta8`), the entry
  ring, with `zeta8_sq : ζ₈² = i`, the explicit-basis `mem_cyclotomicIntSubring_iff`
  (`a + b·ζ₈ + c·ζ₈² + d·ζ₈³`), and `gaussianIntSubring_le_cyclotomicIntSubring` (`ℤ[i] ⊆ ℤ[ζ₈]`).
* The gate memberships `isSqrt2Cyclotomic_hadamardC` / `_sMatrix` / `_cnotMatrix` / `_tMatrix`
  (and `_toffoliMatrix`), and the main results `exists_two_pow_neg_half_smul_cyclotomic` /
  `exists_circuit_form_cyclotomic`: any `{H, S, CNOT, T}` circuit unitary is `2⁻ᵏ⸍² M` with
  `M ∈ ℤ[ζ₈]`.

## Faithfulness

The theorems range over an arbitrary finite index type (containing `Fin (2ⁿ)`), so specialising to
a `2ⁿ`-dimensional register is not a weakening; `k` is a genuine natural number and `M` a genuine
matrix over the named ring. The single-global-scalar predicate captures "`2⁻ᵏ⸍² M`, one common `k`"
exactly — strictly stronger than "entries in `ℤ[i][1/√2]`" (e.g. `1 + 1/√2` lies in that subring but
is not `2⁻ᵏ⸍²·Gaussian`). The `T`-variant is handled honestly on both sides: the literal `ℤ[i]`
reading is refuted, and the true statement over `ℤ[ζ₈]` is proved.
-/
