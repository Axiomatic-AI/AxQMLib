/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliExpansion
import AxQM.Postulates.API.TrotterProduct
import AxQM.Postulates.API.HamiltonianGenerator
import ToMathlib.Analysis.CStarAlgebra.Matrix

/-!
# AxQM.Postulates.API — the literal Pauli-string Trotter approximation (N&C Problem 4.3)

This file joins the two independent halves of Nielsen & Chuang, Problem 4.3 that had been
formalised separately — the **Pauli expansion** of the generator (part (2)) and the **Trotter
product formula** for propagators (parts (4)/(5)) — into N&C's *literal* statement, in which the
approximating product runs over the `4ⁿ` Pauli strings:

* **(4)** `exp(-i H Δ) = ∏_g exp(-i h_g g Δ) + O(Δ²)`;
* **(5)** `U = [∏_g exp(-i h_g g Δ)]ᵏ + O(1/k)` for `Δ = 1/k`.

Here `H = Σ_g h_g g` is the Pauli expansion of a Hamiltonian on the `n`-qubit register
`qudit (2ⁿ)`, `g` ranges over the Pauli strings `Fin n → Fin 4` (a choice of `{I, X, Y, Z}` per
qubit), and each `exp(-i h_g g Δ)` is the propagator of the Pauli-string Hamiltonian `h_g · g`.

The general Trotter bounds in `Postulates/API/TrotterProduct.lean`
(`Observable.exists_norm_prod_propagator_op_sub_propagator_op_le` and its `k`-fold power version)
already prove (4)/(5) for an *arbitrary* ordered decomposition `H = Σᵢ Hᵢ` of a Hamiltonian into
Hamiltonians. This file supplies the missing specialisation — the operator↔matrix transport that
turns N&C's `H = Σ_g h_g g` into such a decomposition — so those bounds fire on the literal
Pauli-string list.

## What this file provides

* `Observable.toEuclideanCLM_stdMatrix` — the **reverse bridge**: `Matrix.toEuclideanCLM H.stdMatrix
  = H.op`. It recovers an observable's operator from its computational-basis matrix
  (`Observable.stdMatrix`, the forward bridge of `PauliExpansion.lean`), by the round trip
  `toLin ∘ toMatrix = id` in an orthonormal basis. This is the operator↔matrix
  transport described above.
* `pauliStringHamiltonian g c` — the **Pauli-string Hamiltonian** `c · g` on `qudit (2ⁿ)`: the
  real-scaled Pauli string `Concrete.pauliStringStd g` promoted to a self-adjoint operator through
  `Matrix.toEuclideanCLM` (self-adjoint because the string is Hermitian and `c` is real). Its
  propagator `(pauliStringHamiltonian g (h g)).propagator 1 0 Δ` is exactly N&C's
  `exp(-i h_g g Δ)`.
* `Observable.op_eq_sum_pauliStringHamiltonian` — **part (2), operator form**: every Hamiltonian on
  the `n`-qubit register is the sum `H.op = Σ_g (pauliStringHamiltonian g (h g)).op` of its
  Pauli-string Hamiltonians, for real `h_g`. This is exactly the ordered decomposition the Trotter
  bounds consume.
* `Observable.exists_norm_prod_pauliStringHamiltonian_propagator_sub_le` — **part (4)**, literal
  form: `‖(∏_g exp(-i h_g g Δ)) - exp(-i H Δ)‖ ≤ C·Δ²`.
* `Observable.exists_norm_prod_pauliStringHamiltonian_propagator_pow_sub_le` — **part (5)**, literal
  form: `‖(∏_g exp(-i h_g g /k))ᵏ - exp(-i H)‖ ≤ C/k`.
* `Evolution.exists_pauliString_trotter_approximation` — the conclusion of Problem 4.3: *every*
  `n`-qubit unitary `U` is approximated to `O(1/k)` by the `k`-fold Pauli–Trotter product
  `[∏_g exp(-i h_g g /k)]ᵏ`. Combining parts (1) (`U = exp(-iH)` for a Hermitian `H`), (2)
  (`H = Σ_g h_g g`) and (5).

## Design notes

* **What is new versus the general bounds.** N&C's parts (4)/(5) are already captured, more
  generally, by the arbitrary-decomposition bounds in `TrotterProduct.lean`; the physics content
  (Trotterising a Hamiltonian sum) is identical. What is proved here in addition
  is that N&C's *specific* decomposition into Pauli strings *is* such a sum, i.e. the transport of
  the matrix-level Pauli expansion (`Observable.exists_real_pauliString_expansion`) into an equality
  of operators `H.op = Σ_g (h_g · g).op`. The `4ⁿ` term count of N&C's `O(4ⁿ Δ²)`/`O(4ⁿ Δ)` is
  absorbed into the constant `C`, as in the general bounds.
* **The ordering.** N&C fix "any ordering" of the Pauli strings; here the ordering is
  `Finset.univ.toList` over `Fin n → Fin 4` (all `4ⁿ` strings). The bound holds for that fixed
  ordering — the physical content is order-independent (the constant `C` may depend on it).
* **The register↔matrix transport.** An observable's operator lives on `EuclideanSpace ℂ (Fin 2ⁿ)`,
  its `stdMatrix` on `Fin 2ⁿ`, and the Pauli-string mathematics on bit strings `Fin n → Fin 2`.
  `Observable.toEuclideanCLM_stdMatrix` bridges operator↔matrix; `Concrete.pauliStringStd` bridges
  the bit-string Pauli string to the flat `Fin 2ⁿ` indexing. The star-algebra isomorphism
  `Matrix.toEuclideanCLM` is `ℂ`-linear and multiplicative, so it carries the matrix sum
  `H.stdMatrix = Σ_g h_g · (pauli string)` to the operator sum verbatim.
-/

open scoped InnerProductSpace

open Matrix

noncomputable section

namespace AxQM

variable {d n : ℕ}

/-- The **reverse computational-basis bridge**: the `Matrix.toEuclideanCLM` image of an observable's
computational-basis matrix recovers its operator, `Matrix.toEuclideanCLM H.stdMatrix = H.op`. This
is the inverse of `Observable.stdMatrix` (the forward operator→matrix bridge of `PauliExpansion`):
`stdMatrix` is `toMatrixOrthonormal` in the orthonormal computational basis and `toEuclideanCLM`
coerces to `toEuclideanLin = toLin` in the same basis, so the two compose to the identity
(`Matrix.toLin_toMatrix`). It is the transport that lets a matrix-level identity about `H.stdMatrix`
be pushed to an operator identity about `H.op`. -/
theorem Observable.toEuclideanCLM_stdMatrix (H : Observable (qudit d)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) H.stdMatrix = H.op := by
  apply ContinuousLinearMap.coe_injective
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Observable.stdMatrix]
  exact Matrix.toLin_toMatrix _ _ _

/-- The **Pauli-string Hamiltonian** `c · g` on the `n`-qubit register `qudit (2ⁿ)`, for a Pauli
string `g : Fin n → Fin 4` and a real coefficient `c`. Its operator is the Hermitian matrix
`c • Concrete.pauliStringStd g` (the standard-indexed Pauli string scaled by `c`) promoted to a
continuous linear map through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`; it is
self-adjoint because the Pauli string is Hermitian and `c` is real (so `(c : ℂ)` is self-adjoint),
and that isomorphism preserves `star`. These are the summands `h_g · g` of the Pauli expansion of a
Hamiltonian, whose ordered propagator product is Trotterised in Nielsen & Chuang,
Problem 4.3(4)/(5). -/
def pauliStringHamiltonian (g : Fin n → Fin 4) (c : ℝ) : Observable (qudit (2 ^ n)) where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)) ((c : ℂ) • Concrete.pauliStringStd g)
  selfAdjoint := by
    have hc : IsSelfAdjoint (c : ℂ) := (Complex.im_eq_zero_iff_isSelfAdjoint ↑c).mp rfl
    exact (hc.smul (Concrete.pauliStringStd_isHermitian g).isSelfAdjoint).map
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)))

/-- The operator of the Pauli-string Hamiltonian `c · g` is `c` times the operator of the Pauli
string: `(pauliStringHamiltonian g c).op = c • Matrix.toEuclideanCLM (Concrete.pauliStringStd g)`.
Immediate from the definition and the `ℂ`-linearity of `Matrix.toEuclideanCLM` (`map_smul`). -/
theorem pauliStringHamiltonian_op (g : Fin n → Fin 4) (c : ℝ) :
    (pauliStringHamiltonian g c).op
      = (c : ℂ) • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n))
          (Concrete.pauliStringStd g) :=
  map_smul _ _ _

/-- **Nielsen & Chuang, Problem 4.3(2), operator form with an explicit coefficient function.** From
a *fixed* real Pauli expansion `H.stdMatrix.submatrix _ _ = ∑_g (h_g : ℂ) • pauliString g` of a
Hamiltonian on the `n`-qubit register, its operator decomposes as the ordered sum of its
Pauli-string Hamiltonians, `H.op = Σ_g (pauliStringHamiltonian g (h g)).op`. This is the
form of `Observable.op_eq_sum_pauliStringHamiltonian`, with the coefficient function `h` and the
expansion `hexp` taken as explicit inputs rather than existentially bound — the form needed
when the *same* `h` is used in two places (e.g. the total Pauli weight
`∑_g |h_g|` of `AxQM/Postulates/API/PauliCoefficientOpNorm.lean`). The proof reindexes the
bit-string Pauli expansion to the flat `Fin (2ⁿ)` register, then transports the matrix identity
through the reverse bridge `Observable.toEuclideanCLM_stdMatrix` and the `ℂ`-linearity of
`Matrix.toEuclideanCLM`. -/
theorem Observable.op_eq_sum_pauliStringHamiltonian_of_expansion (H : Observable (qudit (2 ^ n)))
    {h : (Fin n → Fin 4) → ℝ}
    (hexp : H.stdMatrix.submatrix ⇑finFunctionFinEquiv ⇑finFunctionFinEquiv
      = ∑ g, (h g : ℂ) • Concrete.pauliString g) :
    H.op = ((Finset.univ.toList.map fun g => pauliStringHamiltonian g (h g)).map
      Observable.op).sum := by
  -- Reindex the bit-string Pauli expansion to the flat `Fin (2ⁿ)` register indexing.
  have hstd : H.stdMatrix = ∑ g, (h g : ℂ) • Concrete.pauliStringStd g := by
    ext I J
    have hIJ := congr_fun₂ hexp (finFunctionFinEquiv.symm I) (finFunctionFinEquiv.symm J)
    simpa [Concrete.pauliStringStd, Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
      Equiv.apply_symm_apply] using hIJ
  -- The list sum over `Finset.univ.toList` is the Finset sum over all Pauli strings.
  have hlist : ((Finset.univ.toList.map fun g => pauliStringHamiltonian g (h g)).map
        Observable.op).sum = ∑ g, (pauliStringHamiltonian g (h g)).op := by
    rw [List.map_map, Finset.sum_map_toList]; rfl
  -- Push the matrix identity through `toEuclideanCLM` (linear) to an operator identity.
  rw [hlist, ← Observable.toEuclideanCLM_stdMatrix H, hstd, map_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, pauliStringHamiltonian_op]

/-- **Nielsen & Chuang, Problem 4.3(2), operator form: the Pauli-string decomposition of a
Hamiltonian.** Every Hamiltonian `H : Observable (qudit (2ⁿ))` on the `n`-qubit register is the sum
of its Pauli-string Hamiltonians `h_g · g` with real `h_g`:
`H.op = Σ_g (pauliStringHamiltonian g (h g)).op`, the sum over all `4ⁿ` Pauli strings
`g : Fin n → Fin 4` (written as the list `Finset.univ.toList`). This is the ordered Hamiltonian
decomposition `H = Σᵢ Hᵢ` that the Trotter bounds
(`Observable.exists_norm_prod_propagator_op_sub_propagator_op_le`) consume; it is the
existentially-bound corollary of `Observable.op_eq_sum_pauliStringHamiltonian_of_expansion` applied
to the real Pauli expansion `Observable.exists_real_pauliString_expansion`. -/
theorem Observable.op_eq_sum_pauliStringHamiltonian (H : Observable (qudit (2 ^ n))) :
    ∃ h : (Fin n → Fin 4) → ℝ,
      H.op = ((Finset.univ.toList.map fun g => pauliStringHamiltonian g (h g)).map
        Observable.op).sum := by
  obtain ⟨h, hexp⟩ := H.exists_real_pauliString_expansion
  exact ⟨h, H.op_eq_sum_pauliStringHamiltonian_of_expansion hexp⟩

/-- **Nielsen & Chuang, Problem 4.3(4): first-order Trotter error, literal Pauli-string form.**
For a Hamiltonian `H` on the `n`-qubit register, splitting its propagator `exp(-i H Δ)` into ordered
product `∏_g exp(-i h_g g Δ)` over the `4ⁿ` Pauli-string propagators incurs only a second-order
error: there are real coefficients `h_g` and a constant `C ≥ 0` with
`‖(∏_g exp(-i h_g g Δ)) - exp(-i H Δ)‖ ≤ C·Δ²` for every `Δ ∈ [0, 1]`. The specialisation of the
general Hamiltonian-sum bound `Observable.exists_norm_prod_propagator_op_sub_propagator_op_le` to
the Pauli-string decomposition `Observable.op_eq_sum_pauliStringHamiltonian`. -/
theorem Observable.exists_norm_prod_pauliStringHamiltonian_propagator_sub_le
    (H : Observable (qudit (2 ^ n))) :
    ∃ (h : (Fin n → Fin 4) → ℝ) (C : ℝ), 0 ≤ C ∧ ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ 1 →
      ‖(Finset.univ.toList.map fun g =>
            ((pauliStringHamiltonian g (h g)).propagator 1 0 Δ).op).prod
          - (H.propagator 1 0 Δ).op‖ ≤ C * Δ ^ 2 := by
  obtain ⟨h, hH⟩ := H.op_eq_sum_pauliStringHamiltonian
  obtain ⟨C, hC0, hC⟩ := H.exists_norm_prod_propagator_op_sub_propagator_op_le
    (Finset.univ.toList.map fun g => pauliStringHamiltonian g (h g)) hH
  refine ⟨h, C, hC0, fun Δ hΔ0 hΔ1 => ?_⟩
  have hΔ := hC Δ hΔ0 hΔ1
  rwa [List.map_map] at hΔ

/-- **Nielsen & Chuang, Problem 4.3(5): accumulated Trotter error, literal Pauli-string form.**
For a Hamiltonian `H` on the `n`-qubit register, `k` iterations of the ordered Pauli-string
product at step `Δ = 1/k` converge to the full propagator `exp(-i H)` at first order: there are real
coefficients `h_g` and a constant `C ≥ 0` with
`‖(∏_g exp(-i h_g g /k))ᵏ - exp(-i H)‖ ≤ C/k` for every `k ≥ 1`. The specialisation of the general
`k`-fold bound `Observable.exists_norm_prod_propagator_op_pow_sub_propagator_op_le` to the
Pauli-string decomposition. -/
theorem Observable.exists_norm_prod_pauliStringHamiltonian_propagator_pow_sub_le
    (H : Observable (qudit (2 ^ n))) :
    ∃ (h : (Fin n → Fin 4) → ℝ) (C : ℝ), 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ‖(Finset.univ.toList.map fun g =>
            ((pauliStringHamiltonian g (h g)).propagator 1 0 (k : ℝ)⁻¹).op).prod ^ k
          - (H.propagator 1 0 1).op‖ ≤ C * (k : ℝ)⁻¹ := by
  obtain ⟨h, hH⟩ := H.op_eq_sum_pauliStringHamiltonian
  obtain ⟨C, hC0, hC⟩ := H.exists_norm_prod_propagator_op_pow_sub_propagator_op_le
    (Finset.univ.toList.map fun g => pauliStringHamiltonian g (h g)) hH
  refine ⟨h, C, hC0, fun k hk => ?_⟩
  have hk' := hC k hk
  rwa [List.map_map] at hk'

/-- **Nielsen & Chuang, Problem 4.3, the conclusion: universal Pauli–Trotter
approximation.** *Every* unitary `U` on the `n`-qubit register `qudit (2ⁿ)` is approximated, to
`O(1/k)`, by the `k`-fold product of Pauli-string propagators: there are real coefficients `h_g` and
a constant `C ≥ 0` with `‖(∏_g exp(-i h_g g /k))ᵏ - U‖ ≤ C/k` for every `k ≥ 1`.

This is the whole point of Problem 4.3, assembled from its parts: `U = exp(-iH)` for a Hermitian `H`
(part (1), `Evolution.exists_hamiltonian_generator_spectrum_Icc`); `H = Σ_g h_g g` decomposes into
Pauli strings (part (2), `Observable.op_eq_sum_pauliStringHamiltonian`); and the `k`-fold product of
the component propagators converges to `exp(-iH) = U` (part (5),
`Observable.exists_norm_prod_pauliStringHamiltonian_propagator_pow_sub_le`). Since each
`exp(-i h_g g /k)` is implementable in `O(n)` one- and two-qubit gates (part (3)),
this exhibits `U` as approximable by a circuit of `O(n · 4ⁿ · k)` such gates — N&C's universality
construction. -/
theorem Evolution.exists_pauliString_trotter_approximation (U : Evolution (qudit (2 ^ n))) :
    ∃ (h : (Fin n → Fin 4) → ℝ) (C : ℝ), 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ‖(Finset.univ.toList.map fun g =>
            ((pauliStringHamiltonian g (h g)).propagator 1 0 (k : ℝ)⁻¹).op).prod ^ k
          - U.op‖ ≤ C * (k : ℝ)⁻¹ := by
  obtain ⟨H, hU, _⟩ := U.exists_hamiltonian_generator_spectrum_Icc
  obtain ⟨h, C, hC0, hC⟩ := H.exists_norm_prod_pauliStringHamiltonian_propagator_pow_sub_le
  refine ⟨h, C, hC0, fun k hk => ?_⟩
  rw [hU]
  exact hC k hk

end AxQM
