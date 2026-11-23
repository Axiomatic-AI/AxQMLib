/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli
import ToMathlib.Analysis.Matrix.HilbertSchmidt
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import ToMathlib.Algebra.BigOperators.Fin

/-!
# Concrete: the `n`-fold Pauli strings and the Pauli basis of `M₂ₙ(ℂ)`

This file builds, for each `n`, the family of **`n`-fold Pauli tensor products** ("Pauli strings")
and proves that they form a basis of the `2ⁿ × 2ⁿ` complex matrices, with a **real-coefficient**
expansion for every Hermitian matrix. This is the mathematical content underlying part (2) of
Nielsen & Chuang, Problem 4.3 (`H = Σ_g h_g g` with real `h_g`, the sum over all `n`-fold tensor
products `g` of `{I, X, Y, Z}`) — see `AxQM/NC/Ch4/Problem4_3.lean`.

## The construction

An `n`-qubit register carries the index type `Fin n → Fin 2` (a bit-string of length `n`), of
cardinality `2ⁿ`, so its operators are `Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ`. A Pauli
string is indexed by `g : Fin n → Fin 4` (a choice of one of `σ₀ = I, σ₁ = X, σ₂ = Y, σ₃ = Z`
per qubit) and defined **entrywise** as the product of the per-qubit Pauli entries:

`pauliString g i j = ∏ k, pauli (g k) (i k) (j k)`.

Working with the entrywise product (rather than an iterated Kronecker product) keeps the trace
algebra a single `Finset.prod_univ_sum` factorisation.

The single-qubit trace orthogonality `tr(σᵢ σⱼ) = 2 δᵢⱼ` it rests on (`Concrete.pauli_trace_mul`)
lives with the `pauli` family in `Concrete/Pauli.lean`.

## What is proved

* `pauliString` / `pauliString_apply` — the Pauli string and its defining entry formula.
* `pauliString_isHermitian` — each Pauli string is Hermitian (a product of Hermitian factors).
* `pauliString_trace_mul` — the **trace orthogonality** `tr(P_g P_h) = 2ⁿ δ_{g h}`, the
  `n`-fold Hilbert–Schmidt orthogonality of the Pauli strings.
* `pauliString_linearIndependent` — the `4ⁿ` Pauli strings are `ℂ`-linearly independent
  (immediate from trace orthogonality).
* `pauliBasis` — hence they form a **basis** of `M₂ₙ(ℂ)` (a linearly independent family of
  `finrank = 4ⁿ` vectors).
* `exists_real_pauliString_expansion` — every **Hermitian** matrix is a **real**-coefficient
  linear combination of Pauli strings, `M = Σ_g (h_g : ℂ) • P_g` with `h_g : ℝ`. This is the
  faithful matrix-level statement of Problem 4.3(2).
* `pauliStringStd` / `pauliStringStd_isHermitian` — the same Pauli string reindexed to the flat
  `Fin (2ⁿ)` computational-basis ordering (via `finFunctionFinEquiv`), still Hermitian; the form
  ready to be promoted to an operator on the standard register `EuclideanSpace ℂ (Fin (2ⁿ))`.

## Design notes

* The index type is `Fin n → Fin 2` rather than `Fin (2ⁿ)`; this makes the per-qubit product
  structure literal and lets `Finset.prod_univ_sum` collapse the double trace sum
  `∑ᵢ ∑ⱼ ∏ₖ (…)` into `∏ₖ ∑ₐ ∑_b (…) = ∏ₖ tr(σ_{gₖ} σ_{hₖ})`.
* The coefficients are real because, for Hermitian `A`, `B`, the trace `tr(A B)` is real
  (`Matrix.IsHermitian.im_trace_mul`, in `ToMathlib`): `conj tr(AB) = tr((AB)ᴴ) = tr(BA)
  = tr(AB)`.
-/

open Matrix Complex

open scoped BigOperators

namespace AxQM.Concrete

/-! ### The `n`-fold Pauli strings

The single-qubit facts `pauli_isHermitian`, `pauli_conj_apply` and the trace orthogonality
`pauli_trace_mul` (`tr(σᵢ σⱼ) = 2 δᵢⱼ`) live with the `pauli` family in `Concrete/Pauli.lean`. -/

variable {n : ℕ}

/-- The `n`-fold **Pauli string** for `g : Fin n → Fin 4`, the operator on the `n`-qubit
register (index type `Fin n → Fin 2`) whose `(i, j)` entry is the product of the per-qubit Pauli
entries `∏ₖ σ_{gₖ} (iₖ) (jₖ)`. Entrywise, this is the tensor product `σ_{g₀} ⊗ ⋯ ⊗ σ_{g_{n-1}}`. -/
def pauliString (g : Fin n → Fin 4) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun i j => ∏ k, pauli (g k) (i k) (j k)

@[simp]
theorem pauliString_apply (g : Fin n → Fin 4) (i j : Fin n → Fin 2) :
    pauliString g i j = ∏ k, pauli (g k) (i k) (j k) := rfl

/-- Each Pauli string is Hermitian: its `(i, j)` entry is a product of factors each Hermitian,
so conjugating and transposing returns the same product (`pauli_conj_apply` per factor). -/
theorem pauliString_isHermitian (g : Fin n → Fin 4) : (pauliString g).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply, pauliString_apply, pauliString_apply, ← starRingEnd_apply,
    map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [starRingEnd_apply, pauli_conj_apply]

/-- The **all-identity Pauli string** `σ₀ ⊗ ⋯ ⊗ σ₀ = I ⊗ ⋯ ⊗ I` is the identity matrix. Its
`(i, j)` entry is `∏ₖ σ₀ (iₖ) (jₖ) = ∏ₖ (1 : M₂(ℂ)) (iₖ) (jₖ) = ∏ₖ [iₖ = jₖ]`, which is `1`
exactly when `i = j`. (A structural fact about `pauliString`; it isolates the string whose trace
pairing is `tr M` itself, used by the tomographic trace-normalisation refinement.) -/
theorem pauliString_const_zero : pauliString (n := n) (fun _ => 0) = 1 := by
  ext i j
  rw [pauliString_apply, Matrix.one_apply]
  have h0 : (pauli 0) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  simp only [h0, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · rw [ite_eq_right hij]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hij
    exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)

/-- The trace of a product of two matrices given by per-qubit entry products factors over the
qubits: `tr((∏ₖ Aₖ) (∏ₖ Bₖ)) = ∏ₖ tr(Aₖ Bₖ)`, where the two matrices have `(i,j)` entries
`∏ₖ Aₖ(iₖ)(jₖ)` and `∏ₖ Bₖ(iₖ)(jₖ)`. This is the algebraic heart of the Hilbert–Schmidt
orthogonality of the Pauli strings; it collapses the double sum `∑ᵢ ∑ⱼ` via
`Finset.prod_univ_sum`. -/
private theorem trace_mul_prodMatrix (A B : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    ((Matrix.of fun i j : Fin n → Fin 2 => ∏ k, A k (i k) (j k)) *
        (Matrix.of fun i j : Fin n → Fin 2 => ∏ k, B k (i k) (j k))).trace
      = ∏ k, (A k * B k).trace := by
  -- RHS: expand each factor `tr(Aₖ Bₖ) = ∑ a, ∑ b, Aₖ a b * Bₖ b a`, then two `prod_univ_sum`
  -- collapse `∏ₖ ∑ₐ ∑_b` into the double sum `∑ᵢ ∑ⱼ ∏ₖ`.
  have hRHS : (∏ k, (A k * B k).trace)
      = ∑ i : Fin n → Fin 2, ∑ j : Fin n → Fin 2,
          ∏ k, A k (i k) (j k) * B k (j k) (i k) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [hRHS]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
    ← Finset.prod_mul_distrib]

/-- **Trace orthogonality of the Pauli strings**: `tr(P_g P_h) = 2ⁿ δ_{g h}`. Since each Pauli
string is Hermitian, this is the `n`-fold Hilbert–Schmidt orthogonality of the family — the
crucial fact making them a basis. It factors over qubits (`trace_mul_prodMatrix`) into a product
of single-qubit traces `tr(σ_{gₖ} σ_{hₖ}) = 2 δ_{gₖ hₖ}` (`pauli_trace_mul`); the product is `2ⁿ`
when `g = h` and vanishes as soon as one factor differs. -/
theorem pauliString_trace_mul (g h : Fin n → Fin 4) :
    (pauliString g * pauliString h).trace = if g = h then (2 : ℂ) ^ n else 0 := by
  have hfac : (pauliString g * pauliString h).trace
      = ∏ k, (pauli (g k) * pauli (h k)).trace :=
    trace_mul_prodMatrix (fun k => pauli (g k)) (fun k => pauli (h k))
  rw [hfac]
  simp_rw [pauli_trace_mul]
  by_cases hgh : g = h
  · subst hgh; simp
  · rw [ite_eq_right hgh]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hgh
    exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)

/-- **Trace of a single Pauli string**: `tr(P_h) = 2ⁿ` when `h` is the identity index and `0`
otherwise. Immediate from the Hilbert–Schmidt orthogonality `pauliString_trace_mul` (with the
identity `pauliString 0 = 1`, `pauliString_const_zero`). -/
theorem pauliString_trace (h : Fin n → Fin 4) :
    (pauliString h).trace = if h = 0 then (2 : ℂ) ^ n else 0 := by
  have hz : pauliString (0 : Fin n → Fin 4) = 1 := pauliString_const_zero
  have hmul := pauliString_trace_mul h (0 : Fin n → Fin 4)
  rw [hz, mul_one] at hmul
  rw [hmul]

/-- **Trace pairing extracts a coefficient**: `tr(P_m * ∑_g c_g • P_g) = c_m · 2ⁿ`. Only the
`g = m` term survives the Hilbert–Schmidt orthogonality `pauliString_trace_mul`, contributing
`c_m · 2ⁿ`. This coefficient-extraction identity underlies both `pauliString_linearIndependent`
and `exists_real_pauliString_expansion`. -/
theorem pauliString_trace_mul_sum_smul (c : (Fin n → Fin 4) → ℂ) (m : Fin n → Fin 4) :
    (pauliString m * ∑ g, c g • pauliString g).trace = c m * (2 : ℂ) ^ n := by
  rw [Finset.mul_sum, Matrix.trace_sum, Finset.sum_eq_single m]
  · rw [mul_smul_comm, Matrix.trace_smul, pauliString_trace_mul, ite_eq_left rfl, smul_eq_mul]
  · intro b _ hb
    rw [mul_smul_comm, Matrix.trace_smul, pauliString_trace_mul, ite_eq_right (Ne.symm hb),
        smul_zero]
  · intro hm; exact absurd (Finset.mem_univ m) hm

/-! ### The Pauli basis and the real Hermitian expansion -/

/-- The `4ⁿ` Pauli strings are `ℂ`-linearly independent. If `∑_g c_g P_g = 0`, testing against
`P_m` under the trace pairing gives `0 = tr(P_m ∑_g c_g P_g) = ∑_g c_g tr(P_m P_g) = c_m 2ⁿ`,
so every `c_m = 0` (using `pauliString_trace_mul` and `2ⁿ ≠ 0`). -/
theorem pauliString_linearIndependent : LinearIndependent ℂ (pauliString (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc m
  have key := pauliString_trace_mul_sum_smul c m
  rw [hc, Matrix.mul_zero, Matrix.trace_zero] at key
  exact (mul_eq_zero.mp key.symm).resolve_right (pow_ne_zero n two_ne_zero)

/-- The `n`-fold Pauli strings form a **basis** of the `2ⁿ × 2ⁿ` complex matrices: a linearly
independent family whose cardinality `4ⁿ` equals `finrank ℂ M₂ₙ(ℂ) = (2ⁿ)²` (N&C Ex 2.39(2),
`Matrix.finrank_eq_card_sq`). This is the "the Pauli strings span the operators" half of
Problem 4.3(2). -/
noncomputable def pauliBasis :
    Module.Basis (Fin n → Fin 4) ℂ (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := by
  haveI : Nonempty (Fin n → Fin 4) := ⟨fun _ => 0⟩
  refine basisOfLinearIndependentOfCardEqFinrank pauliString_linearIndependent ?_
  rw [Matrix.finrank_eq_card_sq]
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [pow_two, ← mul_pow]
  norm_num

@[simp]
theorem pauliBasis_apply (g : Fin n → Fin 4) : pauliBasis g = pauliString g := by
  rw [pauliBasis]
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) g

/-- **The Pauli-basis expansion of a matrix**: `∑_g (pauliBasis.repr M g) • P_g = M`. This is just
`pauliBasis.sum_repr` with the basis vectors rewritten to Pauli strings (`pauliBasis_apply`); it is
the foundational identity underlying every trace-pairing extraction. -/
theorem sum_repr_smul_pauliString (M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    ∑ g, pauliBasis.repr M g • pauliString g = M := by
  conv_rhs => rw [← pauliBasis.sum_repr M]
  exact Finset.sum_congr rfl fun g _ => by rw [pauliBasis_apply]

/-- **Trace pairing recovers the Pauli coordinate**: `tr(P_g M) = (pauliBasis.repr M g) · 2ⁿ`.
Writing `M = Σ_h (repr M h) • P_h` in the Pauli basis (`sum_repr_smul_pauliString`) and pairing
against `P_g`, only the `h = g` term survives the Hilbert–Schmidt orthogonality
(`pauliString_trace_mul_sum_smul`). The name is kept distinct from the orthogonality lemma
`pauliString_trace_mul` (`tr(P_g P_h) = 2ⁿ δ_{gh}`). -/
theorem trace_pauliString_mul_eq_repr (M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (g : Fin n → Fin 4) :
    (pauliString g * M).trace = pauliBasis.repr M g * (2 : ℂ) ^ n := by
  have h := pauliString_trace_mul_sum_smul (fun h => pauliBasis.repr M h) g
  rwa [sum_repr_smul_pauliString] at h

/-- **Trace pairing with a Hermitian matrix is real**: `im tr(P_g M) = 0`. Both `P_g` and `M` are
Hermitian, and `tr(A B)` is real for Hermitian `A, B` (`Matrix.IsHermitian.im_trace_mul`). For a
density matrix `M` these are the real Pauli expectation values `⟨P_g⟩` used by state tomography
(`Concrete/PauliTomography.lean`). -/
theorem trace_pauliString_mul_im {M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ}
    (hM : M.IsHermitian) (g : Fin n → Fin 4) : ((pauliString g * M).trace).im = 0 := by
  simpa [RCLike.im_to_complex] using (pauliString_isHermitian g).im_trace_mul hM

/-- **Real-coefficient Pauli expansion of a Hermitian matrix** (Nielsen & Chuang, Problem 4.3(2),
matrix form). Every Hermitian `2ⁿ × 2ⁿ` matrix `M` is a **real** linear combination of the Pauli
strings, `M = Σ_g (h_g : ℂ) • P_g` with `h_g : ℝ`. The complex coefficients are `pauliBasis.repr M`;
each is real because `pauliBasis.repr M g · 2ⁿ = tr(P_g M)` is real (both `P_g` and `M` Hermitian,
`Matrix.IsHermitian.im_trace_mul`), so its imaginary part vanishes. -/
theorem exists_real_pauliString_expansion
    {M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ} (hM : M.IsHermitian) :
    ∃ h : (Fin n → Fin 4) → ℝ, M = ∑ g, (h g : ℂ) • pauliString g := by
  have hsum : M = ∑ g, (pauliBasis.repr M g) • pauliString g :=
    (sum_repr_smul_pauliString M).symm
  have hreal : ∀ g, (pauliBasis.repr M g).im = 0 := by
    intro g
    have htr : (pauliString g * M).trace = pauliBasis.repr M g * (2 : ℂ) ^ n :=
      trace_pauliString_mul_eq_repr M g
    have hreal_tr : ((pauliString g * M).trace).im = 0 := trace_pauliString_mul_im hM g
    have h2 : ((2 : ℂ) ^ n) = (((2 : ℝ) ^ n : ℝ) : ℂ) := by push_cast; ring
    rw [htr, h2, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
      at hreal_tr
    exact (mul_eq_zero.mp hreal_tr).resolve_right (pow_ne_zero n two_ne_zero)
  refine ⟨fun g => (pauliBasis.repr M g).re, ?_⟩
  conv_lhs => rw [hsum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hcoe : ((pauliBasis.repr M g).re : ℂ) = pauliBasis.repr M g :=
    Complex.ext (by simp) (by simp [hreal g])
  simp only [hcoe]

/-! ### The Pauli string on the standard `Fin (2ⁿ)` register indexing

The `n`-qubit register carries two interchangeable index types: the bit strings `Fin n → Fin 2`
used above (which make the per-qubit product structure literal), and the flat `Fin (2ⁿ)` used by
the computational-basis register `EuclideanSpace ℂ (Fin (2ⁿ))`. The two are identified by
`finFunctionFinEquiv : (Fin n → Fin 2) ≃ Fin (2ⁿ)`. This section transports a Pauli string to the
flat indexing, so it can be promoted to an operator on the standard register. -/

/-- The `n`-fold **Pauli string on the standard register indexing** `Fin (2ⁿ)`: the matrix
`pauliString g`, reindexed from bit strings `Fin n → Fin 2` to `Fin (2ⁿ)` along
`finFunctionFinEquiv`. Its `(I, J)` entry is `pauliString g (e⁻¹ I) (e⁻¹ J)` for
`e = finFunctionFinEquiv`. This is the same operator as `pauliString g`, expressed on the flat
`Fin (2ⁿ)` computational-basis ordering that the register `EuclideanSpace ℂ (Fin (2ⁿ))` uses. -/
def pauliStringStd (g : Fin n → Fin 4) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (pauliString g).submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm

/-- The standard-indexed Pauli string is **Hermitian**: reindexing a Hermitian matrix by the same
map on rows and columns preserves Hermitianness (`Matrix.IsHermitian.submatrix`), and each Pauli
string is Hermitian (`pauliString_isHermitian`). -/
theorem pauliStringStd_isHermitian (g : Fin n → Fin 4) : (pauliStringStd g).IsHermitian :=
  (pauliString_isHermitian g).submatrix finFunctionFinEquiv.symm

/-! ### Injectivity of the Pauli strings -/

/-- The Pauli strings are **injective** in their index: distinct `g` give distinct operators `P_g`.
Immediate from their `ℂ`-linear independence (`pauliString_linearIndependent`). -/
theorem pauliString_injective : Function.Injective (pauliString (n := n)) :=
  pauliString_linearIndependent.injective

/-- A Pauli string is the **identity operator** exactly when its index is all-identity:
`P_g = I ↔ g = 0`. The `⇐` direction is `pauliString_const_zero`; the `⇒` direction is injectivity
(`pauliString_injective`). -/
theorem pauliString_eq_one_iff (g : Fin n → Fin 4) : pauliString g = 1 ↔ g = 0 := by
  rw [← pauliString_const_zero, pauliString_injective.eq_iff, Pi.zero_def]

/-- The **standard-indexed all-identity Pauli string is the identity matrix**:
`pauliStringStd 0 = 1`. Reindexing the identity matrix along an equivalence on both rows and columns
leaves it fixed (`Matrix.submatrix_one_equiv`), and the underlying string is already the identity
(`pauliString_const_zero`). This is the standard-register form of `pauliString_const_zero`, the
`(I, J)`-flat-indexing companion used wherever the identity Pauli string appears (e.g. the
global-phase Trotter summand of the all-identity string). -/
@[simp] theorem pauliStringStd_zero : pauliStringStd (0 : Fin n → Fin 4) = 1 := by
  simp only [pauliStringStd, Pi.zero_def, pauliString_const_zero, Matrix.submatrix_one_equiv]

end AxQM.Concrete
