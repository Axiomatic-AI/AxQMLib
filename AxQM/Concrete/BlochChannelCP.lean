/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochChannelMatrix
import AxQM.Concrete.BlochPauliTwirl

/-!
# Complete positivity forces the Fujiwara–Algoet inequalities (concrete core)

Concrete matrix algebra completing the qubit converse of
Nielsen & Chuang, Problem 8.3. The remaining ingredient of that converse is the
**complete-positivity criterion**: the singular-value diagonal of a unital qubit channel's Bloch
matrix satisfies the Fujiwara–Algoet inequalities `pauliTwirlInvProb d ≥ 0`. This file supplies its
matrix core: for a finite operator-sum (Kraus) family `A : ι → M₂(ℂ)` that is **unital**
(`∑ₖ Aₖ Aₖ† = I`) and **trace-preserving on the Paulis** (each `∑ₖ Aₖ σⱼ Aₖ†` traceless), the four
inverse-Pauli-transfer weights of the *diagonal* of its Bloch matrix `krausBlochMatrix A` are
**nonnegative**.

The proof needs **no Choi/positive-semidefinite machinery**: it rests on the per-matrix Pauli-twirl
identity
`‖tr(σₘ A)‖² = ½ tr(A A†) + ½ ∑ⱼ εₘⱼ tr(σⱼ A σⱼ A†)`
(with `εₘⱼ = ±1` the commutation sign of `σₘ` with `σⱼ`), which averaged over the family and
combined with unitality (`tr(∑ₖ Aₖ Aₖ†) = 2`) and the diagonal Bloch coefficients
(`d_j = ½ tr(σⱼ ∑ₖ Aₖ σⱼ Aₖ†)`) gives
`4 · pauliTwirlInvProb (diag M) m = ∑ₖ ‖tr(σₘ Aₖ)‖² ≥ 0`.
The right-hand side is a sum of squared complex moduli, so nonnegativity is immediate — the
Fujiwara–Algoet inequalities are exactly the Bell-basis diagonal of the (manifestly positive) Choi
matrix, but here the positivity is read off the sum-of-squares directly.

The Paulis `σₘ` are the existing indexed family `Concrete.pauli` (`σ₀ = I, σ₁ = X, σ₂ = Y, σ₃ = Z`).

* `Concrete.pauliSign` — the commutation sign `εₘⱼ = ±1` of `σₘ` with `σⱼ₊₁` (`X, Y, Z`); it is the
  sign convention of `Concrete.pauliBlochFlip` factored out (`pauliBlochFlip_apply`).
* `Concrete.normSq_trace_pauli_mul` — the per-matrix Pauli-twirl identity.
* `Concrete.pauliTwirlInvProb_krausBlochMatrix_diag_nonneg` — the criterion: the inverse-transfer
  weights of the Bloch-matrix diagonal of a unital trace-preserving Kraus family are nonnegative.
-/

open scoped Matrix

namespace AxQM.Concrete

open Matrix Complex

/-- The **commutation sign** `εₘⱼ` of the Pauli `σₘ` (`m : Fin 4`) with the Pauli `σⱼ₊₁`
(`j : Fin 3`, ranging over `X, Y, Z`): `+1` when they commute, `−1` when they anticommute. `σ₀ = I`
commutes with all; `σₘ` (`m ≥ 1`) commutes with itself and anticommutes with the other two. This is
exactly the sign convention of `Concrete.pauliBlochFlip` (which conjugation `σₘ ρ σₘ` applies to the
Bloch vector), factored out from the vector it multiplies — see `pauliBlochFlip_apply`. -/
def pauliSign : Fin 4 → Fin 3 → ℝ
  | 0 => ![1, 1, 1]
  | 1 => ![1, -1, -1]
  | 2 => ![-1, 1, -1]
  | 3 => ![-1, -1, 1]

/-- `pauliSign` **is** the sign convention of `pauliBlochFlip`: the `k`-th Pauli conjugation flips
the `j`-th Bloch coordinate by `εₖⱼ`, `pauliBlochFlip k v j = pauliSign k j * v j`. This ties the
sign table to the existing Pauli-conjugation Bloch action rather than restating it independently. -/
theorem pauliBlochFlip_apply (k : Fin 4) (v : Fin 3 → ℝ) (j : Fin 3) :
    pauliBlochFlip k v j = pauliSign k j * v j := by
  fin_cases k <;> fin_cases j <;>
    simp [pauliBlochFlip, pauliSign, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- **The per-matrix Pauli-twirl identity.** For any `2 × 2` complex matrix `M`,
`‖tr(σₘ M)‖² = ½ tr(M M†) + ½ ∑ⱼ εₘⱼ tr(σⱼ M σⱼ M†)`,
where `σₘ = Concrete.pauli m` and `εₘⱼ = pauliSign m j` is the commutation sign of `σₘ` with `σⱼ`
(`j : Fin 3` = `X, Y, Z`). This is the Pauli-basis expansion of `‖tr(σₘ M)‖²` and holds for *every*
`M` (no channel hypothesis): writing `‖z‖² = z · z̄` and `z̄ = tr(σₘ Mᴴ)`, both sides are the same
quadratic in the entries of `M`. It is the algebraic engine behind the Fujiwara–Algoet criterion:
summed over a unital trace-preserving Kraus family it exhibits each inverse-Pauli-transfer weight as
a sum of squared moduli.

The four cases `σₘ ∈ {I, X, Y, Z}` are proved uniformly: rewrite `‖z‖² = z · z̄` and
`z̄ = tr(σₘ Mᴴ)` (Hermiticity of `σₘ` = `pauli_isHermitian`), reduce `pauli m` to the concrete
matrix, and close the resulting quadratic in the entries of `M` by `ring`. `fin_cases m` and
`exacts` dispatch the general `m` to the concrete cases by defeq. -/
theorem normSq_trace_pauli_mul (m : Fin 4) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (Complex.normSq ((pauli m * M).trace) : ℂ)
      = 2⁻¹ * (M * Mᴴ).trace
        + 2⁻¹ * ∑ j : Fin 3, (pauliSign m j : ℂ)
            * (pauliDot (Pi.single j 1) * M * pauliDot (Pi.single j 1) * Mᴴ).trace := by
  have h0 : (Complex.normSq ((pauli 0 * M).trace) : ℂ)
      = 2⁻¹ * (M * Mᴴ).trace + 2⁻¹ * ∑ j : Fin 3, (pauliSign 0 j : ℂ)
          * (pauliDot (Pi.single j 1) * M * pauliDot (Pi.single j 1) * Mᴴ).trace := by
    rw [← Complex.mul_conj, starRingEnd_apply, ← Matrix.trace_conjTranspose,
      Matrix.conjTranspose_mul, show (pauli 0)ᴴ = pauli 0 from pauli_isHermitian 0,
      show pauli 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) from rfl]
    simp only [pauliSign, Fin.sum_univ_three, pauliDot_single_zero, pauliDot_single_one,
      pauliDot_single_two, pauliX, pauliY, pauliZ, one_mul, mul_one, Matrix.trace_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  have h1 : (Complex.normSq ((pauli 1 * M).trace) : ℂ)
      = 2⁻¹ * (M * Mᴴ).trace + 2⁻¹ * ∑ j : Fin 3, (pauliSign 1 j : ℂ)
          * (pauliDot (Pi.single j 1) * M * pauliDot (Pi.single j 1) * Mᴴ).trace := by
    rw [← Complex.mul_conj, starRingEnd_apply, ← Matrix.trace_conjTranspose,
      Matrix.conjTranspose_mul, show (pauli 1)ᴴ = pauli 1 from pauli_isHermitian 1,
      show pauli 1 = pauliX from rfl]
    simp only [pauliSign, Fin.sum_univ_three, pauliDot_single_zero, pauliDot_single_one,
      pauliDot_single_two, pauliX, pauliY, pauliZ, one_mul, mul_one, Matrix.trace_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  have h2 : (Complex.normSq ((pauli 2 * M).trace) : ℂ)
      = 2⁻¹ * (M * Mᴴ).trace + 2⁻¹ * ∑ j : Fin 3, (pauliSign 2 j : ℂ)
          * (pauliDot (Pi.single j 1) * M * pauliDot (Pi.single j 1) * Mᴴ).trace := by
    rw [← Complex.mul_conj, starRingEnd_apply, ← Matrix.trace_conjTranspose,
      Matrix.conjTranspose_mul, show (pauli 2)ᴴ = pauli 2 from pauli_isHermitian 2,
      show pauli 2 = pauliY from rfl]
    simp only [pauliSign, Fin.sum_univ_three, pauliDot_single_zero, pauliDot_single_one,
      pauliDot_single_two, pauliX, pauliY, pauliZ, one_mul, mul_one, Matrix.trace_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  have h3 : (Complex.normSq ((pauli 3 * M).trace) : ℂ)
      = 2⁻¹ * (M * Mᴴ).trace + 2⁻¹ * ∑ j : Fin 3, (pauliSign 3 j : ℂ)
          * (pauliDot (Pi.single j 1) * M * pauliDot (Pi.single j 1) * Mᴴ).trace := by
    rw [← Complex.mul_conj, starRingEnd_apply, ← Matrix.trace_conjTranspose,
      Matrix.conjTranspose_mul, show (pauli 3)ᴴ = pauli 3 from pauli_isHermitian 3,
      show pauli 3 = pauliZ from rfl]
    simp only [pauliSign, Fin.sum_univ_three, pauliDot_single_zero, pauliDot_single_one,
      pauliDot_single_two, pauliX, pauliY, pauliZ, one_mul, mul_one, Matrix.trace_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  fin_cases m
  exacts [h0, h1, h2, h3]

/-- **The diagonal Bloch coefficient as a Pauli trace.** For a unital *trace-preserving* Kraus
family — precisely, one for which each Pauli image `∑ₖ Aₖ σⱼ Aₖ†` is traceless (`htl`) — the `j`-th
diagonal entry of the Bloch matrix is recovered by the Hilbert–Schmidt pairing:
`∑ₖ tr(σⱼ Aₖ σⱼ Aₖ†) = 2 · krausBlochMatrix A j j`. The traceless (Hermitian) image is
`(krausBlochMatrix A · j) · σ` (`pauliDot_pauliCoords_of_isHermitian_trace_zero`), so pairing it
with `σⱼ` picks out its `j`-th coordinate (`pauliDot_trace_mul`). -/
theorem sum_trace_conj_pauliDot_single_diag {ι : Type*} [Fintype ι]
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (htl : ∀ j, (∑ k, A k * pauliDot (Pi.single j 1) * (A k)ᴴ).trace = 0) (j : Fin 3) :
    ∑ k, (pauliDot (Pi.single j 1) * A k * pauliDot (Pi.single j 1) * (A k)ᴴ).trace
      = 2 * (krausBlochMatrix A j j : ℝ) := by
  have hPD : pauliDot (fun i => krausBlochMatrix A i j)
      = ∑ k, A k * pauliDot (Pi.single j 1) * (A k)ᴴ :=
    pauliDot_pauliCoords_of_isHermitian_trace_zero
      (sum_conj_pauliDot_single_isHermitian A j) (htl j)
  have hfactor : ∑ k, (pauliDot (Pi.single j 1) * A k * pauliDot (Pi.single j 1) * (A k)ᴴ).trace
      = (pauliDot (Pi.single j 1) * ∑ k, A k * pauliDot (Pi.single j 1) * (A k)ᴴ).trace := by
    rw [Finset.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [mul_assoc (pauliDot (Pi.single j 1)) (A k) (pauliDot (Pi.single j 1)), mul_assoc]
  rw [hfactor, ← hPD, pauliDot_trace_mul, single_dotProduct, one_mul]

/-- **The complete-positivity (Fujiwara–Algoet) criterion, matrix core.** For a finite operator-sum
(Kraus) family `A : ι → M₂(ℂ)` that is **unital** (`∑ₖ Aₖ Aₖ† = I`) and **trace-preserving on the
Paulis** (each `∑ₖ Aₖ σⱼ Aₖ†` traceless), the four inverse-Pauli-transfer weights of the *diagonal*
of its Bloch matrix `krausBlochMatrix A` are nonnegative:
`0 ≤ pauliTwirlInvProb (fun j ↦ krausBlochMatrix A j j) m` for each `m : Fin 4`.

This is the last outstanding ingredient of the qubit converse of Nielsen & Chuang, Problem 8.3.
`4 · pauliTwirlInvProb (diag) m = ∑ₖ ‖tr(σₘ Aₖ)‖²` (via `normSq_trace_pauli_mul` summed over the
family, `sum_trace_conj_pauliDot_single_diag` for the diagonal coefficients and unitality
`tr(∑ₖ Aₖ Aₖ†) = 2` for the constant); the right-hand side is a sum of squared complex moduli, hence
nonnegative — so `pauliTwirlInvProb (diag)` is a genuine probability distribution and the diagonal
channel is a random-unitary (Pauli) channel. -/
theorem pauliTwirlInvProb_krausBlochMatrix_diag_nonneg {ι : Type*} [Fintype ι]
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∑ k, A k * (A k)ᴴ = 1)
    (htl : ∀ j, (∑ k, A k * pauliDot (Pi.single j 1) * (A k)ᴴ).trace = 0) (m : Fin 4) :
    0 ≤ pauliTwirlInvProb (fun j => krausBlochMatrix A j j) m := by
  set d : Fin 3 → ℝ := fun j => krausBlochMatrix A j j with hd
  -- The nonnegative right-hand side: a sum of squared complex moduli.
  have hnn : (0 : ℝ) ≤ ∑ k, Complex.normSq ((pauli m * A k).trace) :=
    Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _
  -- Unitality: `tr(∑ₖ Aₖ Aₖ†) = tr I = 2`.
  have hUtr : (∑ k, A k * (A k)ᴴ).trace = 2 := by rw [hU, trace_one_fin_two]
  -- The averaged Pauli-twirl identity, in `ℂ`.
  have hC : ((∑ k, Complex.normSq ((pauli m * A k).trace) : ℝ) : ℂ)
      = 2⁻¹ * (2 : ℂ)
        + 2⁻¹ * ∑ j : Fin 3, (pauliSign m j : ℂ) * (2 * (d j : ℝ)) := by
    rw [Complex.ofReal_sum,
      Finset.sum_congr rfl fun k _ => normSq_trace_pauli_mul m (A k),
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Matrix.trace_sum, hUtr,
      Finset.sum_comm,
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
        (by rw [← Finset.mul_sum, sum_trace_conj_pauliDot_single_diag A htl j] :
          (∑ k, (pauliSign m j : ℂ)
              * (pauliDot (Pi.single j 1) * A k * pauliDot (Pi.single j 1) * (A k)ᴴ).trace)
            = (pauliSign m j : ℂ) * (2 * (d j : ℝ))))]
  -- The constant `1` plus the signed diagonal terms *is* `4 · pauliTwirlInvProb (diag) m`.
  have hExpr : ((4 : ℝ) * pauliTwirlInvProb d m : ℂ)
      = 2⁻¹ * (2 : ℂ) + 2⁻¹ * ∑ j : Fin 3, (pauliSign m j : ℂ) * (2 * (d j : ℝ)) := by
    fin_cases m <;>
      simp only [pauliSign, pauliTwirlInvProb, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
      push_cast <;> ring
  have key : (4 : ℝ) * pauliTwirlInvProb d m
      = ∑ k, Complex.normSq ((pauli m * A k).trace) := by
    exact_mod_cast hExpr.trans hC.symm
  linarith [key, hnn]

end AxQM.Concrete
