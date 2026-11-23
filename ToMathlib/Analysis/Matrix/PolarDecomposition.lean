/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Polar decomposition of positive, unitary and Hermitian matrices

The *polar decomposition* of a square matrix `A` writes `A = U * J` (and `A = K * U`) with `U`
unitary and `J`, `K` positive semidefinite, where the positive factors are the canonical
`J = √(Aᴴ * A)` and `K = √(A * Aᴴ)` (Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Theorem 2.3). Here `√` is the positive semidefinite square root `CFC.sqrt` supplied by
the continuous functional calculus on the C⋆-algebra `Matrix n n 𝕜` (see
`Mathlib/Analysis/Matrix/Order.lean`, whose scoped `MatrixOrder` instances make `Matrix n n 𝕜`
a `StarOrderedRing` and identify `0 ≤ A` with `A.PosSemidef`).

This file computes the polar decomposition in the three special cases of **Nielsen & Chuang,
Exercise 2.48**: for a positive `P` it is `P = 1 · P`, for a unitary `U` it is `U = U · 1`, and for
a Hermitian `H` it is `H = sgn(H) · |H|` with `sgn(H)` the (kernel-completed) sign of `H`.

## Main results

* `Matrix.PosSemidef.sqrt_conjTranspose_mul_self`,
  `Matrix.PosSemidef.sqrt_mul_conjTranspose_self`: for a positive semidefinite `P`, both polar
  factors are `P` itself, `√(Pᴴ * P) = √(P * Pᴴ) = P`. Combined with
  `Matrix.PosSemidef.eq_one_mul_sqrt_conjTranspose_mul_self` (`P = 1 * √(Pᴴ * P)`) this is the
  polar decomposition `P = I · P` of a positive matrix (unitary factor `1`).
* `Matrix.sqrt_conjTranspose_mul_self_of_mem_unitaryGroup`,
  `Matrix.sqrt_mul_conjTranspose_self_of_mem_unitaryGroup`: for a unitary `U`, both polar factors
  are the identity, `√(Uᴴ * U) = √(U * Uᴴ) = 1`. Combined with
  `Matrix.eq_mul_sqrt_conjTranspose_mul_self_of_mem_unitaryGroup` (`U = U * √(Uᴴ * U)`) this is the
  polar decomposition `U = U · I` of a unitary matrix (positive factor `1`).
* `Matrix.IsHermitian.sqrt_conjTranspose_mul_self`: for a Hermitian `H`, the positive factor is the
  *absolute value* `√(H ^ 2)` (i.e. `|H|`), `√(Hᴴ * H) = √(H ^ 2)`.
* `Matrix.IsHermitian.polarUnitary`, `Matrix.IsHermitian.polarUnitary_mem_unitaryGroup` and
  `Matrix.IsHermitian.eq_polarUnitary_mul_sqrt_conjTranspose_mul_self`: the unitary factor of a
  Hermitian `H` is its *sign* `sgn(H)` (built by the continuous functional calculus of `polarSign`,
  a unitary for every Hermitian `H`), giving the full decomposition `H = sgn(H) · |H|`
  (`Matrix.IsHermitian.exists_mem_unitaryGroup_mul_sqrt_conjTranspose_mul_self` is the existence
  form).
* `Matrix.sqrt_conjTranspose_mul_self_eq_self_iff`: the positive factor `√(Aᴴ * A)` equals `A`
  itself if and only if `A` is positive semidefinite. In particular, among Hermitian matrices the
  polar factor `|H| = √(H ^ 2)` coincides with `H` exactly for the positive ones.

## Implementation notes

For a Hermitian `H` the unitary factor is `sgn(H) = cfc polarSign H`, where `polarSign` is the sign
function normalised to `1` at `0`. This is a genuine unitary for *every* Hermitian `H`: at a zero
eigenvalue the value `1` fills in the kernel (where the sign would otherwise be a mere partial
isometry, cf. the uniqueness clause of N&C Theorem 2.3), while on the range it is the usual `±1`
sign, so that `sgn(H) · |H| = H`.

All results use the scoped matrix order `MatrixOrder` together with `ComplexOrder`.
-/

@[expose] public section

namespace Matrix

open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]

set_option linter.unusedDecidableInType false in
/-- **N&C Exercise 2.48, positive case (left factor).** The positive factor `√(Pᴴ * P)` of the
polar decomposition of a positive semidefinite matrix `P` is `P` itself. -/
theorem PosSemidef.sqrt_conjTranspose_mul_self {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    CFC.sqrt (Pᴴ * P) = P := by
  rw [hP.1]; exact CFC.sqrt_mul_self P hP.nonneg

set_option linter.unusedDecidableInType false in
/-- **N&C Exercise 2.48, positive case (right factor).** The positive factor `√(P * Pᴴ)` of the
polar decomposition of a positive semidefinite matrix `P` is `P` itself. -/
theorem PosSemidef.sqrt_mul_conjTranspose_self {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    CFC.sqrt (P * Pᴴ) = P := by
  rw [hP.1]; exact CFC.sqrt_mul_self P hP.nonneg

/-- **N&C Exercise 2.48, positive case (decomposition).** The polar decomposition of a positive
semidefinite matrix `P` is `P = I · P`: the unitary factor is `1` and the positive factor is `P`
(`= √(Pᴴ * P)`). -/
theorem PosSemidef.eq_one_mul_sqrt_conjTranspose_mul_self {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    P = 1 * CFC.sqrt (Pᴴ * P) := by
  rw [hP.sqrt_conjTranspose_mul_self, one_mul]

/-- **N&C Exercise 2.48, unitary case (left factor).** The positive factor `√(Uᴴ * U)` of the polar
decomposition of a unitary matrix `U` is the identity. -/
theorem sqrt_conjTranspose_mul_self_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) : CFC.sqrt (Uᴴ * U) = 1 := by
  rw [← star_eq_conjTranspose, (mem_unitaryGroup_iff').mp hU, CFC.sqrt_one]

/-- **N&C Exercise 2.48, unitary case (right factor).** The positive factor `√(U * Uᴴ)` of the polar
decomposition of a unitary matrix `U` is the identity. -/
theorem sqrt_mul_conjTranspose_self_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) : CFC.sqrt (U * Uᴴ) = 1 := by
  rw [← star_eq_conjTranspose, (mem_unitaryGroup_iff).mp hU, CFC.sqrt_one]

/-- **N&C Exercise 2.48, unitary case (decomposition).** The polar decomposition of a unitary matrix
`U` is `U = U · I`: the unitary factor is `U` and the positive factor is `1` (`= √(Uᴴ * U)`). -/
theorem eq_mul_sqrt_conjTranspose_mul_self_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) : U = U * CFC.sqrt (Uᴴ * U) := by
  rw [sqrt_conjTranspose_mul_self_of_mem_unitaryGroup hU, mul_one]

/-- **N&C Exercise 2.48, Hermitian case.** The positive factor `√(Hᴴ * H)` of the polar
decomposition of a Hermitian matrix `H` is its absolute value `|H| = √(H ^ 2)`. -/
theorem IsHermitian.sqrt_conjTranspose_mul_self {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    CFC.sqrt (Hᴴ * H) = CFC.sqrt (H ^ 2) := by
  rw [hH.eq, pow_two]

set_option linter.unusedDecidableInType false in
/-- The positive factor `√(Aᴴ * A)` of the polar decomposition equals `A` itself if and only if `A`
is positive semidefinite. In particular, for a Hermitian `H` the polar factor `|H| = √(H ^ 2)`
coincides with `H` exactly when `H` is positive semidefinite. -/
theorem sqrt_conjTranspose_mul_self_eq_self_iff {A : Matrix n n 𝕜} :
    CFC.sqrt (Aᴴ * A) = A ↔ A.PosSemidef := by
  constructor
  · intro h; rw [← h]; exact nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  · exact fun hA => hA.sqrt_conjTranspose_mul_self

/-- The real sign function normalised to take the value `1` at `0` (rather than the usual `0`), so
that `polarSign x * |x| = x` while `polarSign x` is always a unit. Its continuous functional
calculus produces the unitary factor of the polar decomposition of a Hermitian matrix, valid even
in the singular case where `0` is an eigenvalue. -/
noncomputable def polarSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

private lemma polarSign_mul_abs (x : ℝ) : polarSign x * |x| = x := by
  unfold polarSign; split
  · rename_i h; rw [one_mul, abs_of_nonneg h]
  · rename_i h; rw [abs_of_neg (not_le.mp h)]; ring

private lemma polarSign_mul_self (x : ℝ) : polarSign x * polarSign x = 1 := by
  unfold polarSign; split <;> norm_num

/-- The unitary factor of the polar decomposition of a Hermitian matrix `H`: the *sign* of `H`,
`sgn(H) = ∑ⱼ sgn(λⱼ) |j⟩⟨j|` (with `sgn 0 := 1`), realised as the continuous functional calculus
of `polarSign`. It is a genuine unitary for every Hermitian `H` — including the singular case,
where the value `1` chosen at `0` fills in the kernel — and satisfies `H = sgn(H) · |H|`
(`Matrix.IsHermitian.eq_polarUnitary_mul_sqrt_conjTranspose_mul_self`). -/
noncomputable def IsHermitian.polarUnitary {H : Matrix n n 𝕜} (_hH : H.IsHermitian) :
    Matrix n n 𝕜 := cfc polarSign H

/-- **N&C Exercise 2.48, Hermitian case (unitary factor).** The sign factor `sgn(H)` of the polar
decomposition of a Hermitian matrix is unitary. -/
theorem IsHermitian.polarUnitary_mem_unitaryGroup {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    hH.polarUnitary ∈ unitaryGroup n 𝕜 := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ H) :=
    fun f => Matrix.finite_real_spectrum.continuousOn f
  rw [mem_unitaryGroup_iff', IsHermitian.polarUnitary]
  have hstar : star (cfc polarSign H) = cfc polarSign H := by
    rw [← cfc_star]; exact cfc_congr (fun x _ => star_trivial _)
  rw [hstar, ← cfc_mul (R := ℝ) polarSign polarSign H (hcont _) (hcont _),
    show (fun x => polarSign x * polarSign x) = (1 : ℝ → ℝ) from funext polarSign_mul_self]
  exact cfc_one ℝ H

/-- **N&C Exercise 2.48, Hermitian case (decomposition).** A Hermitian matrix `H` factors as
`H = sgn(H) · |H|`: the unitary factor is `hH.polarUnitary = sgn(H)` and the positive factor is
`|H| = √(Hᴴ * H)` (`= √(H ^ 2)`, by `Matrix.IsHermitian.sqrt_conjTranspose_mul_self`). -/
theorem IsHermitian.eq_polarUnitary_mul_sqrt_conjTranspose_mul_self {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) : H = hH.polarUnitary * CFC.sqrt (Hᴴ * H) := by
  have hsa : IsSelfAdjoint H := hH.isSelfAdjoint
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ H) :=
    fun f => Matrix.finite_real_spectrum.continuousOn f
  have hsqrt : CFC.sqrt (Hᴴ * H) = cfc (fun x : ℝ => |x|) H := by
    rw [hH.sqrt_conjTranspose_mul_self]
    have h1 : (0 : Matrix n n 𝕜) ≤ H ^ 2 := by
      rw [sq]; nth_rewrite 1 [← hsa.star_eq]; exact star_mul_self_nonneg H
    have h2 : (0 : Matrix n n 𝕜) ≤ cfc (fun x : ℝ => |x|) H :=
      cfc_nonneg (fun x _ => abs_nonneg x)
    rw [CFC.sqrt_eq_iff (H ^ 2) (cfc (fun x : ℝ => |x|) H) h1 h2,
      ← cfc_mul (R := ℝ) (fun x => |x|) (fun x => |x|) H (hcont _) (hcont _),
      cfc_congr (f := fun x => |x| * |x|) (g := fun x => x ^ 2)
        (fun x _ => by change |x| * |x| = x ^ 2; rw [← sq, sq_abs]),
      show (fun x : ℝ => x ^ 2) = (fun x => (id x) ^ 2) from rfl,
      cfc_pow (R := ℝ) id 2 H (hcont _), cfc_id ℝ H]
  rw [hsqrt, IsHermitian.polarUnitary,
    ← cfc_mul (R := ℝ) polarSign (fun x => |x|) H (hcont _) (hcont _),
    cfc_congr (f := fun x => polarSign x * |x|) (g := id) (fun x _ => polarSign_mul_abs x),
    cfc_id ℝ H]

/-- **N&C Exercise 2.48, Hermitian case (existence form).** Every Hermitian matrix `H` admits a
unitary factor `U` with `H = U · √(Hᴴ * H)`, i.e. the polar decomposition `H = U|H|`. -/
theorem IsHermitian.exists_mem_unitaryGroup_mul_sqrt_conjTranspose_mul_self {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) : ∃ U ∈ unitaryGroup n 𝕜, H = U * CFC.sqrt (Hᴴ * H) :=
  ⟨hH.polarUnitary, hH.polarUnitary_mem_unitaryGroup,
    hH.eq_polarUnitary_mul_sqrt_conjTranspose_mul_self⟩

end Matrix
