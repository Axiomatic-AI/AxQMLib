/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum

/-!
# Concrete: the `d`-dimensional quantum Fourier transform matrix and its unitarity

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §5.1 (eq. 5.2) defines the
**quantum Fourier transform** on an orthonormal basis `|0⟩, …, |d-1⟩` by its action on basis
states,

```
        1  d-1
|j⟩ ↦ ────  Σ   e^{2πi jk/d} |k⟩ .          (5.2)
       √d  k=0
```

The corresponding `d × d` matrix `F` (column `j` = image of `|j⟩`) therefore has entries

```
  Fₖⱼ = (1/√d) · e^{2πi jk/d} ,
```

and N&C remark that this transformation "is a unitary transformation, and thus can be implemented
as the dynamics for a quantum computer" (the direct unitarity check is Exercise 5.1). This file
provides that matrix and a **direct proof that it is unitary**, for a general dimension `d ≥ 1`.

## What is formalised

* `qftPrimitiveRoot d = e^{2πi/d}` — the primitive `d`-th root of unity generating the transform
  (`Complex.isPrimitiveRoot_exp`).
* `qftMatrix d` — the matrix `Fₖⱼ = (1/√d) · ω^{jk}` (`ω = qftPrimitiveRoot d`), with
  `qftMatrix_apply` re-expressing the entry in the literal `(1/√d) · e^{2πi jk/d}` form of (5.2).
* `qftMatrix_star_mul_self` — `F† F = 1`, and hence `qftMatrix_mem_unitaryGroup` —
  `F ∈ Matrix.unitaryGroup (Fin d) ℂ`.

## Proof of unitarity

The `(i, j)` entry of `F† F` is `∑ₖ conj(Fₖᵢ) Fₖⱼ = (1/d) ∑ₖ ω^{(j-i)k} = (1/d) ∑ₖ ζ^k`, where
`ζ = (ω^i)⁻¹ ω^j`. Two cases:

* `i = j`: `ζ = 1`, so `∑ₖ ζ^k = d` and the entry is `(1/d)·d = 1` (using `(√d)² = d`).
* `i ≠ j`: `ζ ≠ 1` because `ω` is a primitive `d`-th root, so `ω^i = ω^j` forces `i = j`
  (`IsPrimitiveRoot.pow_inj`); and `ζ^d = 1`, so the geometric sum `∑_{k<d} ζ^k = (ζ^d-1)/(ζ-1)`
  (`geom_sum_eq`) vanishes and the entry is `0`.

The only complex-conjugation input is `conj ω = ω⁻¹` (`qftPrimitiveRoot_conj`, from `conj(e^z) =
e^{conj z}` and `e^{-z} = (e^z)⁻¹`).

## Design notes

* **Physics wrapper.** A unitary `Evolution` on the qudit `qudit d`, with the (5.2) action on
  `quditBasis`, is built on top of this matrix; Nielsen & Chuang Problem 5.1 cites it.
* **`Fin d` indexing.** The matrix is indexed by `Fin d` (not `ZMod d`) so it transports directly
  to the qudit space `EuclideanSpace ℂ (Fin d)` via `Matrix.toEuclideanCLM`.
* **General `d`.** Unitarity holds for every dimension `d ≥ 1`; Problem 5.1's restriction to `p`
  prime concerns only the *efficient gate-level decomposition* of the circuit, not the transform
  itself, so the reusable mathematics is stated in full generality.
-/

namespace AxQM.Concrete

open Complex
open scoped Matrix

/-- The **primitive `d`-th root of unity** `ω = e^{2πi/d}` generating the `d`-dimensional quantum
Fourier transform. For `d ≥ 1` it is a primitive `d`-th root of unity
(`Complex.isPrimitiveRoot_exp`). -/
noncomputable def qftPrimitiveRoot (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)

/-- The **`d`-dimensional quantum Fourier transform matrix** (Nielsen & Chuang eq. 5.2), with
`(k, j)` entry `Fₖⱼ = (1/√d) · ω^{jk}` for `ω = qftPrimitiveRoot d`. Column `j` is the image of the
basis vector `|j⟩` under the transform; `qftMatrix_apply` gives the entry in the literal
`(1/√d) · e^{2πi jk/d}` form. -/
noncomputable def qftMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun k j => (Real.sqrt d : ℂ)⁻¹ * qftPrimitiveRoot d ^ ((j : ℕ) * (k : ℕ))

/-- The quantum Fourier transform entry in the **literal exponential form** of Nielsen & Chuang
eq. (5.2): `Fₖⱼ = (1/√d) · e^{2πi jk/d}`. This unfolds the `ω^{jk}` power of `qftMatrix` back to
`e^{2πi jk/d}` (`Complex.exp_natCast_mul`). -/
theorem qftMatrix_apply (d : ℕ) (k j : Fin d) :
    qftMatrix d k j
      = (Real.sqrt d : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / d) := by
  rw [qftMatrix, qftPrimitiveRoot, ← Complex.exp_natCast_mul]
  congr 2
  push_cast
  ring

/-- **Conjugate-transpose entry of the quantum Fourier transform matrix:**
`(Fᴴ)ⱼₖ = (1/√d) · e^{−2πi jk/d}` — the forward entry `qftMatrix_apply` conjugated, i.e. the
inverse-DFT amplitude. Since `(Fᴴ)ⱼₖ = conj(Fₖⱼ)`, `conj((1/√d)) = 1/√d` (real) and
`conj(e^{2πi jk/d}) = e^{conj(2πi jk/d)} = e^{−2πi jk/d}`. The `Concrete` companion of
`qftMatrix_apply` used to realize the inverse quantum Fourier transform (Nielsen & Chuang
Exercise 5.5). -/
theorem qftMatrix_conjTranspose_apply (d : ℕ) (j k : Fin d) :
    (qftMatrix d)ᴴ j k
      = (Real.sqrt d : ℂ)⁻¹
        * Complex.exp (-(2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / d)) := by
  rw [Matrix.conjTranspose_apply, qftMatrix_apply, ← starRingEnd_apply, map_mul]
  congr 1
  · rw [map_inv₀, Complex.conj_ofReal]
  · rw [← Complex.exp_conj]
    congr 1
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast, map_ofNat]
    ring

/-- The generating root of unity is closed under conjugation with `conj ω = ω⁻¹`: from
`conj(e^z) = e^{conj z}` and `conj(2πi/d) = -(2πi/d)`, so `conj ω = e^{-2πi/d} = ω⁻¹`. This is the
only complex-conjugation fact used in the unitarity proof. -/
theorem qftPrimitiveRoot_conj (d : ℕ) :
    (starRingEnd ℂ) (qftPrimitiveRoot d) = (qftPrimitiveRoot d)⁻¹ := by
  rw [qftPrimitiveRoot, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    Complex.conj_natCast]
  ring

/-- Conjugation of the generating root, in `star` form: `star ω = ω⁻¹`
(`qftPrimitiveRoot_conj` restated via `starRingEnd_apply`). -/
theorem qftPrimitiveRoot_star (d : ℕ) :
    star (qftPrimitiveRoot d) = (qftPrimitiveRoot d)⁻¹ := by
  rw [← starRingEnd_apply]; exact qftPrimitiveRoot_conj d

/-- **The quantum Fourier transform matrix is an isometry:** `F† F = 1`. Entrywise this is the
root-of-unity orthogonality `(1/d) ∑ₖ ζ^k = δᵢⱼ` with `ζ = (ω^i)⁻¹ ω^j`: for `i = j`, `ζ = 1` and
the sum is `d`; for `i ≠ j`, `ζ ≠ 1` (primitivity, `IsPrimitiveRoot.pow_inj`) and `ζ^d = 1`, so the
geometric sum vanishes (`geom_sum_eq`). -/
theorem qftMatrix_star_mul_self (d : ℕ) [NeZero d] :
    star (qftMatrix d) * qftMatrix d = 1 := by
  have hd : (d : ℕ) ≠ 0 := NeZero.ne d
  have hω : IsPrimitiveRoot (qftPrimitiveRoot d) d := Complex.isPrimitiveRoot_exp d hd
  have hω0 : qftPrimitiveRoot d ≠ 0 := by rw [qftPrimitiveRoot]; exact Complex.exp_ne_zero _
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin d,
      (star (qftMatrix d)) i k * qftMatrix d k j
        = (Real.sqrt d : ℂ)⁻¹ * (Real.sqrt d : ℂ)⁻¹
          * ((qftPrimitiveRoot d ^ (i : ℕ))⁻¹ * qftPrimitiveRoot d ^ (j : ℕ)) ^ (k : ℕ) := by
    intro k
    rw [Matrix.star_apply]
    simp only [qftMatrix, star_mul', star_pow, star_inv₀, qftPrimitiveRoot_star,
      Complex.star_def, Complex.conj_ofReal, mul_pow, inv_pow, ← pow_mul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => ((qftPrimitiveRoot d ^ (i : ℕ))⁻¹ * qftPrimitiveRoot d ^ (j : ℕ)) ^ k) d]
  set ζ : ℂ := (qftPrimitiveRoot d ^ (i : ℕ))⁻¹ * qftPrimitiveRoot d ^ (j : ℕ) with hζ
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hsq : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_natCast]
  by_cases hij : i = j
  · subst hij
    have hz1 : ζ = 1 := by rw [hζ]; exact inv_mul_cancel₀ (pow_ne_zero _ hω0)
    rw [hz1, ite_eq_left rfl]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [← mul_inv, hsq, inv_mul_cancel₀ hd0]
  · have hζ1 : ζ ≠ 1 := by
      rw [hζ]
      intro h
      rw [inv_mul_eq_one₀ (pow_ne_zero _ hω0)] at h
      exact hij (Fin.ext (hω.pow_inj i.isLt j.isLt h))
    have hζd : ζ ^ d = 1 := by
      rw [hζ, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (i : ℕ) d, mul_comm (j : ℕ) d,
        pow_mul, pow_mul]
      simp [hω.pow_eq_one]
    rw [geom_sum_eq hζ1 d, hζd, sub_self, zero_div, mul_zero, ite_eq_right hij]

/-- **The quantum Fourier transform matrix is unitary:** `F ∈ Matrix.unitaryGroup (Fin d) ℂ`
(Nielsen & Chuang, Exercise 5.1 / the unitarity underlying Problem 5.1), from `F† F = 1`
(`qftMatrix_star_mul_self`). -/
theorem qftMatrix_mem_unitaryGroup (d : ℕ) [NeZero d] :
    qftMatrix d ∈ Matrix.unitaryGroup (Fin d) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (qftMatrix_star_mul_self d)

end AxQM.Concrete
