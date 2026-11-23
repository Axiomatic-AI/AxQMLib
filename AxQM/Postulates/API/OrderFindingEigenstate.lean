/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Qudit
import AxQM.Concrete.OrderFindingOrbit
import Mathlib.RingTheory.RootsOfUnity.Complex
import ToMathlib.Algebra.Field.GeomSumRootOfUnity
import ToMathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# AxQM.Postulates.API — the order-finding eigenstates `|u_s⟩` and their reconstruction

The eigenstates behind **Nielsen & Chuang Exercise 5.13**. In the order-finding
subroutine (§5.3.1) one fixes a modulus `N` and a residue `x` coprime to `N` (a unit of `ZMod N`) of
multiplicative order `r`, and the unitary `U|y⟩ = |xy mod N⟩`. Its eigenstates (eq. 5.37) are

  `|u_s⟩ = (1/√r) ∑_{k=0}^{r-1} e^{−2πisk/r} |x^k mod N⟩`,  `0 ≤ s ≤ r − 1`.

The statement of Exercise 5.13 is in `AxQM/NC/Ch5/Exercise5_13.lean`; the analogous
`qftInverseFourierImage` development for Exercise 5.5 is in `AxQM/NC/Ch5/Exercise5_5.lean`.
Exercise 5.13 asks one to prove that these eigenstates reconstruct the computational basis states of
the orbit — the "clever observation" (5.44) that lets phase estimation start from the trivially
preparable `|1⟩` rather than an individual `|u_s⟩`:

  `(1/√r) ∑_{s=0}^{r-1} |u_s⟩ = |1⟩`     (5.44)

and, more generally,

  `(1/√r) ∑_{s=0}^{r-1} e^{2πisk/r} |u_s⟩ = |x^k mod N⟩`.   (5.45)

## What is formalised

* `orderEigenstate x s` — the eigenstate `|u_s⟩` as a genuine `PureState (qudit N)`; its
  normalization is the Pythagorean identity `‖(1/√r) ∑_k e^{−2πisk/r}|x^k⟩‖² = (1/r)·r = 1` over the
  orthonormal orbit family (`Orthonormal.norm_sum_smul_sq`).
* `orderEigenstate_reconstruct` — **eq. (5.45)** for every `k : ℕ`, the inverse-DFT reconstruction.
* `orderEigenstate_sum_eq_one` — **eq. (5.44)**, the `k = 0` specialisation (`|x^0 mod N⟩ = |1⟩`).

The orbit-index combinatorics (`Concrete.orbitIndex` and its injectivity/periodicity) is pure
`ZMod`/`Fin` mathematics in `AxQM/Concrete/OrderFindingOrbit.lean`; the computational basis's
orthonormality (`quditBasis_orthonormal`) is in `AxQM/Postulates/API/Qudit.lean`; and the analytic
engine is the root-of-unity orthogonality `geom_sum_eq_ite_of_pow_eq_one`
(`∑_{s<r} ζ^s = r·[ζ=1]` when `ζ^r = 1`), proved in
`ToMathlib/Algebra/Field/GeomSumRootOfUnity.lean`, the finite-dimension analogue of the identity
that makes the QFT matrix unitary (`Concrete.qftMatrix_star_mul_self`).

## Design notes

* **`x` a unit of `ZMod N`.** N&C's "`x` coprime to `N`" is exactly `x : (ZMod N)ˣ`; this makes the
  order `r = orderOf x` positive (`orderOf_pos`, the units group being finite for `[NeZero N]`), so
  `|u_s⟩` is a bona fide normalized state and the `1/√r` factor is meaningful.
* **Faithful generality.** Eq. (5.45) is proved for *every* `k : ℕ` (not merely `k < r`): both sides
  depend on `k` only through `k mod r` (`orbitIndex_mod` on the right, `e^{2πisk/r}` periodicity on
  the left), which is the content of "in fact, prove that …" in the exercise. Eq. (5.44) is its
  `k = 0` case, the state `|x^0 mod N⟩ = |1⟩` (needs `1 < N`, satisfied by every order-finding
  modulus).
-/

noncomputable section

namespace AxQM

open scoped Matrix
open AxQM.Concrete (orbitIndex orbitIndex_fin_injective orbitIndex_mod)

/-- The complex-exponential DFT phase `e^{−2πi ab/r}` has unit modulus (it is `e^{iθ}` for a real
angle `θ`). -/
private theorem norm_exp_dft (a b r : ℕ) :
    ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) * (b : ℂ)) / (r : ℂ)))‖ = 1 := by
  rw [show (-(2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) * (b : ℂ)) / (r : ℂ)))
        = ((-(2 * Real.pi * ((a : ℝ) * (b : ℝ)) / (r : ℝ)) : ℝ) : ℂ) * Complex.I by
      push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- **The order-finding eigenstate** `|u_s⟩ = (1/√r) ∑_{k<r} e^{−2πisk/r} |x^k mod N⟩` of N&C eq.
(5.37), for a unit `x` of `ZMod N` of order `r = orderOf x` and label `s : Fin r`, as a `PureState`
of `qudit N`. It is normalized: the orbit family `{|x^k mod N⟩ : k < r}` is orthonormal
(`orbitIndex_fin_injective`, `quditBasis_orthonormal`) and each amplitude has modulus `1/√r`, so
`‖|u_s⟩‖² = ∑_{k<r} (1/√r)² = r·(1/r) = 1` (`Orthonormal.norm_sum_smul_sq`). -/
def orderEigenstate {N : ℕ} [NeZero N] (x : (ZMod N)ˣ) (s : Fin (orderOf x)) :
    PureState (qudit N) where
  vec := ∑ k : Fin (orderOf x),
    ((Real.sqrt (orderOf x) : ℂ)⁻¹ *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (k : ℕ)) / (orderOf x : ℂ))))
      • (quditBasis (orbitIndex x (k : ℕ))).vec
  normalized := by
    have hr : 0 < orderOf x := orderOf_pos x
    have horth : Orthonormal ℂ (fun k : Fin (orderOf x) =>
        (quditBasis (orbitIndex x (k : ℕ))).vec) :=
      (quditBasis_orthonormal N).comp _ (orbitIndex_fin_injective x)
    have hcoeff : ∀ k : Fin (orderOf x),
        ‖(Real.sqrt (orderOf x) : ℂ)⁻¹ *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (k : ℕ)) /
            (orderOf x : ℂ)))‖ ^ 2 = (orderOf x : ℝ)⁻¹ := by
      intro k
      rw [norm_mul, norm_exp_dft, mul_one, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), ← Real.sqrt_inv, Real.sq_sqrt (by positivity)]
    have hsq : ‖(∑ k : Fin (orderOf x),
        ((Real.sqrt (orderOf x) : ℂ)⁻¹ *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (k : ℕ)) /
            (orderOf x : ℂ)))) • (quditBasis (orbitIndex x (k : ℕ))).vec)‖ ^ 2 = 1 := by
      rw [horth.norm_sum_smul_sq, Finset.sum_congr rfl (fun k _ => hcoeff k)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_inv_cancel₀ (by exact_mod_cast hr.ne')]
    rw [← Real.sqrt_one, ← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- The underlying vector of `orderEigenstate x s` is the explicit DFT superposition
`(1/√r) ∑_{k<r} e^{−2πisk/r} |x^k mod N⟩`. -/
@[simp]
theorem orderEigenstate_vec {N : ℕ} [NeZero N] (x : (ZMod N)ˣ) (s : Fin (orderOf x)) :
    (orderEigenstate x s).vec = ∑ k : Fin (orderOf x),
      ((Real.sqrt (orderOf x) : ℂ)⁻¹ *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (k : ℕ)) / (orderOf x : ℂ))))
        • (quditBasis (orbitIndex x (k : ℕ))).vec :=
  rfl

/-- The inner `s`-sum arising in the reconstruction: with the `1/√r` factors folded in, the phases
`e^{2πisk/r}·e^{−2πisy/r}` sum over `s < r` to `1` when `y ≡ k (mod r)` and `0` otherwise. The
per-`s` term is `ζ^s` for `ζ = ω^k·(ω^y)⁻¹` (`ω = e^{2πi/r}`, a primitive `r`-th root), so the
sum is the root-of-unity geometric sum (`geom_sum_eq_ite_of_pow_eq_one`): it is `r` exactly when
`ω^k = ω^y`, i.e. `k ≡ y (mod r)` (`IsPrimitiveRoot.pow_inj`, `y < r`), and the surviving
`(1/√r)²·r = 1`. -/
private theorem dft_orthogonality {N : ℕ} [NeZero N] (x : (ZMod N)ˣ) (k : ℕ)
    (y : Fin (orderOf x)) :
    ∑ s : Fin (orderOf x),
        (Real.sqrt (orderOf x) : ℂ)⁻¹ *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (k : ℕ)) / (orderOf x : ℂ)) *
          ((Real.sqrt (orderOf x) : ℂ)⁻¹ *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (y : ℕ)) / (orderOf x : ℂ))))
      = if (y : ℕ) = k % orderOf x then 1 else 0 := by
  have hr : 0 < orderOf x := orderOf_pos x
  have hrne : (orderOf x : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  set ω : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (orderOf x : ℂ)) with hωdef
  have hω : IsPrimitiveRoot ω (orderOf x) := Complex.isPrimitiveRoot_exp _ hr.ne'
  have hω0 : ω ≠ 0 := by rw [hωdef]; exact Complex.exp_ne_zero _
  have horder : orderOf ω = orderOf x := IsPrimitiveRoot.iff_orderOf.mp hω
  -- Each phase `e^{2πisk/r}` is `ω ^ (k·s)`; the product is thus `ζ ^ s` with `ζ = ω^k·(ω^y)⁻¹`.
  have hterm : ∀ s : Fin (orderOf x),
      (Real.sqrt (orderOf x) : ℂ)⁻¹ *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (k : ℕ)) / (orderOf x : ℂ)) *
        ((Real.sqrt (orderOf x) : ℂ)⁻¹ *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (y : ℕ)) / (orderOf x : ℂ))))
        = ((Real.sqrt (orderOf x) : ℂ)⁻¹ * (Real.sqrt (orderOf x) : ℂ)⁻¹) *
            (ω ^ k * (ω ^ (y : ℕ))⁻¹) ^ (s : ℕ) := by
    intro s
    have e1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (k : ℕ)) / (orderOf x : ℂ))
        = ω ^ (k * (s : ℕ)) := by rw [hωdef, ← Complex.exp_natCast_mul]; congr 1; push_cast; ring
    have e2 : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (y : ℕ)) /
        (orderOf x : ℂ))) = (ω ^ ((y : ℕ) * (s : ℕ)))⁻¹ := by
      rw [hωdef, ← Complex.exp_natCast_mul, ← Complex.exp_neg]; congr 1; push_cast; ring
    rw [e1, e2, mul_pow, inv_pow, ← pow_mul, ← pow_mul]; ring
  rw [Finset.sum_congr rfl (fun s _ => hterm s), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun s => (ω ^ k * (ω ^ (y : ℕ))⁻¹) ^ s) (orderOf x)]
  have hζr : (ω ^ k * (ω ^ (y : ℕ))⁻¹) ^ orderOf x = 1 := by
    rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm (y : ℕ), pow_mul, pow_mul]
    simp [hω.pow_eq_one]
  rw [geom_sum_eq_ite_of_pow_eq_one hζr]
  have hmod : ω ^ (k % orderOf x) = ω ^ k := by
    conv_lhs => rw [← horder]
    rw [pow_mod_orderOf]
  have hζ1 : (ω ^ k * (ω ^ (y : ℕ))⁻¹ = 1) ↔ (y : ℕ) = k % orderOf x := by
    rw [mul_inv_eq_one₀ (pow_ne_zero _ hω0)]
    constructor
    · intro h
      exact (hω.pow_inj (Nat.mod_lt k hr) y.isLt (hmod.trans h)).symm
    · intro h
      rw [h]; exact hmod.symm
  by_cases hc : (y : ℕ) = k % orderOf x
  · rw [ite_eq_left (hζ1.mpr hc), ite_eq_left hc, ← mul_inv,
      show (Real.sqrt (orderOf x) : ℂ) * (Real.sqrt (orderOf x) : ℂ) = (orderOf x : ℂ) by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_natCast],
      inv_mul_cancel₀ hrne]
  · rw [ite_eq_right (fun h => hc (hζ1.mp h)), ite_eq_right hc, mul_zero]

/-- **Nielsen & Chuang, Exercise 5.13, eq. (5.45).** The order-finding eigenstates reconstruct the
orbit basis states by the inverse discrete Fourier transform: for every `k : ℕ`,

  `(1/√r) ∑_{s<r} e^{2πisk/r} |u_s⟩ = |x^k mod N⟩`.

Substituting the definition of `|u_s⟩`, exchanging the sums, and pulling each orbit vector out of
the `s`-sum, the coefficient is `dft_orthogonality`: `1` when `y ≡ k (mod r)` and `0` otherwise.
Only the term `y = k mod r` survives, giving `|x^{k mod r} mod N⟩ = |x^k mod N⟩`
(`orbitIndex_mod`). -/
theorem orderEigenstate_reconstruct {N : ℕ} [NeZero N] (x : (ZMod N)ˣ) (k : ℕ) :
    ∑ s : Fin (orderOf x),
        ((Real.sqrt (orderOf x) : ℂ)⁻¹ *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s : ℕ) * (k : ℕ)) / (orderOf x : ℂ)))
        • (orderEigenstate x s).vec
      = (quditBasis (orbitIndex x k)).vec := by
  have hr : 0 < orderOf x := orderOf_pos x
  simp only [orderEigenstate_vec, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, dft_orthogonality]
  rw [Finset.sum_eq_single (⟨k % orderOf x, Nat.mod_lt k hr⟩ : Fin (orderOf x))]
  · rw [ite_eq_left rfl, one_smul, orbitIndex_mod]
  · intro y _ hy
    rw [ite_eq_right (fun h => hy (Fin.ext h)), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Nielsen & Chuang, Exercise 5.13, eq. (5.44).** The equal-weight superposition of all order-
finding eigenstates is the trivially preparable computational basis state `|1⟩`:

  `(1/√r) ∑_{s<r} |u_s⟩ = |1⟩`.

This is the `k = 0` case of `orderEigenstate_reconstruct` (`e^{2πis·0/r} = 1`), whose right-hand
side `|x^0 mod N⟩` is `|1⟩` because `x^0 mod N = 1` (`orbitIndex x 0 = 1`, using `1 < N`). It is the
observation that lets phase estimation for order-finding start from `|1⟩` without knowing `r`. -/
theorem orderEigenstate_sum_eq_one {N : ℕ} [NeZero N] (hN : 1 < N) (x : (ZMod N)ˣ) :
    ∑ s : Fin (orderOf x), (Real.sqrt (orderOf x) : ℂ)⁻¹ • (orderEigenstate x s).vec
      = (quditBasis (1 : Fin N)).vec := by
  have : Fact (1 < N) := ⟨hN⟩
  have hidx : orbitIndex x 0 = (1 : Fin N) := by
    apply Fin.ext
    simp only [orbitIndex, pow_zero, ZMod.val_one, Fin.val_one', Nat.mod_eq_of_lt hN]
  have h := orderEigenstate_reconstruct x 0
  rw [hidx] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp

end AxQM
