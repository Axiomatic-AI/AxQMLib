/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Qudit
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.API.QuantumFourierTransform
import AxQM.Postulates.API.InverseQuantumFourierTransform
import AxQM.Postulates.API.QuditMeasurement

/-!
# AxQM.Postulates.API — the period-shift operator and its Fourier eigenstates

The development behind **Nielsen & Chuang Exercise 5.21** (Period-finding and phase
estimation). For a periodic function `f` with period `r` (`f(x+r) = f(x)`), whose `r` value states
`|f(0)⟩, …, |f(r-1)⟩` are distinct and orthonormal, one is given the **shift operator** `U_y`
(N&C's `U_y`) acting by `U_y|f(x)⟩ = |f(x+y)⟩`. Since the `r` value states are orthonormal and `U_y`
cyclically permutes them, they are canonically the computational basis of the `r`-level **period
register** `qudit r`, with `|f(x)⟩ = |x mod r⟩`; the shift is then the cyclic-shift gate
`|x⟩ ↦ |x+y⟩` on `Fin r` (`+` the modular addition of `Fin r`). Its Fourier eigenstates (N&C
eq. 5.63)

  `|f̂(ℓ)⟩ = (1/√r) ∑_{x<r} e^{−2πiℓx/r} |f(x)⟩`

are exactly the inverse quantum Fourier images `F⁻¹|ℓ⟩` (`qftInverseFourierImage r ℓ`).

## What is formalised

* `quditPerm σ` — the general **single-register computational-basis permutation gate** on `qudit d`
  for `σ : Equiv.Perm (Fin d)`, `|x⟩ ↦ |σ x⟩` (the single-register companion of `quditPairPerm`).
* `periodShift r y` — the **shift operator** `U_y` of Exercise 5.21: `quditPerm` of the cyclic shift
  `Equiv.addRight y`, so `U_y|x⟩ = |x+y⟩`. Defined as the raw shift permutation (no reference to the
  Fourier transform), so that its Fourier diagonalisation below is a *theorem*, not a definition.
* `periodShift_op_apply_quditBasis` / `periodShift_evolvePure_quditBasis` — the defining action
  `U_y|x⟩ = |x+y⟩`. This is also **Exercise 5.21(2)'s black box**: applied to a value state
  `|f(x₀)⟩` it realises evaluation of the shifted (same-period) function.
* `periodShift_hasEigenstate_qftInverseFourierImage` — **Exercise 5.21(1)**: the Fourier states
  `|f̂(ℓ)⟩ = F⁻¹|ℓ⟩` are eigenvectors of `U_y`, with eigenvalue `e^{2πiℓy/r}`.
* `quditBasis_eq_sum_qftInverseFourierImage` — **eq. (5.64)**, the inverse identity: a value state
  `|f(x₀)⟩ = |x₀⟩` is the equal-magnitude superposition `(1/√r) ∑_ℓ e^{2πiℓx₀/r} |f̂(ℓ)⟩` of *all*
  eigenstates. This is the key content of Exercise 5.21(2): `|f(x₀)⟩` plays the role that `|1⟩ =
  (1/√r) ∑_s |u_s⟩` plays in order-finding (cf. eq. 5.44), so phase estimation on `U_y` started from
  `|f(x₀)⟩` samples the eigenphases `ℓy/r` and recovers the period `r`.

## Design notes

* **Statements.** The statements of Exercise 5.21 (`periodShift_hasEigenstate_…`) are in
  `AxQM/NC/Ch5/Exercise5_21.lean`.
* **Faithful model.** N&C give `U_y` abstractly by its action on the value states `|f(x)⟩`; on the
  period register those states are the whole computational basis, so `U_y` is *uniquely* the
  cyclic-shift permutation `periodShift r y` — the unique unitary with `U_y|x⟩ = |x+y⟩`. Modelling
  `|f(x)⟩` as `|x mod r⟩` loses nothing: any injective periodic `f` gives the same eigenstructure up
  to the relabelling `|f(x)⟩ ↔ |x mod r⟩`, which is exactly what parts (1)/(2) are about.
* **Eigenvalue proof.** Purely the N&C computation: `U_y|f̂(ℓ)⟩ = (1/√r) ∑_x e^{−2πiℓx/r} |x+y⟩`,
  reindex `x ↦ x+y` (`Fintype.sum_equiv (Equiv.addRight y)`), and the phase picks up the constant
  `e^{2πiℓy/r}` — the modular wrap `e^{−2πiℓ·val(x+y)/r}` agreeing with `e^{−2πiℓ(x+y)/r}` because
  they differ by `e^{2πi·(integer)} = 1` (`Fin.val_add`, `Complex.exp_nat_mul_two_pi_mul_I`).
* **Reconstruction proof.** `|x₀⟩ = F⁻¹(F|x₀⟩)` (`Evolution.evolvePure_adjoint_evolvePure`); then
  `F` produces `∑_ℓ e^{2πiℓx₀/r}|ℓ⟩/√r` (`qftFourierImage`) and `F⁻¹` is expanded over the sum, each
  `F⁻¹|ℓ⟩` being `|f̂(ℓ)⟩` (`qftInverseFourierImage`).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-! ### The single-register computational-basis permutation gate -/

/-- **The single-register computational-basis permutation gate** `quditPerm σ` on `qudit d`, for a
permutation `σ : Equiv.Perm (Fin d)` of the basis labels: the unitary `Evolution` sending each
computational-basis state `|x⟩` to `|σ x⟩`. It is `Evolution.ofLinearIsometryEquiv` of the isometry
`OrthonormalBasis.equiv` permuting the computational orthonormal basis `quditOrthonormalBasis` by
`σ`, with unitarity inherited from that isometry (permuting an orthonormal basis is an isometry).
The single-register companion of `quditPairPerm`. -/
def quditPerm {d : ℕ} (σ : Equiv.Perm (Fin d)) : Evolution (qudit d) :=
  Evolution.ofLinearIsometryEquiv ((quditOrthonormalBasis d).equiv (quditOrthonormalBasis d) σ)

/-- **Action of the permutation gate** on a computational-basis vector:
`quditPerm σ |x⟩ = |σ x⟩`. Follows from the action of an `OrthonormalBasis.equiv` on a basis vector
(`OrthonormalBasis.equiv_apply_basis`), since `|x⟩ = quditOrthonormalBasis d x`
(`quditOrthonormalBasis_apply`). -/
theorem quditPerm_op_apply_quditBasis {d : ℕ} (σ : Equiv.Perm (Fin d)) (x : Fin d) :
    (quditPerm σ).op (quditBasis x).vec = (quditBasis (σ x)).vec := by
  rw [quditPerm, Evolution.ofLinearIsometryEquiv_op_apply, ← quditOrthonormalBasis_apply,
    OrthonormalBasis.equiv_apply_basis, quditOrthonormalBasis_apply]

/-- **Action of the permutation gate on a computational-basis pure state:**
`quditPerm σ |x⟩ = |σ x⟩`. The `evolvePure`-level companion of `quditPerm_op_apply_quditBasis`. -/
theorem quditPerm_evolvePure_quditBasis {d : ℕ} (σ : Equiv.Perm (Fin d)) (x : Fin d) :
    (quditPerm σ).evolvePure (quditBasis x) = quditBasis (σ x) := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, quditPerm_op_apply_quditBasis]

/-! ### The period-shift operator `U_y` -/

/-- **The period-shift operator** `U_y` of Nielsen & Chuang Exercise 5.21, on the period register
`qudit r`: the cyclic-shift gate `|x⟩ ↦ |x+y⟩` (`+` the modular addition of `Fin r`), realised as
`quditPerm` of the shift permutation `Equiv.addRight y`. It is `U_y|f(x)⟩ = |f(x+y)⟩` under the
identification `|f(x)⟩ = |x mod r⟩` of the value states with the computational basis. Defined as the
raw shift permutation — with *no* reference to the Fourier transform — so that its Fourier
diagonalisation (`periodShift_hasEigenstate_qftInverseFourierImage`) is a theorem. -/
def periodShift (r : ℕ) [NeZero r] (y : Fin r) : Evolution (qudit r) :=
  quditPerm (Equiv.addRight y)

/-- **The defining action of the shift operator** `U_y|x⟩ = |x+y⟩` (Nielsen & Chuang Exercise 5.21).
Applied to a value state `|f(x₀)⟩ = |x₀⟩` it produces `|f(x₀+y)⟩ = |x₀+y⟩`, so — with `y` supplied
by a control register — it realises the period-finding black box for the shifted (same-period)
function `g(y) = f(x₀+y)` (part (2)). -/
theorem periodShift_op_apply_quditBasis (r : ℕ) [NeZero r] (y x : Fin r) :
    (periodShift r y).op (quditBasis x).vec = (quditBasis (x + y)).vec := by
  rw [periodShift, quditPerm_op_apply_quditBasis, Equiv.coe_addRight]

/-- **The defining action of the shift operator on a pure state** `U_y|x⟩ = |x+y⟩`. The
`evolvePure`-level companion of `periodShift_op_apply_quditBasis`, and the form of Exercise
5.21(2)'s black box. -/
theorem periodShift_evolvePure_quditBasis (r : ℕ) [NeZero r] (y x : Fin r) :
    (periodShift r y).evolvePure (quditBasis x) = quditBasis (x + y) := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, periodShift_op_apply_quditBasis]

/-- **Conjugation of the standard basis projector by the shift:** `U_y |0⟩⟨0| U_y† = |y⟩⟨y|`. The
cyclic shift `U_y = periodShift r y` sends `|0⟩` to `|y⟩` (`periodShift_evolvePure_quditBasis` at
`x = 0`), so its conjugation action on the density operator `|0⟩⟨0|` — read through
`Evolution.evolve` (`ρ ↦ U ρ U†`) — produces `|y⟩⟨y|`. Reusable whenever the period register is used
as a measuring apparatus that stores an outcome by shifting a reset state `|0⟩` to `|y⟩` (e.g. the
Holevo-bound measurement operation, N&C Exercise 12.2). -/
theorem periodShift_op_conj_quditBasisZero (r : ℕ) [NeZero r] (y : Fin r) :
    (periodShift r y).op.comp
        (((quditBasis (0 : Fin r)).toState.op).comp
          (ContinuousLinearMap.adjoint (periodShift r y).op))
      = (quditBasis y).toState.op := by
  rw [← Evolution.evolve_op, ← toState_evolvePure, periodShift_evolvePure_quditBasis, zero_add]

/-! ### Exercise 5.21(1): the Fourier states are eigenstates of `U_y` -/

/-- The per-mode phase identity behind the eigenvalue computation: for the shift by `y`, the
inverse-Fourier amplitude `(1/√r) e^{−2πiℓx/r}` equals `e^{2πiℓy/r}` times the amplitude at the
shifted index `x+y` (in `Fin r`). Both sides are `(1/√r) e^{iθ}`; the exponents differ by
`2πi·(ℓ·⌊(x+y)/r⌋)`, an integer multiple of `2πi` (`Fin.val_add`,
`Complex.exp_nat_mul_two_pi_mul_I`), which is invisible under `Complex.exp`. -/
private theorem periodShift_phase_shift (r : ℕ) [NeZero r] (y ℓ x : Fin r) :
    (Real.sqrt r : ℂ)⁻¹ * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℕ) * (ℓ : ℕ)) / r))
      = Complex.exp (2 * Real.pi * Complex.I * ((y : ℕ) * (ℓ : ℕ)) / r)
        * ((Real.sqrt r : ℂ)⁻¹
          * Complex.exp
              (-(2 * Real.pi * Complex.I * (((x + y : Fin r) : ℕ) * (ℓ : ℕ)) / r))) := by
  have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  -- The exponentials agree: `e^{−2πixℓ/r} = e^{2πiyℓ/r}·e^{−2πi·val(x+y)·ℓ/r}`. The exponents
  -- differ by `2πi·(⌊(val x + val y)/r⌋·val ℓ)`, an integer multiple of `2πi`, since
  -- `val(x+y) = (val x + val y) − r·⌊(val x + val y)/r⌋` (`Fin.val_add`).
  have hmod : (((x + y : Fin r) : ℕ) : ℂ)
      = ((x : ℕ) : ℂ) + ((y : ℕ) : ℂ)
        - (r : ℂ) * (((((x : ℕ) + (y : ℕ)) / r) : ℕ) : ℂ) := by
    have hnat : ((x + y : Fin r) : ℕ) + r * (((x : ℕ) + (y : ℕ)) / r)
        = (x : ℕ) + (y : ℕ) := by
      rw [Fin.val_add]; exact Nat.mod_add_div _ _
    have hcast : (((x + y : Fin r) : ℕ) : ℂ)
        + (r : ℂ) * (((((x : ℕ) + (y : ℕ)) / r) : ℕ) : ℂ)
        = ((x : ℕ) : ℂ) + ((y : ℕ) : ℂ) := by
      exact_mod_cast hnat
    linear_combination hcast
  have key : Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℕ) * (ℓ : ℕ)) / r))
      = Complex.exp (2 * Real.pi * Complex.I * ((y : ℕ) * (ℓ : ℕ)) / r)
        * Complex.exp (-(2 * Real.pi * Complex.I * (((x + y : Fin r) : ℕ) * (ℓ : ℕ)) / r)) := by
    rw [← Complex.exp_add]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((y : ℕ) * (ℓ : ℕ)) / r
          + -(2 * (Real.pi : ℂ) * Complex.I * (((x + y : Fin r) : ℕ) * (ℓ : ℕ)) / r)
        = -(2 * (Real.pi : ℂ) * Complex.I * ((x : ℕ) * (ℓ : ℕ)) / r)
          + (((((x : ℕ) + (y : ℕ)) / r) * (ℓ : ℕ) : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
        rw [hmod]; push_cast; field_simp; ring,
      Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [key]; ring

/-- **Nielsen & Chuang, Exercise 5.21(1).** The Fourier states `|f̂(ℓ)⟩ = F⁻¹|ℓ⟩`
(`qftInverseFourierImage r ℓ`, N&C eq. 5.63) are the eigenvectors of the shift operator `U_y`
(`periodShift r y`), with eigenvalue `e^{2πiℓy/r}`:

  `U_y |f̂(ℓ)⟩ = e^{2πiℓy/r} |f̂(ℓ)⟩`.

Direct N&C computation: `U_y|f̂(ℓ)⟩ = (1/√r) ∑_x e^{−2πiℓx/r} |x+y⟩`; reindexing the sum by
`x ↦ x+y` (`Fintype.sum_equiv (Equiv.addRight y)`) turns each amplitude into `e^{2πiℓy/r}` times
the amplitude at the original index (`periodShift_phase_shift`), factoring out the constant
`e^{2πiℓy/r}` and returning `|f̂(ℓ)⟩`. -/
theorem periodShift_hasEigenstate_qftInverseFourierImage (r : ℕ) [NeZero r] (y ℓ : Fin r) :
    (periodShift r y).HasEigenstate
      (Complex.exp (2 * Real.pi * Complex.I * ((y : ℕ) * (ℓ : ℕ)) / r))
      (qftInverseFourierImage r ℓ) := by
  change (periodShift r y).op (qftInverseFourierImage r ℓ).vec
    = Complex.exp (2 * Real.pi * Complex.I * ((y : ℕ) * (ℓ : ℕ)) / r)
        • (qftInverseFourierImage r ℓ).vec
  rw [qftInverseFourierImage_vec, map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.addRight y)
    (fun x => (periodShift r y).op (((Real.sqrt r : ℂ)⁻¹
        * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℕ) * (ℓ : ℕ)) / r)))
      • (quditBasis x).vec))
    (fun x => Complex.exp (2 * Real.pi * Complex.I * ((y : ℕ) * (ℓ : ℕ)) / r)
      • (((Real.sqrt r : ℂ)⁻¹
          * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℕ) * (ℓ : ℕ)) / r)))
        • (quditBasis x).vec)) ?_
  intro x
  simp only [Equiv.coe_addRight]
  rw [map_smul, periodShift_op_apply_quditBasis, smul_smul, periodShift_phase_shift r y ℓ x]

/-! ### Exercise 5.21(2): the value state is a uniform superposition of eigenstates -/

/-- **Nielsen & Chuang, Exercise 5.21(2) / eq. (5.64).** A value state `|f(x₀)⟩ = |x₀⟩` is the
equal-magnitude superposition of *all* Fourier eigenstates `|f̂(ℓ)⟩`:

  `|f(x₀)⟩ = (1/√r) ∑_ℓ e^{2πiℓx₀/r} |f̂(ℓ)⟩`.

This is the inverse of eq. (5.63) and the crux of part (2): each `|f̂(ℓ)⟩` appears with amplitude of
modulus `1/√r`, so `|f(x₀)⟩` is to `U_y` what `|1⟩ = (1/√r) ∑_s |u_s⟩` (eq. 5.44) is to the
order-finding operator — a single, trivially preparable state that is an equal superposition of
every eigenstate. Phase estimation on `U_y` started from `|f(x₀)⟩` therefore samples the eigenphases
`ℓy/r` (from `periodShift_hasEigenstate_qftInverseFourierImage`) and recovers the period `r`.

Proof: `|x₀⟩ = F⁻¹(F|x₀⟩)` (`Evolution.evolvePure_adjoint_evolvePure`, as
`qftInverseEvolution = F†`); `F|x₀⟩ = (1/√r) ∑_ℓ e^{2πiℓx₀/r}|ℓ⟩` (`qftFourierImage`); and expanding
`F⁻¹` over the sum sends each `|ℓ⟩` to `F⁻¹|ℓ⟩ = |f̂(ℓ)⟩`. -/
theorem quditBasis_eq_sum_qftInverseFourierImage (r : ℕ) [NeZero r] (x₀ : Fin r) :
    (quditBasis x₀).vec
      = ∑ ℓ : Fin r, ((Real.sqrt r : ℂ)⁻¹
          * Complex.exp (2 * Real.pi * Complex.I * ((x₀ : ℕ) * (ℓ : ℕ)) / r))
          • (qftInverseFourierImage r ℓ).vec := by
  have hround : (qftInverseEvolution r).evolvePure (qftFourierImage r x₀) = quditBasis x₀ := by
    rw [← qftEvolution_evolvePure_quditBasis]
    exact Evolution.evolvePure_adjoint_evolvePure (qftEvolution r) (quditBasis x₀)
  have hvec : (qftInverseEvolution r).op ((qftFourierImage r x₀).vec) = (quditBasis x₀).vec := by
    have h := congrArg PureState.vec hround
    rwa [Evolution.evolvePure_vec] at h
  rw [← hvec, qftFourierImage_vec, map_sum]
  refine Finset.sum_congr rfl (fun ℓ _ => ?_)
  rw [map_smul]
  congr 1
  rw [qftInverseEvolution_op_apply_quditBasis, ← qftInverseFourierImage_vec]

end AxQM
