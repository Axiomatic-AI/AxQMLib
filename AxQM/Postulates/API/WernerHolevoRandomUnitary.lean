/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.WernerHolevoChannel
import AxQM.Concrete.AntisymmetricDet
import ToMathlib.Analysis.InnerProductSpace.EuclideanConjVec
import ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM

/-!
# AxQM.Postulates.API — the Werner–Holevo channel is not random-unitary

The **larger-system counterexample of Nielsen & Chuang, Problem 8.3** (Landau & Streater): the
qutrit **Werner–Holevo channel** `Φ(ρ) = ½(tr(ρ)·I − ρᵀ)` (`wernerHolevoChannel`, shown to be a
*unital CPTP channel* in `WernerHolevoChannel.lean`) is **not** a random-unitary average
`∑ₖ pₖ Uₖ ρ Uₖ†`. The statements `¬ IsRandomUnitary wernerHolevoChannel` and
`∃ unital channel that is not random-unitary` are in `AxQM/NC/Ch8/Problem8_3.lean`; this file
supplies the sesquilinear computation used in their proof.

## The argument

Suppose `Φ = ∑ₖ pₖ Uₖ ρ Uₖ†` for a `RandomUnitaryChannel` `C`. Evaluate both sides on a **pure
state** `ρ = |ψ⟩⟨ψ|` and pair with the conjugate vector `ψ̄` (`pureConjVec`, i.e.
`EuclideanSpace.conjVec` of `ψ.vec`):

* `wernerHolevoChannel_inner_conjVec_eq_zero` — the Werner–Holevo side vanishes,
  `⟨ψ̄, Φ(|ψ⟩⟨ψ|) ψ̄⟩ = 0`, because `Φ(|ψ⟩⟨ψ|) = ½(I − |ψ̄⟩⟨ψ̄|)` and `‖ψ̄‖ = ‖ψ‖ = 1`.
* `inner_evolve_toState_op_eq_normSq` — each random-unitary term is a nonnegative square,
  `⟨ψ̄, Uₖ |ψ⟩⟨ψ| Uₖ† ψ̄⟩ = ‖⟨ψ̄, Uₖ ψ⟩‖²`.
* `RandomUnitaryChannel.inner_apply_op_eq_sum` — the sesquilinear form is additive over the mixture.
* `RandomUnitaryChannel.sum_prob_normSq_eq_zero_of_apply_eq_wernerHolevoChannel` — assembling the
  three, `∑ₖ pₖ ‖⟨ψ̄, Uₖ ψ⟩‖² = 0` for every pure state `ψ`.

Since the `pₖ` sum to one, some `pₖ₀ > 0`, forcing `⟨ψ̄, Uₖ₀ ψ⟩ = ψᵀ Uₖ₀ ψ = 0` for **every** unit
`ψ`, hence every `ψ`. But:

* `Evolution.not_forall_inner_conjVec_op_eq_zero` — no unitary `U` on the qutrit can satisfy
  `⟨ψ̄, U ψ⟩ = 0` for all `ψ`: that would make its matrix antisymmetric
  (`Concrete.transpose_eq_neg_of_forall_dotProduct_mulVec_self_eq_zero`), and an antisymmetric
  matrix in **odd** dimension is singular (`Concrete.det_eq_zero_of_transpose_eq_neg`),
  contradicting unitarity (`Concrete.not_forall_dotProduct_mulVec_self_eq_zero_of_isUnit_det`).

This is the contradiction. The odd dimension is essential — for a qubit (dimension `2`) *every*
unital channel is random-unitary (see `AxQM/NC/Ch8/Problem8_3.lean`); the obstruction appears
only for `d ≥ 3`.

## Design note — `pureConjVec`

The conjugate vector `ψ̄` is `EuclideanSpace.conjVec ψ.vec`, whose *declared* type is
`EuclideanSpace ℂ (Fin 3)`, while the operators of `qudit 3` act on `(qudit 3).space`. Those two
types are definitionally equal but not syntactically, so an inner product written on the bare
`ψ.vec.conjVec` carries a different (Euclidean) type-argument than one written on a
`(qudit 3).space` vector, which blocks `rw` from matching the two. `pureConjVec ψ : (qudit 3).space`
pins the
type-argument to the system space uniformly, so the sesquilinear identities compose by `rw`; the
Euclidean-coordinate lemmas are reached through its definitional unfolding.
-/

open Matrix InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder Matrix ComplexConjugate

noncomputable section

namespace AxQM

/-- **The conjugate vector `ψ̄` of a pure state**, `EuclideanSpace.conjVec ψ.vec`, typed in the
system space `(qudit 3).space`. Pairing the operator identities of Problem 8.3 against `ψ̄` turns
the Werner–Holevo transpose `ρᵀ` into the conjugate projector `|ψ̄⟩⟨ψ̄|` and the unitary matrix
element `⟨ψ̄, U ψ⟩` into the coordinate bilinear form `ψᵀ U ψ`. Its declared type pins the
inner-product type-argument to the system space (see the module design note). -/
def pureConjVec (ψ : PureState (qudit 3)) : (qudit 3).space := ψ.vec.conjVec

/-- **A unitary conjugation of a pure state has a square sesquilinear form.** For a unitary
evolution `U`, a pure state `|ψ⟩⟨ψ|` and *any* vector `φ`, `⟨φ, U |ψ⟩⟨ψ| U† φ⟩ = ‖⟨φ, U ψ⟩‖²` — the
matrix element `⟨φ, (U.evolve ψ.toState).op φ⟩` factors as
`⟨ψ, U† φ⟩ · ⟨φ, U ψ⟩ = conj⟨φ, U ψ⟩ · ⟨φ, U ψ⟩`. This is each summand of a random-unitary channel's
sesquilinear form; at `φ = ψ̄` it is `‖ψᵀ U ψ‖²`, the quantity Problem 8.3's counterexample forces
to zero. -/
theorem inner_evolve_toState_op_eq_normSq (U : Evolution (qudit 3)) (ψ : PureState (qudit 3))
    (φ : (qudit 3).space) :
    (inner ℂ φ ((U.evolve ψ.toState).op φ) : ℂ)
      = ((‖(inner ℂ φ (U.op ψ.vec) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [Evolution.evolve_op, PureState.toState_op, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply, map_smul, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right, ← conj_inner_symm (U.op ψ.vec) φ, RCLike.conj_mul]
  norm_cast

/-- **The Werner–Holevo side vanishes on a conjugated pure state:** `⟨ψ̄, Φ(|ψ⟩⟨ψ|) ψ̄⟩ = 0`, where
`ψ̄ = ψ.vec.conjVec`. From the closed form `Φ(ρ) = ½(tr(ρ)·I − ρᵀ)` (`wernerHolevoChannel_op`), on
the pure-state matrix `M = |ψ⟩⟨ψ|` (`Matrix.vecMulVec ψ (star ψ)`) the output acts on `ψ̄`
(coordinate vector `star ψ`) as `½(tr(M)·star ψ − Mᵀ (star ψ)) = ½(star ψ − star ψ) = 0`, using
`tr(M) = ⟨ψ,ψ⟩ = 1` and `Mᵀ (star ψ) = (ψ ⬝ᵥ star ψ)·star ψ = star ψ`. -/
theorem wernerHolevoChannel_inner_conjVec_eq_zero (ψ : PureState (qudit 3)) :
    (inner ℂ ψ.vec.conjVec ((wernerHolevoChannel ψ.toState).op ψ.vec.conjVec) : ℂ) = 0 := by
  have hM : ψ.toState.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)
      (Matrix.vecMulVec ψ.vec.ofLp (star ψ.vec.ofLp)) := by
    rw [PureState.toState_op]; exact (Matrix.toEuclideanCLM_vecMulVec ψ.vec ψ.vec).symm
  have hadot : ψ.vec.ofLp ⬝ᵥ star ψ.vec.ofLp = 1 := by
    have hself : (inner ℂ ψ.vec ψ.vec : ℂ) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, ψ.normalized]; norm_num
    erw [← EuclideanSpace.inner_eq_star_dotProduct]; exact hself
  have hbr : ((wernerHolevoChannel ψ.toState).op ψ.vec.conjVec).ofLp
      = ((2 : ℂ)⁻¹ • ((Matrix.vecMulVec ψ.vec.ofLp (star ψ.vec.ofLp)).trace •
          (1 : Matrix (Fin 3) (Fin 3) ℂ) - (Matrix.vecMulVec ψ.vec.ofLp (star ψ.vec.ofLp))ᵀ)).mulVec
          ψ.vec.conjVec.ofLp := by
    rw [wernerHolevoChannel_op ψ.toState hM]
    exact Matrix.ofLp_toEuclideanCLM _ ψ.vec.conjVec
  erw [EuclideanSpace.inner_eq_star_dotProduct, hbr, EuclideanSpace.ofLp_conjVec, star_star,
    Matrix.trace_vecMulVec, hadot, one_smul, Matrix.transpose_vecMulVec,
    smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    IsCentralScalar.op_smul_eq_smul, hadot, one_smul, sub_self, smul_zero, zero_dotProduct]

/-- **A random-unitary realisation of the Werner–Holevo channel forces every per-unitary square to
sum to zero:** if `C.apply ρ = Φ(ρ)` for all `ρ`, then for every pure state `ψ` (writing `ψ̄` for
`pureConjVec ψ`), `∑ₖ pₖ ‖⟨ψ̄, Uₖ ψ⟩‖² = 0`. Equating `⟨ψ̄, C(|ψ⟩⟨ψ|) ψ̄⟩` — expanded by
`RandomUnitaryChannel.inner_apply_op_eq_sum` and `inner_evolve_toState_op_eq_normSq` to
`∑ₖ pₖ ‖⟨ψ̄, Uₖ ψ⟩‖²` — with `⟨ψ̄, Φ(|ψ⟩⟨ψ|) ψ̄⟩ = 0`
(`wernerHolevoChannel_inner_conjVec_eq_zero`). -/
theorem RandomUnitaryChannel.sum_prob_normSq_eq_zero_of_apply_eq_wernerHolevoChannel
    (C : RandomUnitaryChannel (qudit 3)) (hC : ∀ ρ, C.apply ρ = wernerHolevoChannel ρ)
    (ψ : PureState (qudit 3)) :
    ∑ k, C.prob k * ‖(inner ℂ (pureConjVec ψ) ((C.unitary k).op ψ.vec) : ℂ)‖ ^ 2 = 0 := by
  have h0 : (inner ℂ (pureConjVec ψ) ((C.apply ψ.toState).op (pureConjVec ψ)) : ℂ) = 0 := by
    rw [hC]; exact wernerHolevoChannel_inner_conjVec_eq_zero ψ
  rw [RandomUnitaryChannel.inner_apply_op_eq_sum C ψ.toState (pureConjVec ψ)] at h0
  simp only [inner_evolve_toState_op_eq_normSq] at h0
  exact_mod_cast h0

/-- **No qutrit unitary conjugation annihilates every conjugated pure state:** for a unitary
evolution `U` of `qudit 3` it is *not* the case that `⟨ψ̄, U ψ⟩ = 0` for all pure states `ψ`
(`ψ̄ = pureConjVec ψ`). Writing `N` for the matrix of `U`, `⟨ψ̄, U ψ⟩ = ψ ⬝ᵥ N ψ`, so the hypothesis
would make the quadratic form `v ⬝ᵥ N v` vanish on every unit vector, hence (by homogeneity) every
vector; but `N` is unitary — `IsUnit N.det` — and no odd-dimensional matrix with invertible
determinant can have an identically-vanishing quadratic form
(`Concrete.not_forall_dotProduct_mulVec_self_eq_zero_of_isUnit_det`). This is the odd-dimension
obstruction at the heart of the Werner–Holevo counterexample. -/
theorem Evolution.not_forall_inner_conjVec_op_eq_zero (U : Evolution (qudit 3)) :
    ¬ ∀ (ψ : PureState (qudit 3)), (inner ℂ (pureConjVec ψ) (U.op ψ.vec) : ℂ) = 0 := by
  intro hzero
  set N := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)).symm U.op with hN
  have hUN : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3) N = U.op :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)).apply_symm_apply U.op
  -- `N` is a unitary matrix, hence `IsUnit N.det`.
  have hstar : (star U.op) * U.op = 1 := (Unitary.mem_iff.mp U.unitary).1
  have hmat : Nᴴ * N = 1 :=
    calc Nᴴ * N
        = (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)).symm (star U.op) * N := by
          rw [hN, ← Matrix.star_eq_conjTranspose]
          erw [← map_star]
      _ = (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)).symm (star U.op * U.op) :=
          (map_mul _ _ _).symm
      _ = 1 := by rw [hstar]; exact map_one _
  have hdetU : IsUnit N.det := by
    have hdet : N.det * Nᴴ.det = 1 := by rw [mul_comm, ← Matrix.det_mul, hmat, Matrix.det_one]
    exact isUnit_iff_ne_zero.mpr (fun h => by rw [h, zero_mul] at hdet; exact zero_ne_one hdet)
  -- The hypothesis, read on the coordinate track, is `ψ ⬝ᵥ N ψ = 0` for every pure state.
  have hquad : ∀ (ψ : PureState (qudit 3)), ψ.vec.ofLp ⬝ᵥ N.mulVec ψ.vec.ofLp = 0 := by
    intro ψ
    have hbr : (U.op ψ.vec).ofLp = N.mulVec ψ.vec.ofLp := by
      rw [← hUN]; exact Matrix.ofLp_toEuclideanCLM N ψ.vec
    have heq : (inner ℂ ψ.vec.conjVec (U.op ψ.vec) : ℂ) = (N.mulVec ψ.vec.ofLp) ⬝ᵥ ψ.vec.ofLp := by
      erw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.ofLp_conjVec, star_star, hbr]
    have hz : (N.mulVec ψ.vec.ofLp) ⬝ᵥ ψ.vec.ofLp = 0 := by rw [← heq]; exact hzero ψ
    rw [dotProduct_comm]; exact hz
  -- Extend the vanishing quadratic form from unit vectors to all vectors by homogeneity.
  have hall : ∀ (v : Fin 3 → ℂ), v ⬝ᵥ N.mulVec v = 0 := by
    intro v
    rcases eq_or_ne (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 3)) 0 with hv | hv
    · have hv0 : v = 0 := by have := congrArg WithLp.ofLp hv; simpa using this
      simp [hv0]
    · have hxn : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 3))‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      set c : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 3))‖ with hc
      have hnorm1 : ‖((c⁻¹ : ℝ) : ℂ) • (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 3))‖ = 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          inv_mul_cancel₀ hxn]
      set ψ : PureState (qudit 3) := ⟨((c⁻¹ : ℝ) : ℂ) • (WithLp.toLp 2 v), hnorm1⟩ with hψ
      have hψvec : ψ.vec.ofLp = ((c⁻¹ : ℝ) : ℂ) • v := by
        change (((c⁻¹ : ℝ) : ℂ) • (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 3))).ofLp = _
        rw [WithLp.ofLp_smul, WithLp.ofLp_toLp]
      have hq := hquad ψ
      rw [hψvec, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        smul_eq_mul] at hq
      have hcne : ((c⁻¹ : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]; exact hxn
      exact (mul_eq_zero.mp (by rw [← mul_assoc] at hq; exact hq)).resolve_left
        (mul_ne_zero hcne hcne)
  exact Concrete.not_forall_dotProduct_mulVec_self_eq_zero_of_isUnit_det
    (by decide : Odd (Fintype.card (Fin 3))) hdetU hall

end AxQM
