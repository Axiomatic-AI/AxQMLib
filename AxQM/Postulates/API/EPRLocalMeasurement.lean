/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EigenspaceCollapse
import AxQM.Postulates.API.BellState
import AxQM.Postulates.API.RelativePhase

/-!
# AxQM.Postulates.API — measuring one half of an EPR pair collapses the other

The development behind **Nielsen & Chuang, Exercise 12.37** (§12.6.5, p. 598): a
local measurement of *one* qubit of the maximally entangled Bell state
`|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` (`bellPhiPlus`) collapses the *other* qubit into an eigenstate of the
measured observable, determined by the outcome.

## The general collapse lemma

Everything is driven by one reusable computation, keyed on an arbitrary single-qubit `±1`
observable `A` (`A² = I`) and a pair of eigenstates `ψp`, `ψm` (`A ψp = ψp`, `A ψm = −ψm`) that
"diagonalise the Bell vector":

  `bellVec = |ψp⟩⊗|ψp⟩ + |ψm⟩⊗|ψm⟩`.        (`hbell`)

This is the basis-independence of the maximally entangled state (N&C Exercise 12.36): it holds for
the computational basis by definition of `bellVec`, and for the `X` basis `{|+⟩, |-⟩}` by
`bellVec_eq_plusMinus`. Given it, `A ⊗ I` acts on `bellVec` by flipping the sign of the `ψm` branch
(`tmul_id_op_bellVec`), so the `±1` eigenprojectors `P± = (I ± A⊗I)/2` send `|Φ⁺⟩` to

  `P₊ |Φ⁺⟩ = (√2)⁻¹ |ψp⟩⊗|ψp⟩`,   `P₋ |Φ⁺⟩ = (√2)⁻¹ |ψm⟩⊗|ψm⟩`

(`projPlus_tmul_id_bellPhiPlus`, `projMinus_tmul_id_bellPhiPlus`): `I + A⊗I` doubles `ψp⊗ψp` and
kills `ψm⊗ψm`, and dually for `I − A⊗I`. Normalising, the two collapsed states are exactly the
product states `ψp⊗ψp`, `ψm⊗ψm` (`postMeasPlus_tmul_id_bellPhiPlus`,
`postMeasMinus_tmul_id_bellPhiPlus`) — **the second qubit is left in the corresponding eigenstate**
— and each outcome has probability `‖P±|Φ⁺⟩‖² = ½`
(`bornProb_signMeasurement_plus/minus_tmul_id_bellPhiPlus`): the collapse is into a *random*
eigenstate.

The `X`- and `Z`-basis measurements themselves are packaged as the two named measurements
`eprMeasureFirstX`, `eprMeasureFirstZ : Measurement (Fin 2) (qubit ⊗ qubit)` — the projective
measurement of the observable `X ⊗ I` (resp. `Z ⊗ I`), i.e. "measure the first qubit in the `X`
(resp. `Z`) basis". The statement of Exercise 12.37, in terms of `Measurement.postMeasurement` and
`Measurement.bornProb`, is in `AxQM/NC/Ch12/Exercise12_37.lean`.

## Design note — the tensor-space instance diamond

Linear-algebra automation (`module`, `match_scalars`) is unreliable on `(qubit ⊗ qubit).space`
because its `Module ℂ` instance (via the bundled `QSystem.space`) is a *different* term from the
canonical `TensorProduct.instModule`, even though the two are definitionally equal. The two `module`
helper lemmas below (`two_inv_smul_add_diag`, `two_inv_smul_sub_diag`) are proved over an
*abstract* `Module ℂ M`, where `module` sees the canonical instance and succeeds; they are then
applied with `exact`, whose defeq check bridges the diamond. The eigenvalue-action computation is
routed through the raw `TensorProduct.mapL` head (`change`) for the same reason.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-! ### Abstract `module` helpers (applied via `exact`; see the design note) -/

/-- The `+1`-eigenprojector arithmetic, abstractly: `½·(s(P+Q) + s(P−Q)) = sP`, since the `Q`
branch cancels and the `P` branch doubles. Proved by `module` over an abstract `ℂ`-module (where
the canonical instance is in force) and applied via `exact` to the concrete tensor space. -/
private theorem two_inv_smul_add_diag {M : Type*} [AddCommGroup M] [Module ℂ M] (s : ℂ) (P Q : M) :
    (2 : ℂ)⁻¹ • (s • (P + Q) + s • (P - Q)) = s • P := by module

/-- The `−1`-eigenprojector arithmetic, abstractly: `½·(s(P+Q) − s(P−Q)) = sQ`, the `−1` sibling of
`two_inv_smul_add_diag`. -/
private theorem two_inv_smul_sub_diag {M : Type*} [AddCommGroup M] [Module ℂ M] (s : ℂ) (P Q : M) :
    (2 : ℂ)⁻¹ • (s • (P + Q) - s • (P - Q)) = s • Q := by module

variable {A : Observable qubit} {ψp ψm : PureState qubit}

/-! ### `A ⊗ I` on the Bell vector -/

/-- **`(A ⊗ I) |β⟩ = |ψp⟩⊗|ψp⟩ − |ψm⟩⊗|ψm⟩`.** For a `±1` observable `A` with `+1`/`−1` eigenstates
`ψp`/`ψm` diagonalising the (unnormalised) Bell vector (`hbell : bellVec = ψp⊗ψp + ψm⊗ψm`),
applying `A ⊗ I` fixes the `ψp` branch (`A ψp = ψp`) and negates the `ψm` branch (`A ψm = −ψm`).
The eigenvalue action is read off through the raw `TensorProduct.mapL` head (see the design
note). -/
theorem tmul_id_op_bellVec (hp : A.HasEigenstate 1 ψp) (hm : A.HasEigenstate (-1) ψm)
    (hbell : bellVec = ψp.vec ⊗ₜ[ℂ] ψp.vec + ψm.vec ⊗ₜ[ℂ] ψm.vec) :
    (A.tmul (Observable.id qubit)).op bellVec
      = ψp.vec ⊗ₜ[ℂ] ψp.vec - ψm.vec ⊗ₜ[ℂ] ψm.vec := by
  have ep : A.op ψp.vec = ((1 : ℝ) : ℂ) • ψp.vec := hp
  have em : A.op ψm.vec = ((-1 : ℝ) : ℂ) • ψm.vec := hm
  rw [Observable.tmul_op, Observable.id_op, hbell]
  change (TensorProduct.mapL A.op (1 : qubit.space →L[ℂ] qubit.space))
      (ψp.vec ⊗ₜ[ℂ] ψp.vec + ψm.vec ⊗ₜ[ℂ] ψm.vec)
    = ψp.vec ⊗ₜ[ℂ] ψp.vec - ψm.vec ⊗ₜ[ℂ] ψm.vec
  rw [map_add, TensorProduct.mapL_tmul, TensorProduct.mapL_tmul, one_apply_eq_self,
    one_apply_eq_self, ep, em]
  push_cast
  rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', one_smul, neg_one_smul]
  abel

/-! ### The collapse computation on `|Φ⁺⟩` -/

/-- **`P₊ |Φ⁺⟩ = (√2)⁻¹ |ψp⟩⊗|ψp⟩`.** The `+1` eigenprojector `P₊ = (I + A⊗I)/2` sends `|Φ⁺⟩` to
`(√2)⁻¹ |ψp⟩⊗|ψp⟩`: `I + A⊗I` doubles `ψp⊗ψp` and annihilates `ψm⊗ψm` (`tmul_id_op_bellVec` +
`two_inv_smul_add_diag`). -/
theorem projPlus_tmul_id_bellPhiPlus
    (hp : A.HasEigenstate 1 ψp) (hm : A.HasEigenstate (-1) ψm)
    (hbell : bellVec = ψp.vec ⊗ₜ[ℂ] ψp.vec + ψm.vec ⊗ₜ[ℂ] ψm.vec) :
    (A.tmul (Observable.id qubit)).projPlus bellPhiPlus.vec
      = (Real.sqrt 2 : ℂ)⁻¹ • (ψp.vec ⊗ₜ[ℂ] ψp.vec) := by
  rw [Observable.projPlus, _root_.smul_apply, _root_.add_apply,
    one_apply_eq_self, bellPhiPlus_vec, map_smul, tmul_id_op_bellVec hp hm hbell, hbell]
  exact two_inv_smul_add_diag _ _ _

/-- **`P₋ |Φ⁺⟩ = (√2)⁻¹ |ψm⟩⊗|ψm⟩`.** The `−1` sibling of `projPlus_tmul_id_bellPhiPlus`: the `−1`
eigenprojector `P₋ = (I − A⊗I)/2` sends `|Φ⁺⟩` to `(√2)⁻¹ |ψm⟩⊗|ψm⟩`. -/
theorem projMinus_tmul_id_bellPhiPlus
    (hp : A.HasEigenstate 1 ψp) (hm : A.HasEigenstate (-1) ψm)
    (hbell : bellVec = ψp.vec ⊗ₜ[ℂ] ψp.vec + ψm.vec ⊗ₜ[ℂ] ψm.vec) :
    (A.tmul (Observable.id qubit)).projMinus bellPhiPlus.vec
      = (Real.sqrt 2 : ℂ)⁻¹ • (ψm.vec ⊗ₜ[ℂ] ψm.vec) := by
  rw [Observable.projMinus, _root_.smul_apply, _root_.sub_apply,
    one_apply_eq_self, bellPhiPlus_vec, map_smul, tmul_id_op_bellVec hp hm hbell, hbell]
  exact two_inv_smul_sub_diag _ _ _

/-- The `+1` eigenprojector image `P₊ |Φ⁺⟩` is nonzero, so the `+1` outcome is possible and the
post-measurement state is well defined: `P₊ |Φ⁺⟩ = (√2)⁻¹ |ψp⟩⊗|ψp⟩` is a nonzero scalar multiple
of the unit product vector `|ψp⟩⊗|ψp⟩`. -/
theorem projPlus_tmul_id_bellPhiPlus_ne_zero
    (hp : A.HasEigenstate 1 ψp) (hm : A.HasEigenstate (-1) ψm)
    (hbell : bellVec = ψp.vec ⊗ₜ[ℂ] ψp.vec + ψm.vec ⊗ₜ[ℂ] ψm.vec) :
    (A.tmul (Observable.id qubit)).projPlus bellPhiPlus.vec ≠ 0 := by
  rw [projPlus_tmul_id_bellPhiPlus hp hm hbell]
  refine smul_ne_zero ?_ ?_
  · simp only [ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
    exact Real.sqrt_ne_zero'.mpr (by norm_num)
  · rw [← PureState.tmul_vec]; exact (ψp ⊗ ψp).vec_ne_zero

/-- The `−1` eigenprojector image `P₋ |Φ⁺⟩` is nonzero (the `−1` sibling of
`projPlus_tmul_id_bellPhiPlus_ne_zero`), so the `−1` outcome is possible. -/
theorem projMinus_tmul_id_bellPhiPlus_ne_zero
    (hp : A.HasEigenstate 1 ψp) (hm : A.HasEigenstate (-1) ψm)
    (hbell : bellVec = ψp.vec ⊗ₜ[ℂ] ψp.vec + ψm.vec ⊗ₜ[ℂ] ψm.vec) :
    (A.tmul (Observable.id qubit)).projMinus bellPhiPlus.vec ≠ 0 := by
  rw [projMinus_tmul_id_bellPhiPlus hp hm hbell]
  refine smul_ne_zero ?_ ?_
  · simp only [ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
    exact Real.sqrt_ne_zero'.mpr (by norm_num)
  · rw [← PureState.tmul_vec]; exact (ψm ⊗ ψm).vec_ne_zero

/-! ### The collapsed states are the product eigenstates -/

/-- **The `+1` collapse is the product state `|ψp⟩⊗|ψp⟩`.** After measuring `A` on the first
qubit of `|Φ⁺⟩` and obtaining `+1`, the normalized post-measurement pure state
`Observable.postMeasPlus (A⊗I) |Φ⁺⟩` is exactly `ψp ⊗ ψp`: the second qubit is left in the `+1`
eigenstate `ψp`. From `P₊ |Φ⁺⟩ = (√2)⁻¹ |ψp⟩⊗|ψp⟩` (`projPlus_tmul_id_bellPhiPlus`) with
`‖|ψp⟩⊗|ψp⟩‖ = 1`, the normalization scalar `(√2)⁻¹` divides out exactly (no residual phase). -/
theorem postMeasPlus_tmul_id_bellPhiPlus
    (hp : A.HasEigenstate 1 ψp) (hm : A.HasEigenstate (-1) ψm)
    (hbell : bellVec = ψp.vec ⊗ₜ[ℂ] ψp.vec + ψm.vec ⊗ₜ[ℂ] ψm.vec)
    (hne : (A.tmul (Observable.id qubit)).projPlus bellPhiPlus.vec ≠ 0) :
    (A.tmul (Observable.id qubit)).postMeasPlus bellPhiPlus hne = ψp ⊗ ψp := by
  apply PureState.ext
  have hw : ‖ψp.vec ⊗ₜ[ℂ] ψp.vec‖ = 1 := by
    rw [← PureState.tmul_vec]; exact (ψp ⊗ ψp).normalized
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  rw [Observable.postMeasPlus_vec, PureState.tmul_vec, projPlus_tmul_id_bellPhiPlus hp hm hbell]
  change (↑‖(Real.sqrt 2 : ℂ)⁻¹ • (ψp.vec ⊗ₜ[ℂ] ψp.vec)‖ : ℂ)⁻¹ • (Real.sqrt 2 : ℂ)⁻¹ •
      (ψp.vec ⊗ₜ[ℂ] ψp.vec) = ψp.vec ⊗ₜ[ℂ] ψp.vec
  rw [norm_smul, hw, mul_one, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), smul_smul, Complex.ofReal_inv, inv_inv,
    mul_inv_cancel₀ hs, one_smul]

/-- **The `−1` collapse is the product state `|ψm⟩⊗|ψm⟩`.** The `−1` sibling of
`postMeasPlus_tmul_id_bellPhiPlus`: after obtaining `−1`, the post-measurement state
`Observable.postMeasMinus (A⊗I) |Φ⁺⟩` is exactly `ψm ⊗ ψm`, leaving the second qubit in the `−1`
eigenstate `ψm`. -/
theorem postMeasMinus_tmul_id_bellPhiPlus
    (hp : A.HasEigenstate 1 ψp) (hm : A.HasEigenstate (-1) ψm)
    (hbell : bellVec = ψp.vec ⊗ₜ[ℂ] ψp.vec + ψm.vec ⊗ₜ[ℂ] ψm.vec)
    (hne : (A.tmul (Observable.id qubit)).projMinus bellPhiPlus.vec ≠ 0) :
    (A.tmul (Observable.id qubit)).postMeasMinus bellPhiPlus hne = ψm ⊗ ψm := by
  apply PureState.ext
  have hw : ‖ψm.vec ⊗ₜ[ℂ] ψm.vec‖ = 1 := by
    rw [← PureState.tmul_vec]; exact (ψm ⊗ ψm).normalized
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  rw [Observable.postMeasMinus_vec, PureState.tmul_vec, projMinus_tmul_id_bellPhiPlus hp hm hbell]
  change (↑‖(Real.sqrt 2 : ℂ)⁻¹ • (ψm.vec ⊗ₜ[ℂ] ψm.vec)‖ : ℂ)⁻¹ • (Real.sqrt 2 : ℂ)⁻¹ •
      (ψm.vec ⊗ₜ[ℂ] ψm.vec) = ψm.vec ⊗ₜ[ℂ] ψm.vec
  rw [norm_smul, hw, mul_one, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), smul_smul, Complex.ofReal_inv, inv_inv,
    mul_inv_cancel₀ hs, one_smul]

/-! ### Each outcome has probability one half -/

/-- **`p(+1) = ½`.** The Born probability of the `+1` outcome of the first-qubit `A` measurement on
`|Φ⁺⟩` is exactly one half: `p(+1) = ‖P₊|Φ⁺⟩‖² = ‖(√2)⁻¹ |ψp⟩⊗|ψp⟩‖² = ((√2)⁻¹)² = ½`
(`bornProb_signMeasurement_plus_eq_normSq` + `projPlus_tmul_id_bellPhiPlus`). The outcome — hence
the collapsed eigenstate — is uniformly random. -/
theorem bornProb_signMeasurement_plus_tmul_id_bellPhiPlus (hA : A.op * A.op = 1)
    (hp : A.HasEigenstate 1 ψp) (hm : A.HasEigenstate (-1) ψm)
    (hbell : bellVec = ψp.vec ⊗ₜ[ℂ] ψp.vec + ψm.vec ⊗ₜ[ℂ] ψm.vec) :
    ((A.tmul (Observable.id qubit)).signMeasurement
        (Observable.tmul_op_mul_self hA (by simp [Observable.id_op]))).bornProb
        bellPhiPlus.toState 0 = 1 / 2 := by
  have hw : ‖ψp.vec ⊗ₜ[ℂ] ψp.vec‖ = 1 := by
    rw [← PureState.tmul_vec]; exact (ψp ⊗ ψp).normalized
  rw [Observable.bornProb_signMeasurement_plus_eq_normSq,
    projPlus_tmul_id_bellPhiPlus hp hm hbell]
  change ‖(Real.sqrt 2 : ℂ)⁻¹ • (ψp.vec ⊗ₜ[ℂ] ψp.vec)‖ ^ 2 = 1 / 2
  rw [norm_smul, hw, mul_one, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- **`p(−1) = ½`.** The `−1` sibling of `bornProb_signMeasurement_plus_tmul_id_bellPhiPlus`. -/
theorem bornProb_signMeasurement_minus_tmul_id_bellPhiPlus (hA : A.op * A.op = 1)
    (hp : A.HasEigenstate 1 ψp) (hm : A.HasEigenstate (-1) ψm)
    (hbell : bellVec = ψp.vec ⊗ₜ[ℂ] ψp.vec + ψm.vec ⊗ₜ[ℂ] ψm.vec) :
    ((A.tmul (Observable.id qubit)).signMeasurement
        (Observable.tmul_op_mul_self hA (by simp [Observable.id_op]))).bornProb
        bellPhiPlus.toState 1 = 1 / 2 := by
  have hw : ‖ψm.vec ⊗ₜ[ℂ] ψm.vec‖ = 1 := by
    rw [← PureState.tmul_vec]; exact (ψm ⊗ ψm).normalized
  rw [Observable.bornProb_signMeasurement_minus_eq_normSq,
    projMinus_tmul_id_bellPhiPlus hp hm hbell]
  change ‖(Real.sqrt 2 : ℂ)⁻¹ • (ψm.vec ⊗ₜ[ℂ] ψm.vec)‖ ^ 2 = 1 / 2
  rw [norm_smul, hw, mul_one, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-! ### The Bell vector in the `X` basis -/

/-- **`bellVec = |+⟩⊗|+⟩ + |-⟩⊗|-⟩`.** The maximally entangled vector is basis-independent (N&C
Exercise 12.36): expressed in the `X` basis `{|+⟩, |-⟩}` it has the same diagonal form as in the
computational basis `{|0⟩, |1⟩}`. Expanding `|±⟩ = (√2)⁻¹(|0⟩ ± |1⟩)`
(`qubitPlus_vec_eq_smul_add`, `qubitMinus_vec_eq_smul_sub`), the cross terms `|0⟩⊗|1⟩`, `|1⟩⊗|0⟩`
cancel and each diagonal term appears with coefficient `1`. This is the `X`-basis instance of the
`hbell` hypothesis of the collapse lemmas. -/
theorem bellVec_eq_plusMinus :
    bellVec = qubitPlus.vec ⊗ₜ[ℂ] qubitPlus.vec + qubitMinus.vec ⊗ₜ[ℂ] qubitMinus.vec := by
  rw [bellVec, qubitPlus_vec_eq_smul_add, qubitMinus_vec_eq_smul_sub]
  change (_ : qubit.space ⊗[ℂ] qubit.space) = _
  simp only [smul_add, smul_sub, TensorProduct.add_tmul, TensorProduct.sub_tmul,
    TensorProduct.tmul_add, TensorProduct.tmul_sub, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, smul_smul, Concrete.invSqrt2_mul_self]
  module

/-! ### The two named measurements -/

/-- **Measure the first qubit in the `X` basis.** The projective (sign) measurement of the
observable `X ⊗ I` on `qubit ⊗ qubit`: its `±1` eigenprojectors are `|±⟩⟨±| ⊗ I`, i.e. it projects
the first qubit onto the `X` eigenbasis `{|+⟩, |-⟩}` while leaving the second untouched. Outcome
`0 ↔ +1`, `1 ↔ −1`. -/
def eprMeasureFirstX : Measurement (Fin 2) (qubit ⊗ qubit) :=
  (pauliXObservable.tmul (Observable.id qubit)).signMeasurement
    (Observable.tmul_op_mul_self pauliXObservable_op_mul_self (by simp [Observable.id_op]))

/-- **Measure the first qubit in the `Z` basis.** The projective (sign) measurement of the
observable `Z ⊗ I` on `qubit ⊗ qubit`: its `±1` eigenprojectors are `|0⟩⟨0| ⊗ I`, `|1⟩⟨1| ⊗ I`, the
computational-basis measurement of the first qubit. Outcome `0 ↔ +1` (`|0⟩`), `1 ↔ −1` (`|1⟩`). -/
def eprMeasureFirstZ : Measurement (Fin 2) (qubit ⊗ qubit) :=
  (pauliZObservable.tmul (Observable.id qubit)).signMeasurement
    (Observable.tmul_op_mul_self pauliZObservable_op_mul_self (by simp [Observable.id_op]))

end AxQM
