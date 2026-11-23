/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuantumChannel
import AxQM.Postulates.API.MaximallyMixed
import AxQM.Postulates.API.Qudit
import ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl

/-!
# AxQM.Postulates.API — the generalized depolarizing channel and its operator sum

The **generalized depolarizing channel** on a `d`-dimensional quantum system (Nielsen & Chuang,
§8.3.4, eq. 8.106): with probability `p` the state is replaced by the maximally mixed state `I/d`,
and left untouched otherwise,
`E(ρ) = p (I/d) + (1 - p) ρ`.
This file gives its **operator-sum (Kraus) representation** — the object Nielsen & Chuang,
Exercise 8.19 asks for — reusing the completely-depolarizing unitary `1`-design of `ToMathlib`.

* `AxQM.genDepolarizingChannel` — the channel `ρ ↦ (1 - p) ρ + p (I/d)` as a state-map on
  `qudit d`, a genuine `State` (a convex combination of `ρ` and `maximallyMixedState`, for
  `0 ≤ p ≤ 1`).
* `AxQM.genDepolarizingKraus` — the **operation elements** `{Eₖ}`, indexed by
  `Option ((Fin d → Bool) × Equiv.Perm (Fin d))`: the identity `√(1-p) · I`, and one
  `√(p/2ᵈd!) · Uⱼ` per depolarizing-design unitary `Uⱼ` (`OrthonormalBasis.depolarizingUnitary`).
* `AxQM.genDepolarizingChannel_op_eq_krausSum` — **the operator-sum representation**
  `E(ρ) = ∑ₖ Eₖ ρ Eₖ†`: the channel acts as the Kraus sum of `genDepolarizingKraus`. The heart of
  the exercise; proved by the depolarizing `1`-design twirl
  `∑ⱼ (2ᵈd!)⁻¹ Uⱼ A Uⱼ† = (tr A / d) I`
  (`OrthonormalBasis.sum_conjStarAlgEquiv_depolarizingUnitary`).
* `AxQM.genDepolarizingKraus_completeness` — **the completeness relation**
  `∑ₖ Eₖ† Eₖ = I` (each `Uⱼ` unitary, and `(1-p) + 2ᵈd! · p/2ᵈd! = 1`), certifying `E` is trace
  preserving.

Together these two are the operator-sum representation. The statement that these form a genuine
CPTP quantum operation (`IsChannel`) is in `AxQM/NC/Ch8/Exercise8_19.lean`.

## Design notes

* **Why the depolarizing `1`-design, not matrix units.** The completely-depolarizing part
  `ρ ↦ (tr ρ) I/d` needs an operator basis whose conjugation-average is `(tr ·/d) I`. `ToMathlib`
  supplies exactly this as a *unitary* `1`-design (the `2ᵈ d!` sign-flip×permutation unitaries
  `OrthonormalBasis.depolarizingUnitary`, with twirl
  `sum_conjStarAlgEquiv_depolarizingUnitary`), so the operation elements are `√pₖ Uₖ` and the
  representation is manifestly *random-unitary* — the physically natural reading of "replace with
  `I/d` with probability `p`", and the `d`-dimensional generalization of the qubit Pauli twirl
  `I/2 = (ρ + XρX + YρY + ZρZ)/4` (N&C eq. 8.101, Exercise 8.17) used for the qubit case.
-/

open scoped InnerProductSpace ComplexOrder
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {d : ℕ}

/-- The **computational orthonormal basis** `{|i⟩}` of `qudit d` (the standard basis of
`EuclideanSpace ℂ (Fin d)`), packaged at the qudit's state space so that operators on it have type
`(qudit d).space →L[ℂ] (qudit d).space`. -/
def quditOrthonormalBasis (d : ℕ) : OrthonormalBasis (Fin d) ℂ (qudit d).space :=
  EuclideanSpace.basisFun (Fin d) ℂ

/-- The `j`-th **depolarizing-design unitary** of the computational basis of `qudit d`, as a
(unitary) operator on the qudit space. Ranging over `j : (Fin d → Bool) × Equiv.Perm (Fin d)` these
are the `2ᵈ d!` sign-flip×permutation unitaries whose uniform conjugation-average is the completely
depolarizing map (`OrthonormalBasis.sum_conjStarAlgEquiv_depolarizingUnitary`). -/
def depolarizingOp (d : ℕ) (j : (Fin d → Bool) × Equiv.Perm (Fin d)) :
    (qudit d).space →L[ℂ] (qudit d).space :=
  ((quditOrthonormalBasis d).depolarizingUnitary j).toContinuousLinearEquiv

/-- The depolarizing-design operators are unitary: `Uⱼ† Uⱼ = I`. -/
theorem depolarizingOp_adjoint_comp_self (j : (Fin d → Bool) × Equiv.Perm (Fin d)) :
    (adjoint (depolarizingOp d j)).comp (depolarizingOp d j) = 1 := by
  rw [depolarizingOp, LinearIsometryEquiv.adjoint_eq_symm]
  ext x
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply]

/-- **The generalized depolarizing channel** `E(ρ) = (1 - p) ρ + p (I/d)` on `qudit d`
(Nielsen & Chuang eq. 8.106): with probability `p` the state is replaced by the maximally mixed
state `I/d = maximallyMixedState`, and left untouched otherwise. For `0 ≤ p ≤ 1` this is a genuine
`State`, being the convex combination of the states `ρ` and `I/d`. -/
def genDepolarizingChannel (d : ℕ) [NeZero d] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : State (qudit d)) : State (qudit d) where
  op := ((1 - p : ℝ) : ℂ) • ρ.op + ((p : ℝ) : ℂ) • (maximallyMixedState (qudit d)).op
  isDensity :=
    ContinuousLinearMap.IsDensityOp.convex_combination ρ.isDensity
      (maximallyMixedState (qudit d)).isDensity
      (by exact_mod_cast (by linarith : (0:ℝ) ≤ 1 - p)) (by exact_mod_cast hp0)
      (by push_cast; ring)

/-- The operator of the generalized depolarizing channel is `(1-p) ρ + p (I/d)`. -/
@[simp]
theorem genDepolarizingChannel_op [NeZero d] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : State (qudit d)) :
    (genDepolarizingChannel d p hp0 hp1 ρ).op
      = ((1 - p : ℝ) : ℂ) • ρ.op + ((p : ℝ) : ℂ) • (maximallyMixedState (qudit d)).op := rfl

/-- The **operation elements** of the generalized depolarizing channel, indexed by
`Option ((Fin d → Bool) × Equiv.Perm (Fin d))`:

* `none ↦ √(1-p) · I` — the "leave `ρ` untouched" branch;
* `some j ↦ √(p / 2ᵈd!) · Uⱼ` — one element per depolarizing-design unitary `Uⱼ` (`depolarizingOp`).

Since the `Uⱼ` average by conjugation to the completely-depolarizing map, `∑ₖ Eₖ ρ Eₖ†` reproduces
`E(ρ)` (`genDepolarizingChannel_op_eq_krausSum`), and `∑ₖ Eₖ† Eₖ = I`
(`genDepolarizingKraus_completeness`). -/
def genDepolarizingKraus (d : ℕ) (p : ℝ) :
    Option ((Fin d → Bool) × Equiv.Perm (Fin d)) →
      ((qudit d).space →L[ℂ] (qudit d).space)
  | none => (Real.sqrt (1 - p) : ℂ) • 1
  | some j => (Real.sqrt (p / (2 ^ d * d.factorial : ℝ)) : ℂ) • depolarizingOp d j

/-- The number of depolarizing-design unitaries is `2ᵈ d!`. -/
theorem card_depolarizing_index :
    Fintype.card ((Fin d → Bool) × Equiv.Perm (Fin d)) = 2 ^ d * d.factorial := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_perm,
    Fintype.card_fin]

/-- **The completeness relation** `∑ₖ Eₖ† Eₖ = I` for the generalized-depolarizing operation
elements (Nielsen & Chuang's trace condition, certifying `E` is trace preserving). Each `Uⱼ` is
unitary (`Uⱼ† Uⱼ = I`), so the sum is `(1-p) I + 2ᵈd! · (p/2ᵈd!) I = (1-p) I + p I = I`. -/
theorem genDepolarizingKraus_completeness [NeZero d] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ k, (adjoint (genDepolarizingKraus d p k)).comp (genDepolarizingKraus d p k) = 1 := by
  have hn : (0 : ℝ) < 2 ^ d * d.factorial := by positivity
  rw [Fintype.sum_option]
  -- the `none` (identity) branch contributes `(1-p) • I`
  have hnone : (adjoint (genDepolarizingKraus d p none)).comp (genDepolarizingKraus d p none)
      = ((1 - p : ℝ) : ℂ) • 1 := by
    simp only [genDepolarizingKraus]
    rw [← star_eq_adjoint, star_smul, star_one, smul_comp, comp_smul, smul_smul,
      ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by linarith)]
  -- each `some j` branch contributes `(p / 2ᵈd!) • I`
  have hsome : ∀ j, (adjoint (genDepolarizingKraus d p (some j))).comp
      (genDepolarizingKraus d p (some j)) = ((p / (2 ^ d * d.factorial : ℝ) : ℝ) : ℂ) • 1 := by
    intro j
    simp only [genDepolarizingKraus]
    rw [← star_eq_adjoint, star_smul, star_eq_adjoint, smul_comp, comp_smul, smul_smul,
      depolarizingOp_adjoint_comp_self]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by positivity)]
  rw [hnone, Finset.sum_congr rfl (fun j _ => hsome j), Finset.sum_const, Finset.card_univ,
    card_depolarizing_index, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← add_smul]
  rw [show ((2 ^ d * d.factorial : ℕ) : ℂ) * ((p / (2 ^ d * d.factorial : ℝ) : ℝ) : ℂ)
      = ((p : ℝ) : ℂ) by push_cast; field_simp]
  rw [show ((1 - p : ℝ) : ℂ) + ((p : ℝ) : ℂ) = 1 by push_cast; ring, one_smul]

/-- **The operator-sum (Kraus) representation of the generalized depolarizing channel**
(Nielsen & Chuang, Exercise 8.19): the channel acts as the operator sum of its operation elements,
`E(ρ) = ∑ₖ Eₖ ρ Eₖ†`. The identity element contributes `(1-p) ρ`; the `2ᵈd!` depolarizing-design
elements average, by the twirl `∑ⱼ (2ᵈd!)⁻¹ Uⱼ ρ Uⱼ† = (tr ρ / d) I`, to `p (I/d)` (using
`tr ρ = 1`). Together with `genDepolarizingKraus_completeness` (`∑ₖ Eₖ† Eₖ = I`) this is the
operator-sum representation the exercise asks for. -/
theorem genDepolarizingChannel_op_eq_krausSum [NeZero d] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : State (qudit d)) :
    (genDepolarizingChannel d p hp0 hp1 ρ).op = krausSumₗ (genDepolarizingKraus d p) ρ.op := by
  have hn : (0 : ℝ) < 2 ^ d * d.factorial := by positivity
  rw [genDepolarizingChannel_op, ContinuousLinearMap.krausSumₗ_apply, Fintype.sum_option]
  -- the `none` (identity) branch contributes `(1-p) • ρ.op`
  have hnone : (genDepolarizingKraus d p none).comp (ρ.op.comp
        (adjoint (genDepolarizingKraus d p none))) = ((1 - p : ℝ) : ℂ) • ρ.op := by
    simp only [genDepolarizingKraus]
    rw [← star_eq_adjoint, star_smul, star_one, smul_comp, comp_smul, comp_smul, smul_smul,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by linarith)]
  -- each `some j` branch is `(p/2ᵈd!) · conjugation of ρ by Uⱼ`
  have hterm : ∀ j, (genDepolarizingKraus d p (some j)).comp
      (ρ.op.comp (adjoint (genDepolarizingKraus d p (some j))))
      = ((p / (2 ^ d * d.factorial : ℝ) : ℝ) : ℂ)
          • ((quditOrthonormalBasis d).depolarizingUnitary j).conjStarAlgEquiv ρ.op := by
    intro j
    simp only [genDepolarizingKraus, depolarizingOp, LinearIsometryEquiv.conjStarAlgEquiv_apply]
    rw [← star_eq_adjoint, star_smul, star_eq_adjoint, LinearIsometryEquiv.adjoint_eq_symm,
      smul_comp, comp_smul, comp_smul, smul_smul]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by positivity)]
  -- the twirl: the `some`-sum averages to `p • (I/d)`
  have htwirl : ∑ j, (genDepolarizingKraus d p (some j)).comp
        (ρ.op.comp (adjoint (genDepolarizingKraus d p (some j))))
      = ((p : ℝ) : ℂ) • (maximallyMixedState (qudit d)).op := by
    have h := (quditOrthonormalBasis d).sum_conjStarAlgEquiv_depolarizingUnitary ρ.op
    have hfac : ∀ j ∈ (Finset.univ : Finset ((Fin d → Bool) × Equiv.Perm (Fin d))),
        (genDepolarizingKraus d p (some j)).comp
          (ρ.op.comp (adjoint (genDepolarizingKraus d p (some j))))
        = ((p : ℝ) : ℂ) • ((2 ^ Fintype.card (Fin d) *
            ((Fintype.card (Fin d)).factorial : ℂ))⁻¹
            • ((quditOrthonormalBasis d).depolarizingUnitary j).conjStarAlgEquiv ρ.op) := by
      intro j _
      rw [hterm j, smul_smul, Fintype.card_fin]
      congr 1
      push_cast
      field_simp
    rw [Finset.sum_congr rfl hfac, ← Finset.smul_sum, h, State.trace_op_eq_one,
      maximallyMixedState_op]
    rw [show Module.finrank ℂ (qudit d).space = Fintype.card (Fin d) by
      rw [Fintype.card_fin]; exact finrank_euclideanSpace_fin, one_div]
  rw [hnone, htwirl]

end AxQM
