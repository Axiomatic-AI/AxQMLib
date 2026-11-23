/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasurementTransportBornProb
import AxQM.Postulates.API.SameNonzeroSpectrumConjugate

/-!
# Post-measurement marginal isospectrality (Proposition 12.14, `hspec`)

The measurement-simulation step of **Nielsen & Chuang, Proposition 12.14** transports a measurement
`mB` that Bob performs on his factor `T` to the square-root ("pretty-good") measurement
`mA = Measurement.ofPOVM (mB.transportPOVM W hW)` of the transported POVM
`{W Mⱼ† Mⱼ W†} ∪ {1 − W W†}`
Alice performs on her factor `S`, where `W = crossSynthesis a b` identifies Bob's Schmidt basis `b`
with Alice's `a`. The Born-probability half of the simulation (`hprob`) is
`AxQM/Postulates/API/MeasurementTransportBornProb.lean`; this file supplies the **spectral half**
(`hspec`): after Bob measures `mB` and gets outcome `j`, and Alice measures `mA` and gets the
matching outcome `some j`, Bob's post-measurement marginal and Alice's are **isospectral**.

## The result

`PureState.sameNonzeroSpectrum_transport_postMeasurement_marginal`:

Alice's and Bob's post-measurement reduced states share the same non-zero spectrum.

By the reduced-operator formulas (`Measurement.reducedRight_postMeasurement_onRight_op`,
`reducedLeft_postMeasurement_onLeft_op`) these marginals are, up to the common Born scalar `p⁻¹`
(equal by `hprob`), the conjugations `Mⱼ ρ_B Mⱼ†` and `Nⱼ ρ_A Nⱼ` with Alice's simulating
operator `Nⱼ = √Eⱼ = cfc √ (W Mⱼ†Mⱼ W†)`.
The theorem is exactly N&C's Eq. (12.159) claim that these two
post-measurement states are related by a local unitary — the isospectrality that
`Measurement.exists_localEvolution_postMeasurement_onRight_of_reducedSpectrum` (the general crux)
then turns into the local unitary via Exercise 2.80.

## The proof — two `X X† ≅ X† X` flips through a diagonal intermediate

Writing `ρ_A = tr_T|ψ⟩⟨ψ|`, `ρ_B = tr_S|ψ⟩⟨ψ|`, `Dₐ = ∑ᵢ λᵢ |aᵢ⟩⟨aᵢ|`, `D_b = ∑ᵢ λᵢ |bᵢ⟩⟨bᵢ|` (the
diagonal square roots of `ρ_A = Dₐ²`, `ρ_B = D_b²`; `λ` the Schmidt coefficients), and
`Eⱼ = W Mⱼ† Mⱼ W†` (so `Nⱼ Nⱼ = Eⱼ`, `Nⱼ` self-adjoint), the operator-isospectrality lemma
`State.sameNonzeroSpectrum_of_op_eq_smul_comp_adjoint` (`X X† ≅ X† X`) is applied twice
through the **intermediate state** whose density operator is `p⁻¹ · (Dₐ Eⱼ Dₐ)`:

* **Flip 1** (`X_A = Nⱼ Dₐ`): Alice's `p⁻¹ · Nⱼ ρ_A Nⱼ = p⁻¹ · (X_A X_A†)` is isospectral to
  `p⁻¹ · (X_A† X_A) = p⁻¹ · (Dₐ Eⱼ Dₐ)` — the intermediate.
* **Flip 2** (`X_W = W D_b Mⱼ†`): the intermediate `p⁻¹ · (X_W X_W†) = p⁻¹ · (Dₐ Eⱼ Dₐ)` is
  isospectral to `p⁻¹ · (X_W† X_W) = p⁻¹ · (Mⱼ ρ_B Mⱼ†)` — Bob's.

The two adjoint-conjugation identities `X_A† X_A = X_W X_W† = Dₐ Eⱼ Dₐ` and
`X_W† X_W = Mⱼ ρ_B Mⱼ†` are pure operator algebra on the **cross-synthesis intertwining**
`Dₐ W = W D_b` (`InnerProductSpace.crossSynthesis_comp_diagonal` at `c = λ`) and the state
identity
`W† ρ_A W = ρ_B` (`PureState.adjoint_crossSynthesis_reducedLeft_conj`); the intermediate is a
genuine density operator (positive as `X_W X_W†`, trace one because Bob's marginal — a `State` — has
trace one, forcing `tr(Mⱼ ρ_B Mⱼ†) = p`). Transitivity of `SameNonzeroSpectrum` then chains
Alice ≅ intermediate ≅ Bob.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap (adjoint)
open InnerProductSpace (crossSynthesis rankOne)

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S T : QSystem}

set_option maxHeartbeats 1000000 in
-- Heavy operator-algebra chain: two `X X† ≅ X† X` isospectrality flips through a
-- diagonal intermediate, with many rank-one / adjoint rewrites on composite-system operators.
/-- **Post-measurement marginal isospectrality (Proposition 12.14, `hspec`).** For a bipartite pure
state `ψ` on `S ⊗ T` in Schmidt form `|ψ⟩ = ∑ᵢ lᵢ |aᵢ⟩|bᵢ⟩`, let `W = crossSynthesis a b`
identify Bob's Schmidt basis with Alice's, and let `mA = ofPOVM (mB.transportPOVM W hW)` be Alice's
simulating square-root measurement of the transported POVM. After Bob measures `mB` and obtains
outcome `j`, and Alice measures `mA` and obtains the matching outcome `some j`, Bob's
post-measurement reduced state
on his factor is **isospectral** to Alice's post-measurement reduced state on her factor:

`(Bob's post).reducedRight ≅ (Alice's post).reducedLeft`.

This is the spectral half of N&C's measurement simulation (Eq. 12.159): the two post-measurement
states have the same reduced spectrum, so by the general crux
(`Measurement.exists_localEvolution_postMeasurement_onRight_of_reducedSpectrum`) they are related by
a local unitary. The proof flips the two conjugations `Mⱼ ρ_B Mⱼ†` (Bob's) and `Nⱼ ρ_A Nⱼ` (Alice's,
`Nⱼ = √(W Mⱼ†Mⱼ W†)`) through the common intermediate `Dₐ Eⱼ Dₐ` using the isospectrality lemma
`State.sameNonzeroSpectrum_of_op_eq_smul_comp_adjoint` twice, over the cross-synthesis intertwining
`Dₐ W = W D_b` and the state identity `W† ρ_A W = ρ_B`. See the module docstring. -/
theorem PureState.sameNonzeroSpectrum_transport_postMeasurement_marginal {n : ℕ}
    (mB : Measurement ι T) {ψ : PureState (S ⊗ T)} {l : Fin n → ℝ} {a : Fin n → S.space}
    {b : Fin n → T.space} (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hψ : ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i)
    (hW : IsStarProjection ((crossSynthesis ℂ a b).comp (adjoint (crossSynthesis ℂ a b)))) (j : ι)
    (hpB : (mB.onRight S).bornProb ψ.toState j ≠ 0)
    (hpA : ((Measurement.ofPOVM (mB.transportPOVM (crossSynthesis ℂ a b) hW)).onLeft T).bornProb
      ψ.toState (some j) ≠ 0) :
    ((mB.onRight S).postMeasurement ψ.toState j hpB).reducedRight.SameNonzeroSpectrum
      (((Measurement.ofPOVM (mB.transportPOVM (crossSynthesis ℂ a b) hW)).onLeft T).postMeasurement
        ψ.toState (some j) hpA).reducedLeft := by
  classical
  set W := crossSynthesis ℂ a b with hWdef
  set M := mB.op j with hMdef
  set ρA := ψ.toState.reducedLeft.op with hρAdef
  set ρB := ψ.toState.reducedRight.op with hρBdef
  -- The diagonal square roots of the two marginals.
  set Da := ∑ i, (l i : ℂ) • rankOne ℂ (a i) (a i) with hDadef
  set Db := ∑ i, (l i : ℂ) • rankOne ℂ (b i) (b i) with hDbdef
  -- Alice's simulating operator `Nⱼ = √Eⱼ` and the transported effect `Eⱼ`.
  set E := (mB.transportPOVM W hW).elements (some j) with hEdef
  set N := (Measurement.ofPOVM (mB.transportPOVM W hW)).op (some j) with hNdef
  -- The common Born scalar (Bob's; Alice's equals it by `hprob`).
  set p := (mB.onRight S).bornProb ψ.toState j with hpdef
  have hpA' : ((Measurement.ofPOVM (mB.transportPOVM W hW)).onLeft T).bornProb ψ.toState (some j)
      = p := mB.bornProb_onLeft_ofPOVM_transportPOVM_eq ha hb hψ hW j
  -- Diagonal-operator algebra (`Mathlib/Analysis/InnerProductSpace/PartialIsometryOrthonormal`).
  have hDa_sa : adjoint Da = Da := InnerProductSpace.adjoint_sum_smul_rankOne_self a l
  have hDb_sa : adjoint Db = Db := InnerProductSpace.adjoint_sum_smul_rankOne_self b l
  have hDaDa : Da.comp Da = ρA := by
    rw [hρAdef, ψ.reducedLeft_op_eq_sum_rankOne hb hψ, hDadef]
    exact InnerProductSpace.sum_smul_rankOne_self_comp_self ha l
  have hDbDb : Db.comp Db = ρB := by
    rw [hρBdef, ψ.reducedRight_op_eq_sum_rankOne ha hψ, hDbdef]
    exact InnerProductSpace.sum_smul_rankOne_self_comp_self hb l
  -- Cross-synthesis intertwining `W ∘ D_b = Dₐ ∘ W` (at `c = λ`).
  have hWDb : W.comp Db = Da.comp W :=
    InnerProductSpace.crossSynthesis_comp_diagonal ha hb (fun i => (l i : ℂ))
  -- `E = W (M†M) W†`.
  have hEeq : E = W.comp (((adjoint M).comp M).comp (adjoint W)) := by
    rw [hEdef, Measurement.transportPOVM_elements_some]
  -- `Nⱼ` is self-adjoint and squares to `Eⱼ`.
  have hN_sa : adjoint N = N := by
    rw [hNdef, Measurement.ofPOVM_op]; exact ContinuousLinearMap.adjoint_cfc_real_sqrt _
  have hE_nonneg : (0 : S.space →L[ℂ] S.space) ≤ E :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mpr ((mB.transportPOVM W hW).isPositive (some j))
  have hNN : N.comp N = E := by
    rw [hNdef, Measurement.ofPOVM_op, ← ContinuousLinearMap.mul_def,
      cfc_real_sqrt_mul_self_of_nonneg hE_nonneg]
  -- The state identity `W† ρ_A W = ρ_B`.
  have hconj : (adjoint W).comp (ρA.comp W) = ρB :=
    ψ.adjoint_crossSynthesis_reducedLeft_conj ha hb hψ
  -- The two flip operators.
  set XA := N.comp Da with hXAdef
  set XW := W.comp (Db.comp (adjoint M)) with hXWdef
  -- `adjoint XA = Da N`.
  have hXA_adj : adjoint XA = Da.comp N := by
    rw [hXAdef, ContinuousLinearMap.adjoint_comp, hN_sa, hDa_sa]
  -- `adjoint XW = M D_b W†`.
  have hXW_adj : adjoint XW = M.comp (Db.comp (adjoint W)) := by
    rw [hXWdef, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, hDb_sa, ContinuousLinearMap.comp_assoc]
  -- Identity (II): `XA XA† = Nⱼ ρ_A Nⱼ`.
  have hII : XA.comp (adjoint XA) = N.comp (ρA.comp (adjoint N)) := by
    rw [hXAdef, hXA_adj, hN_sa]
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc Da Da N, hDaDa]
  -- Identity (I): `XW† XW = Mⱼ ρ_B Mⱼ†`.
  have hI : (adjoint XW).comp XW = M.comp (ρB.comp (adjoint M)) := by
    rw [hXWdef, hXW_adj]
    -- `M D_b W† ∘ W D_b M† = M (D_b W† W D_b) M†`, and `D_b W† W D_b = W† ρ_A W = ρ_B`.
    have key : (Db.comp (adjoint W)).comp (W.comp Db) = ρB := by
      have h1 : W.comp Db = Da.comp W := hWDb
      have h2 : Db.comp (adjoint W) = adjoint (W.comp Db) := by
        rw [ContinuousLinearMap.adjoint_comp, hDb_sa]
      rw [h2, h1, ContinuousLinearMap.adjoint_comp, hDa_sa]
      rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc Da Da W, hDaDa,
        ← hconj]
    calc (M.comp (Db.comp (adjoint W))).comp ((W.comp (Db.comp (adjoint M))))
        = M.comp (((Db.comp (adjoint W)).comp (W.comp Db)).comp (adjoint M)) := by
            simp only [ContinuousLinearMap.comp_assoc]
      _ = M.comp (ρB.comp (adjoint M)) := by rw [key]
  -- Identity (III): `XA† XA = XW XW† = Dₐ Eⱼ Dₐ`.
  have hIII : (adjoint XA).comp XA = XW.comp (adjoint XW) := by
    rw [hXA_adj, hXAdef, hXW_adj, hXWdef]
    -- LHS `= Da N N Da = Da E Da`; RHS `= W D_b M† M D_b W† = Da (W M†M W†) Da = Da E Da`.
    have hlhs : (Da.comp N).comp (N.comp Da) = Da.comp (E.comp Da) := by
      rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc N N Da, hNN,
        ← ContinuousLinearMap.comp_assoc]
    have hrhs : (W.comp (Db.comp (adjoint M))).comp (M.comp (Db.comp (adjoint W)))
        = Da.comp (E.comp Da) := by
      -- `W D_b M† M D_b W† = W D_b (M†M) D_b W†`; push `W`, `W†` in via intertwining to `Dₐ E Dₐ`.
      have hWDb' : W.comp Db = Da.comp W := hWDb
      have hDbW : Db.comp (adjoint W) = (adjoint W).comp Da := by
        have := congrArg adjoint hWDb'
        rwa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, hDb_sa, hDa_sa]
          at this
      rw [hEeq]
      calc (W.comp (Db.comp (adjoint M))).comp (M.comp (Db.comp (adjoint W)))
          = (W.comp Db).comp (((adjoint M).comp M).comp (Db.comp (adjoint W))) := by
              simp only [ContinuousLinearMap.comp_assoc]
        _ = (Da.comp W).comp (((adjoint M).comp M).comp ((adjoint W).comp Da)) := by
              rw [hWDb', hDbW]
        _ = Da.comp ((W.comp (((adjoint M).comp M).comp (adjoint W))).comp Da) := by
              simp only [ContinuousLinearMap.comp_assoc]
    rw [hlhs, hrhs]
  -- Marginal-operator formulas.
  have hBobop : ((mB.onRight S).postMeasurement ψ.toState j hpB).reducedRight.op
      = ((p : ℝ) : ℂ)⁻¹ • (M.comp (ρB.comp (adjoint M))) := by
    rw [hMdef, hρBdef, hpdef]
    exact mB.reducedRight_postMeasurement_onRight_op ψ j hpB
  have hAliceop : (((Measurement.ofPOVM (mB.transportPOVM W hW)).onLeft T).postMeasurement
        ψ.toState (some j) hpA).reducedLeft.op
      = ((p : ℝ) : ℂ)⁻¹ • (N.comp (ρA.comp (adjoint N))) := by
    rw [hNdef, hρAdef]
    rw [(Measurement.ofPOVM (mB.transportPOVM W hW)).reducedLeft_postMeasurement_onLeft_op
      ψ.toState (some j) hpA]
    rw [hpA']
  -- Trace one of `Mⱼ ρ_B Mⱼ†`: forced by Bob's marginal being a genuine `State` (trace one).
  have hp0 : ((p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpB
  have htrBob : (LinearMap.trace ℂ T.space) ↑(M.comp (ρB.comp (adjoint M))) = (p : ℂ) := by
    have h1 := ((mB.onRight S).postMeasurement ψ.toState j hpB).reducedRight.trace_op_eq_one
    rw [hBobop, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul] at h1
    rwa [inv_mul_eq_one₀ hp0, eq_comm] at h1
  have hp_nonneg : (0 : ℝ) ≤ p := Measurement.bornProb_nonneg _ _ _
  have hpinv_nonneg : (0 : ℝ) ≤ p⁻¹ := inv_nonneg.mpr hp_nonneg
  -- The intermediate density operator `p⁻¹ · (XW XW†) = p⁻¹ · (Dₐ Eⱼ Dₐ)`.
  have hσpos : (((p : ℝ) : ℂ)⁻¹ • (XW.comp (adjoint XW))).IsPositive := by
    rw [← Complex.ofReal_inv, Complex.coe_smul]
    exact (ContinuousLinearMap.isPositive_self_comp_adjoint XW).smul_real_of_nonneg hpinv_nonneg
  have hσtr : (LinearMap.trace ℂ S.space)
      ↑(((p : ℝ) : ℂ)⁻¹ • (XW.comp (adjoint XW))) = 1 := by
    rw [ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul,
        ContinuousLinearMap.toLinearMap_comp,
      LinearMap.trace_comp_comm', ← ContinuousLinearMap.toLinearMap_comp, hI, htrBob,
          inv_mul_cancel₀ hp0]
  let σint : State S := ⟨((p : ℝ) : ℂ)⁻¹ • (XW.comp (adjoint XW)), hσpos, hσtr⟩
  have hσop : σint.op = ((p : ℝ) : ℂ)⁻¹ • (XW.comp (adjoint XW)) := rfl
  -- Flip 1: Alice's post-marginal ≅ the intermediate, via `X_A = Nⱼ Dₐ`.
  have hflip1 : (((Measurement.ofPOVM (mB.transportPOVM W hW)).onLeft T).postMeasurement
      ψ.toState (some j) hpA).reducedLeft.SameNonzeroSpectrum σint :=
    State.sameNonzeroSpectrum_of_op_eq_smul_comp_adjoint (X := XA) (c := p⁻¹)
      (by rw [Complex.ofReal_inv, hII]; exact hAliceop)
      (by rw [hσop, Complex.ofReal_inv, hIII])
  -- Flip 2: the intermediate ≅ Bob's post-marginal, via `X_W = W D_b Mⱼ†`.
  have hflip2 : σint.SameNonzeroSpectrum
      ((mB.onRight S).postMeasurement ψ.toState j hpB).reducedRight :=
    State.sameNonzeroSpectrum_of_op_eq_smul_comp_adjoint (X := XW) (c := p⁻¹)
      (by rw [hσop, Complex.ofReal_inv])
      (by rw [Complex.ofReal_inv, hI]; exact hBobop)
  exact (hflip1.trans hflip2).symm

end AxQM
