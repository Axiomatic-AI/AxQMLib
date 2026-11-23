/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch10.Exercise10_52
import AxQM.Postulates.API.PureState
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.API.ControlBranchExt
import AxQM.Postulates.API.ThreeQubitBitFlipCode

/-!
# Nielsen & Chuang, Exercise 10.63 — a `Z̄ ↔ X̄` normalizer is the encoded Hadamard

*(N&C §10.6.2, p. 482.)*

If U maps Steane code to itself with UZbarU-dag=Xbar, UXbarU-dag=Zbar, then U acts as encoded
Hadamard.

## The content, and why it holds

The Steane code space is the two-dimensional subspace spanned by the logical
codewords `|0_L⟩ = steaneLogicalZero`, `|1_L⟩ = steaneLogicalOne`; on it the encoded
operators `Z̄ = Z₁…Z₇ = steaneLogicalZBar` and `X̄ = X₁…X₇ = steaneLogicalXBar` act
as the single-qubit Pauli `Z`, `X`: `Z̄|0_L⟩ = |0_L⟩`, `Z̄|1_L⟩ = −|1_L⟩`,
`X̄|0_L⟩ = |1_L⟩`, `X̄|1_L⟩ = |0_L⟩` (Exercise 10.52). A unitary `U` **mapping the
code into itself** restricts to a unitary of this qubit; the Hadamard is the unique
(up to global phase) single-qubit unitary interchanging `Z ↔ X` under conjugation,
so `U` must act on the code as the encoded Hadamard `H̄`.

The proof needs no `2×2`-uniqueness machinery. Write `ψ₀ := U|0_L⟩`. Since `U` maps
the code into itself, `ψ₀ = a|0_L⟩ + b|1_L⟩` for amplitudes `a, b`. From
`U Z̄ U† = X̄` (rearranged to `X̄ U = U Z̄`) and `Z̄|0_L⟩ = |0_L⟩`,
`X̄ ψ₀ = X̄ U |0_L⟩ = U Z̄ |0_L⟩ = U |0_L⟩ = ψ₀`, so `ψ₀` is a `+1`-eigenvector of
`X̄`. Expanding `X̄ ψ₀ = ψ₀` in the basis gives `a|1_L⟩ + b|0_L⟩ = a|0_L⟩ + b|1_L⟩`;
taking `⟨0_L|·⟩` (the codewords are orthonormal) yields `b = a`. Hence
`ψ₀ = a(|0_L⟩ + |1_L⟩) = (a√2)·(|0_L⟩+|1_L⟩)/√2`, a global-phase multiple of
`(|0_L⟩+|1_L⟩)/√2` (the scalar has unit modulus, both being unit vectors). For the
other codeword, `U X̄ U† = Z̄` rearranges to `U X̄ = Z̄ U`, so
`U|1_L⟩ = U X̄ |0_L⟩ = Z̄ U |0_L⟩ = Z̄ ψ₀ = a(|0_L⟩ − |1_L⟩) = (a√2)·(|0_L⟩−|1_L⟩)/√2`,
the **same** phase — exactly the encoded Hadamard action.

## Shape of the statement

* **"Up to a global phase"** is the equality of the *density operators*
  (`PureState.toState`, `|ψ⟩⟨ψ|`), which erase the global phase: two conjuncts
  `(U.evolvePure |0_L⟩).toState = steaneLogicalPlus.toState` and the `|1_L⟩`
  companion. N&C's phase is a **single** one, so a third grounded conjunct
  `⟪U|0_L⟩, |+_L⟩⟫ = ⟪U|1_L⟩, |−_L⟩⟫` (equality of `PureState.overlap`s, both `= conj c`)
  ties the two column phases together — without it the two `toState` equalities would
  leave the phases independent (admitting the physically distinct `U = H̄·Z̄`).
* **"Maps the code into itself"** is `InSteaneCode`, the predicate that a state's
  vector is a linear combination of the two codewords (they span the
  two-dimensional code).
* The conjugation hypotheses are `Evolution` equalities through `Evolution.comp` /
  `Evolution.adjoint` (`U Z̄ U† = X̄`). The codeword
  orthogonality `steaneLogical_overlap_eq_zero` is stated with the overlap
  `PureState.overlap` (a scalar).

## The declarations

* `steaneLogical_overlap_eq_zero` — the codewords are orthogonal, `⟨0_L|1_L⟩ = 0`
  (eigenstates of the unitary `Z̄` with distinct eigenvalues `+1 ≠ −1`).
* `InSteaneCode` — "lies in the Steane code space" (a combination of the codewords).
* `steaneLogicalPlus` / `steaneLogicalMinus` — the target states `(|0_L⟩ ± |1_L⟩)/√2`
  (encoded `|±_L⟩`).
* `steaneEncodedHadamard_action` — **Exercise 10.63**: any `U` mapping the code into
  itself with `U Z̄ U† = X̄`, `U X̄ U† = Z̄` sends `|0_L⟩ ↦ (|0_L⟩+|1_L⟩)/√2` and
  `|1_L⟩ ↦ (|0_L⟩−|1_L⟩)/√2`, up to a *single* global phase (the two `toState`
  equalities plus the shared-phase `overlap` conjunct).
-/

namespace AxQM

open scoped InnerProductSpace

/-- **The Steane logical codewords are orthogonal**, `⟨0_L|1_L⟩ = 0`. They are
eigenstates of the unitary logical-`Z̄` operator `steaneLogicalZBar` with the
distinct eigenvalues `+1` (on `|0_L⟩`) and `−1` (on `|1_L⟩`); a unitary preserves
inner products, so eigenvectors with different eigenvalues are orthogonal. Stated
over the grounded overlap `PureState.overlap`. -/
theorem steaneLogical_overlap_eq_zero :
    steaneLogicalZero.overlap steaneLogicalOne = 0 := by
  have h0 : steaneLogicalZBar.op steaneLogicalZero.vec = steaneLogicalZero.vec := by
    have h : steaneLogicalZBar.op steaneLogicalZero.vec = (1 : ℂ) • steaneLogicalZero.vec :=
      steaneLogicalZBar_hasEigenstate_logicalZero
    rwa [one_smul] at h
  have h1 : steaneLogicalZBar.op steaneLogicalOne.vec = -steaneLogicalOne.vec := by
    have h : steaneLogicalZBar.op steaneLogicalOne.vec = (-1 : ℂ) • steaneLogicalOne.vec :=
      steaneLogicalZBar_hasEigenstate_logicalOne
    rwa [neg_one_smul] at h
  have iso : inner ℂ (steaneLogicalZBar.op steaneLogicalZero.vec)
      (steaneLogicalZBar.op steaneLogicalOne.vec)
      = inner ℂ steaneLogicalZero.vec steaneLogicalOne.vec := by
    rw [← Evolution.toIsometryEquiv_apply, ← Evolution.toIsometryEquiv_apply,
      LinearIsometryEquiv.inner_map_map]
  rw [h0, h1, inner_neg_right] at iso
  rw [PureState.overlap_def]
  linear_combination (-(1 : ℂ) / 2) * iso

/-- **The Steane code space membership predicate.** A pure state `ψ` of the
seven-qubit register lies in the (two-dimensional) Steane code space iff its vector
is a linear combination `a|0_L⟩ + b|1_L⟩` of the two logical codewords, which span
the code. "`U` maps the Steane code into itself" is exactly
`InSteaneCode (U.evolvePure |0_L⟩) ∧ InSteaneCode (U.evolvePure |1_L⟩)`. -/
def InSteaneCode (ψ : PureState (bitReg (Fin 7))) : Prop :=
  ∃ a b : ℂ, ψ.vec = a • steaneLogicalZero.vec + b • steaneLogicalOne.vec

/-- **The encoded `|+_L⟩ = (|0_L⟩ + |1_L⟩)/√2`.** The normalized equal superposition
of the two Steane codewords — the image of `|0_L⟩` under the encoded Hadamard. -/
noncomputable def steaneLogicalPlus : PureState (bitReg (Fin 7)) :=
  PureState.orthoPairOfOverlap steaneLogicalZero steaneLogicalOne steaneLogical_overlap_eq_zero
    ((Real.sqrt 2 : ℂ)⁻¹) ((Real.sqrt 2 : ℂ)⁻¹) (by rw [norm_sq_sqrtTwo_inv]; norm_num)

/-- **The encoded `|−_L⟩ = (|0_L⟩ − |1_L⟩)/√2`.** The other Hadamard-rotated
codeword — the image of `|1_L⟩` under the encoded Hadamard. -/
noncomputable def steaneLogicalMinus : PureState (bitReg (Fin 7)) :=
  PureState.orthoPairOfOverlap steaneLogicalZero steaneLogicalOne steaneLogical_overlap_eq_zero
    ((Real.sqrt 2 : ℂ)⁻¹) (-(Real.sqrt 2 : ℂ)⁻¹) (by rw [norm_neg, norm_sq_sqrtTwo_inv]; norm_num)

/-- **Nielsen & Chuang, Exercise 10.63.** Any unitary `U` that maps the Steane code
into itself and conjugates `Z̄ ↦ X̄`, `X̄ ↦ Z̄` acts on the encoded basis as the
encoded Hadamard, up to a **single** global phase: `|0_L⟩ ↦ (|0_L⟩+|1_L⟩)/√2` and
`|1_L⟩ ↦ (|0_L⟩−|1_L⟩)/√2`.

The two `toState` (density-operator) equalities render "→ up to a global phase" for
each codeword; on their own they would only give `U|0_L⟩ = c₀·|+_L⟩`,
`U|1_L⟩ = c₁·|−_L⟩` with *independent* unit-modulus `c₀, c₁` (admitting the distinct
gate `U = H̄·Z̄`). The third conjunct — the equality of the grounded overlaps
`⟪U|0_L⟩, |+_L⟩⟫ = ⟪U|1_L⟩, |−_L⟩⟫` (both `= conj c`) — pins `c₀ = c₁`, so `U` acts as
the encoded Hadamard up to one shared phase, exactly as N&C states. -/
theorem steaneEncodedHadamard_action (U : Evolution (bitReg (Fin 7)))
    (hZX : U.comp (steaneLogicalZBar.comp U.adjoint) = steaneLogicalXBar)
    (hXZ : U.comp (steaneLogicalXBar.comp U.adjoint) = steaneLogicalZBar)
    (hmap : InSteaneCode (U.evolvePure steaneLogicalZero) ∧
            InSteaneCode (U.evolvePure steaneLogicalOne)) :
    (U.evolvePure steaneLogicalZero).toState = steaneLogicalPlus.toState ∧
    (U.evolvePure steaneLogicalOne).toState = steaneLogicalMinus.toState ∧
    (U.evolvePure steaneLogicalZero).overlap steaneLogicalPlus
      = (U.evolvePure steaneLogicalOne).overlap steaneLogicalMinus := by
  obtain ⟨a, b, hψ0⟩ := hmap.1
  -- Operator actions of `X̄`, `Z̄` on the codewords (Exercise 10.52).
  have hX0 : steaneLogicalXBar.op steaneLogicalZero.vec = steaneLogicalOne.vec := by
    rw [← Evolution.evolvePure_vec, steaneLogicalXBar_evolvePure_logicalZero]
  have hX1 : steaneLogicalXBar.op steaneLogicalOne.vec = steaneLogicalZero.vec := by
    rw [← Evolution.evolvePure_vec, steaneLogicalXBar_evolvePure_logicalOne]
  have hZ0 : steaneLogicalZBar.op steaneLogicalZero.vec = steaneLogicalZero.vec := by
    have h : steaneLogicalZBar.op steaneLogicalZero.vec = (1 : ℂ) • steaneLogicalZero.vec :=
      steaneLogicalZBar_hasEigenstate_logicalZero
    rwa [one_smul] at h
  have hZ1 : steaneLogicalZBar.op steaneLogicalOne.vec = -steaneLogicalOne.vec := by
    have h : steaneLogicalZBar.op steaneLogicalOne.vec = (-1 : ℂ) • steaneLogicalOne.vec :=
      steaneLogicalZBar_hasEigenstate_logicalOne
    rwa [neg_one_smul] at h
  -- Conjugation relations rearranged: `X̄ U = U Z̄` and `U X̄ = Z̄ U`.
  have hXU : steaneLogicalXBar.comp U = U.comp steaneLogicalZBar := by
    rw [← hZX, Evolution.comp_assoc, Evolution.comp_assoc, Evolution.adjoint_comp_self',
      Evolution.comp_id]
  have hUX : U.comp steaneLogicalXBar = steaneLogicalZBar.comp U := by
    rw [← hXZ, Evolution.comp_assoc, Evolution.comp_assoc, Evolution.adjoint_comp_self',
      Evolution.comp_id]
  -- `X̄` fixes `ψ₀ = U|0_L⟩`.
  have hfixP : steaneLogicalXBar.evolvePure (U.evolvePure steaneLogicalZero)
      = U.evolvePure steaneLogicalZero := by
    rw [← Evolution.evolvePure_comp, hXU, Evolution.evolvePure_comp,
      steaneLogicalZBar_hasEigenstate_logicalZero.evolvePure_eq]
  have hfix : steaneLogicalXBar.op (U.evolvePure steaneLogicalZero).vec
      = (U.evolvePure steaneLogicalZero).vec := by
    rw [← Evolution.evolvePure_vec, hfixP]
  -- Extract `a = b` from `X̄ ψ₀ = ψ₀`.
  have key : a • steaneLogicalOne.vec + b • steaneLogicalZero.vec
      = a • steaneLogicalZero.vec + b • steaneLogicalOne.vec := by
    have h := hfix
    rw [hψ0, map_add, map_smul, map_smul, hX0, hX1] at h
    exact h
  have hab : a = b := by
    have hu := congrArg (inner ℂ steaneLogicalZero.vec) key
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right,
      inner_smul_right, PureState.inner_self] at hu
    have ho : inner ℂ steaneLogicalZero.vec steaneLogicalOne.vec = 0 := by
      rw [← PureState.overlap_def]; exact steaneLogical_overlap_eq_zero
    rw [ho] at hu
    simpa using hu.symm
  rw [← hab] at hψ0
  -- The unit-modulus scalar realizing "up to a global phase".
  set c : ℂ := a * (Real.sqrt 2 : ℂ) with hc
  have hr0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hcr : c * (Real.sqrt 2 : ℂ)⁻¹ = a := by
    rw [hc, mul_inv_cancel_right₀ hr0]
  -- `U|0_L⟩ = c • |+_L⟩`.
  have hvecP : (U.evolvePure steaneLogicalZero).vec = c • steaneLogicalPlus.vec := by
    rw [hψ0]
    simp only [steaneLogicalPlus, PureState.orthoPairOfOverlap_vec, smul_add, smul_smul, hcr]
  -- `U|1_L⟩ = Z̄ (U|0_L⟩) = c • |−_L⟩`.
  have hM : U.evolvePure steaneLogicalOne
      = steaneLogicalZBar.evolvePure (U.evolvePure steaneLogicalZero) := by
    rw [← steaneLogicalXBar_evolvePure_logicalZero, ← Evolution.evolvePure_comp, hUX,
      Evolution.evolvePure_comp]
  have hvecM : (U.evolvePure steaneLogicalOne).vec = c • steaneLogicalMinus.vec := by
    rw [hM, Evolution.evolvePure_vec, hψ0, map_add, map_smul, map_smul, hZ0, hZ1]
    simp only [steaneLogicalMinus, PureState.orthoPairOfOverlap_vec, smul_add, smul_smul, hcr,
      smul_neg, neg_smul]
  -- `‖c‖ = 1` from both sides being unit vectors.
  have hcnorm : ‖c‖ = 1 := by
    have h1 := (U.evolvePure steaneLogicalZero).normalized
    rw [hvecP, norm_smul, steaneLogicalPlus.normalized, mul_one] at h1
    exact h1
  -- The **shared** phase: both overlaps equal `conj c`, so the two column phases coincide (with
  -- the two `toState` equalities this pins `U|0_L⟩ = c·|+_L⟩`, `U|1_L⟩ = c·|−_L⟩` for one `c`).
  have hphase : (U.evolvePure steaneLogicalZero).overlap steaneLogicalPlus
      = (U.evolvePure steaneLogicalOne).overlap steaneLogicalMinus := by
    rw [PureState.overlap_def, PureState.overlap_def, hvecP, hvecM, inner_smul_left,
      inner_smul_left, PureState.inner_self, PureState.inner_self]
  exact ⟨PureState.toState_eq_of_vec_eq_smul hcnorm hvecP,
    PureState.toState_eq_of_vec_eq_smul hcnorm hvecM, hphase⟩

end AxQM
