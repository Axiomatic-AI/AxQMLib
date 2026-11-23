/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PhaseFlipStabilizer
import AxQM.Postulates.API.PauliEigen

/-!
# AxQM.Postulates.API — maximality of the phase-flip stabilizer `⟨X₁X₂, X₂X₃⟩`

Infrastructure for the **maximality** half of Nielsen & Chuang **Exercise 10.46**:
the stabilizer of the three-qubit *phase-flip* code (`|0_L⟩ = |+++⟩`, `|1_L⟩ = |−−−⟩`) is generated
by `X₁X₂` and `X₂X₃`. `PhaseFlipStabilizer.lean` built the two generators as observables
`xxIObservable = X ⊗ X ⊗ I`,
`ixxObservable = I ⊗ X ⊗ X`, together with their product `xixObservable = X ⊗ I ⊗ X` (`X₁X₃`), and
showed each fixes both codewords (**containment**: `⟨X₁X₂, X₂X₃⟩` stabilizes the code). This file
records the group law `X₁X₂ · X₂X₃ = X₁X₃` (so the generated group is the Klein-four group
`{I, X₁X₂, X₂X₃, X₁X₃}`) and proves that these two commuting involutions generate *exactly* the full
stabilizer.

## The maximality argument

A `[3, 1]` stabilizer code `C(S)` is by definition the joint `+1`-eigenspace of a set of commuting
generators; `S = ⟨g₁, g₂⟩` iff the code space is *precisely* the joint `+1`-eigenspace of `g₁, g₂`.
The joint `+1`-eigenprojector of two commuting `±1` involutions is the composition of their
individual `+1`-eigenprojectors `P₊(g) = ½(I + g)` (`Observable.projPlus`). So maximality is the
operator identity

  `phaseFlipCodeProj = P₊(X₁X₂) ∘ P₊(X₂X₃)`

(`phaseFlipCodeProj_eq_projPlus_comp`): the code projector `|+++⟩⟨+++| + |−−−⟩⟨−−−|` equals the
projector onto the joint `+1`-eigenspace of `X₁X₂` and `X₂X₃`. Both sides are read off on the eight
orthonormal `±`-basis vectors `pmThreeVec |σ₁σ₂σ₃⟩`: `P₊(X₁X₂) P₊(X₂X₃)` kills `|σ₁σ₂σ₃⟩` unless
`σ₁ = σ₂` *and* `σ₂ = σ₃` (i.e. `σ₁ = σ₂ = σ₃`), leaving exactly the two codewords `|+++⟩`, `|−−−⟩`;
`phaseFlipCodeProj` does the same via `pmThreeVec_inner`. Since the joint `+1`-eigenspace is thus
**exactly two-dimensional** (`= 2^k` with `k = 1` logical qubit and two independent generators), the
stabilizer has the full order `2^{3-1} = 4` and `⟨X₁X₂, X₂X₃⟩` is *the whole* stabilizer — not a
proper subgroup.

The eight `±`-basis vectors span the register (eight orthonormal vectors in the eight-dimensional
`qubit ⊗ (qubit ⊗ qubit)`), packaged as `pmThreeBasis`; operator identities on the register reduce
to their action on this basis (`eq_of_pmThreeVec`), the same device as `qubitModuleBasis` /
`Module.Basis.ext`.

## Commuting generators

The two generators commute (`xxIObservable_commute_ixxObservable`), so `⟨X₁X₂, X₂X₃⟩` is abelian —
the commuting-generator requirement for a stabilizer group. Together with the two-dimensional joint
`+1`-eigenspace this pins the group to the full order `2^{3-1} = 4`: two independent commuting `±1`
involutions whose common `+1`-eigenspace is exactly the code.

## Contents

* `pmThreeBasis` — the eight `±`-basis vectors `pmThreeVec` as a `Module.Basis` of the register;
  `eq_of_pmThreeVec` reduces an operator identity to its action on them.
* `xxIObservable_commute_ixxObservable` — the generators commute (`⟨X₁X₂, X₂X₃⟩` is abelian).
* `xxIObservable_op_mul_ixxObservable` — the group law `X₁X₂ · X₂X₃ = X₁X₃`: the two generators
  produce the third stabilizer element `xixObservable`, so `⟨X₁X₂, X₂X₃⟩ = {I, X₁X₂, X₂X₃, X₁X₃}`.
* `phaseFlipCodeProj_eq_projPlus_comp` — **maximality**: `phaseFlipCodeProj = P₊(X₁X₂) ∘ P₊(X₂X₃)`,
  i.e. the code space is exactly the joint `+1`-eigenspace, so `⟨X₁X₂, X₂X₃⟩` is the full
  stabilizer.

The `HasEigenstate` containment statements are in `AxQM/NC/Ch10/Exercise10_46.lean`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-! ### The `±` basis of the three-qubit register -/

/-- **The three-qubit register is eight-dimensional:** `dim (qubit ⊗ (qubit ⊗ qubit)) = 8`, from
`finrank_qubit_space = 2` and multiplicativity of `finrank` over tensor products. -/
theorem finrank_bitFlipReg : Module.finrank ℂ (qubit ⊗ (qubit ⊗ qubit)).space = 8 := by
  change Module.finrank ℂ
    (TensorProduct ℂ qubit.space (TensorProduct ℂ qubit.space qubit.space)) = 8
  rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct, finrank_qubit_space]

/-- **The eight `±`-basis vectors are orthonormal** (`Orthonormal`-packaged `pmThreeVec_inner`). -/
theorem pmThreeVec_orthonormal : Orthonormal ℂ pmThreeVec :=
  orthonormal_iff_ite.mpr pmThreeVec_inner

/-- **The eight `±`-basis vectors `|σ₁σ₂σ₃⟩` as a `ℂ`-basis of the register.** They are orthonormal
(`pmThreeVec_orthonormal`) and number `8 = dim (qubit ⊗ (qubit ⊗ qubit))` (`finrank_bitFlipReg`), so
they form a `Module.Basis`; this is what lets an operator identity be checked on the `±` basis. -/
def pmThreeBasis : Module.Basis (Fin 2 × Fin 2 × Fin 2) ℂ (qubit ⊗ (qubit ⊗ qubit)).space :=
  basisOfLinearIndependentOfCardEqFinrank pmThreeVec_orthonormal.linearIndependent
    (by rw [finrank_bitFlipReg]; rfl)

/-- The `s`-th vector of `pmThreeBasis` is the `±`-basis vector `pmThreeVec s = |σ₁σ₂σ₃⟩`. -/
@[simp] theorem pmThreeBasis_apply (s : Fin 2 × Fin 2 × Fin 2) : pmThreeBasis s = pmThreeVec s :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) s

/-- **Operator extensionality on the `±` basis:** two operators out of the register agree iff they
agree on the eight basis vectors `pmThreeVec s`. Reduces every operator identity below to a check on
the `±` basis (`Module.Basis.ext` on `pmThreeBasis`). -/
theorem eq_of_pmThreeVec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : (qubit ⊗ (qubit ⊗ qubit)).space →L[ℂ] E}
    (h : ∀ s, f (pmThreeVec s) = g (pmThreeVec s)) : f = g := by
  apply ContinuousLinearMap.coe_injective
  refine Module.Basis.ext pmThreeBasis fun s => ?_
  simpa only [pmThreeBasis_apply, ContinuousLinearMap.coe_coe] using h s

/-! ### Commutativity of the generators -/

/-- **The two stabilizer generators commute:** `X₁X₂ · X₂X₃ = X₂X₃ · X₁X₂`. So `⟨X₁X₂, X₂X₃⟩` is
abelian — the commuting-generator requirement for a stabilizer group. -/
theorem xxIObservable_commute_ixxObservable :
    Commute xxIObservable.op ixxObservable.op := by
  refine eq_of_pmThreeVec fun s => ?_
  obtain ⟨a, b, c⟩ := s
  rw [mul_apply_eq_comp, ixxObservable_op_pmThreeVec, map_smul,
    xxIObservable_op_pmThreeVec, mul_apply_eq_comp, xxIObservable_op_pmThreeVec,
    map_smul, ixxObservable_op_pmThreeVec, smul_smul, smul_smul, mul_comm]

/-! ### The group law: the two generators produce the third stabilizer element -/

/-- **The stabilizer group law `X₁X₂ · X₂X₃ = X₁X₃`.** The product of the two generators is the
third nontrivial stabilizer element `X₁X₃` (`xixObservable`): on `|σ₁σ₂σ₃⟩` the signs
`(−1)^{σ₁+σ₂}` and `(−1)^{σ₂+σ₃}` multiply to `(−1)^{σ₁+2σ₂+σ₃} = (−1)^{σ₁+σ₃}`, the sign of `X₁X₃`.
Hence the group generated by `X₁X₂` and `X₂X₃` is exactly the Klein-four group
`{I, X₁X₂, X₂X₃, X₁X₃}`, and all of its elements stabilize the code (`⟨X₁X₂, X₂X₃⟩ ⊆ S`): the
identity trivially, the two generators and their product `X₁X₃` by their `+1`-eigenstate laws.

Proved by evaluating both operators on the `±` basis via `eq_of_pmThreeVec` — the same
eigenbasis-extensionality route as `xxIObservable_commute_ixxObservable`, which avoids computing the
tensor-operator product structurally. -/
theorem xxIObservable_op_mul_ixxObservable :
    xxIObservable.op * ixxObservable.op = xixObservable.op := by
  refine eq_of_pmThreeVec fun s => ?_
  obtain ⟨a, b, c⟩ := s
  rw [mul_apply_eq_comp, ixxObservable_op_pmThreeVec, map_smul,
    xxIObservable_op_pmThreeVec, xixObservable_op_pmThreeVec, smul_smul, ← pow_add]
  congr 1
  fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num

/-! ### Maximality: the code is the joint `+1`-eigenspace of the generators -/

/-- **Nielsen & Chuang, Exercise 10.46 (maximality).** The phase-flip code projector equals the
projector onto the joint `+1`-eigenspace of the two generators:
`phaseFlipCodeProj = P₊(X₁X₂) ∘ P₊(X₂X₃)`. Read off on the `±` basis, `P₊(X₁X₂) P₊(X₂X₃)` fixes
`|σ₁σ₂σ₃⟩` exactly when `σ₁ = σ₂ = σ₃` — i.e. exactly on the two-dimensional codeword span. Hence
the code space is *precisely* the stabilized subspace of `⟨X₁X₂, X₂X₃⟩`; the stabilizer has the full
order `2^{3-1} = 4` and `⟨X₁X₂, X₂X₃⟩` is the whole stabilizer, not a proper subgroup. -/
theorem phaseFlipCodeProj_eq_projPlus_comp :
    phaseFlipCodeProj = xxIObservable.projPlus.comp ixxObservable.projPlus := by
  refine eq_of_pmThreeVec fun s => ?_
  obtain ⟨a, b, c⟩ := s
  rw [ContinuousLinearMap.comp_apply,
    ixxObservable.projPlus_apply_smul (ixxObservable_op_pmThreeVec (a, b, c)), map_smul,
    xxIObservable.projPlus_apply_smul (xxIObservable_op_pmThreeVec (a, b, c)), smul_smul]
  simp only [phaseFlipCodeProj, Fin.sum_univ_two, _root_.add_apply,
    InnerProductSpace.rankOne_apply, phaseFlipCodeword, pmThreeVec_inner]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num [Prod.ext_iff]

end AxQM
