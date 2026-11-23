/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuditGate
import AxQM.Postulates.API.PeriodShift

/-!
# AxQM.Postulates.API — a `quditGate` under a basis reindex is conjugation by `quditPerm`

The companion of the encoding-change bridge
(`AxQM/Concrete/WireGateEncodingChange.lean`): reindexing a unitary matrix's rows and columns by a
permutation `ρ : Equiv.Perm (Fin d)` — the `submatrix ρ ρ` — promotes, through `quditGate`, to
conjugation of the promoted evolution by the computational-basis permutation gate `quditPerm ρ`:

  `quditGate (M.submatrix ρ ρ) = quditPerm ρ.symm * quditGate M * quditPerm ρ`.

Physically this is the register-relabelling law for a gate: `M.submatrix ρ ρ` is the same operation
as `M` read against a `ρ`-permuted computational basis, and permuting the basis is exactly the gate
`quditPerm ρ`. It is the operator-level move that carries a matrix identity known against *one*
encoding of a register (the tensor-split encoding `regTensorEnc` of N&C Ex 4.44) onto *any* other
encoding, whose basis differs from it by such a permutation.

## What is formalised

* `quditGate_submatrix_eq_conj` — for a unitary `M ∈ U(d)`, a permutation `ρ` of the `d` basis
  labels, and the (also unitary) reindex `M.submatrix ρ ρ`,

    `quditGate (M.submatrix ρ ρ) = quditPerm ρ.symm * quditGate M * quditPerm ρ`.

  Proved by `Module.Basis.ext` over the computational basis: on `|z⟩` the left side is the `z`-th
  column of `M.submatrix ρ ρ`, `∑ₛ M (ρ s) (ρ z) |s⟩` (`quditGate_op_quditBasis_vec`,
  `submatrix_apply`), and the right side sends `|z⟩ ↦ |ρ z⟩` (`quditPerm ρ`) `↦ ∑ₛ M s (ρ z) |s⟩`
  (`quditGate M`) `↦ ∑ₛ M s (ρ z) |ρ⁻¹ s⟩` (`quditPerm ρ.symm`), which reindexes (`Equiv.sum_comp`)
  to the same sum.

Compare `QuditGate` (whose `quditGate` it reindexes) and `PeriodShift` (whose `quditPerm` it
conjugates by). The statement is fully generic, with no Nielsen & Chuang content.
-/

open Matrix

namespace AxQM

noncomputable section

/-- **A `quditGate` under a basis reindex is conjugation by the permutation gate.** For a unitary
matrix `M ∈ U(d)` and a permutation `ρ` of the `d` computational-basis labels, the promoted gate of
the row/column reindex `M.submatrix ρ ρ` is `quditGate M` conjugated by the basis-permutation gate
`quditPerm ρ`:

  `quditGate (M.submatrix ρ ρ) = quditPerm ρ.symm * quditGate M * quditPerm ρ`.

Both sides are read on the computational basis (`Module.Basis.ext` over `EuclideanSpace.basisFun`).
The left side is the `z`-th column `∑ₛ (M.submatrix ρ ρ) s z • |s⟩ = ∑ₛ M (ρ s) (ρ z) • |s⟩`
(`quditGate_op_quditBasis_vec`, `Matrix.submatrix_apply`). The right side applies, in order,
`quditPerm ρ` (`|z⟩ ↦ |ρ z⟩`), `quditGate M` (`|ρ z⟩ ↦ ∑ₛ M s (ρ z) • |s⟩`) and `quditPerm ρ.symm`
(`|s⟩ ↦ |ρ⁻¹ s⟩`, linearly), giving `∑ₛ M s (ρ z) • |ρ⁻¹ s⟩`, which the reindex `s ↦ ρ s`
(`Equiv.sum_comp`) turns into the same `∑ₛ M (ρ s) (ρ z) • |s⟩`. -/
theorem quditGate_submatrix_eq_conj {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin d) ℂ) (ρ : Equiv.Perm (Fin d))
    (hsub : M.submatrix ρ ρ ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quditGate hsub = quditPerm ρ.symm * quditGate hM * quditPerm ρ := by
  apply Evolution.ext
  apply ContinuousLinearMap.coe_injective
  refine Module.Basis.ext (EuclideanSpace.basisFun (Fin d) ℂ).toBasis (fun z => ?_)
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  have hlhs : (quditGate hsub).op (quditBasis z).vec
      = ∑ s, M (ρ s) (ρ z) • (quditBasis s).vec := by
    rw [quditGate_op_quditBasis_vec hsub]
    exact Finset.sum_congr rfl (fun s _ => by rw [Matrix.submatrix_apply])
  have hrhs : (quditPerm ρ.symm * quditGate hM * quditPerm ρ).op (quditBasis z).vec
      = ∑ s, M (ρ s) (ρ z) • (quditBasis s).vec := by
    rw [Evolution.mul_def, Evolution.mul_def, Evolution.comp_op, Evolution.comp_op]
    simp only [ContinuousLinearMap.comp_apply]
    rw [quditPerm_op_apply_quditBasis, quditGate_op_quditBasis_vec hM, map_sum]
    simp only [map_smul, quditPerm_op_apply_quditBasis]
    rw [← Equiv.sum_comp ρ fun x => M x (ρ z) • (quditBasis (ρ.symm x)).vec]
    simp only [Equiv.symm_apply_apply]
  rw [← quditBasis_vec z]
  exact hlhs.trans hrhs.symm

end

end AxQM
