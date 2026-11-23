/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.StateMajorization
import AxQM.Postulates.API.StateTensorEigenbasis
import AxQM.Postulates.API.GeneralizedDepolarizingChannel
import AxQM.Concrete.EntanglementCatalysis
import ToMathlib.Analysis.InnerProductSpace.DiagonalOperatorEntropy

/-!
# AxQM.Postulates.API — reduced states of the entanglement-catalysis example

The part of Nielsen & Chuang, Exercise 12.21 (entanglement catalysis): the
reduced density operators of the three bipartite pure states, built as diagonal `State`s on qudits
with the squared-Schmidt spectra of `AxQM.Concrete.EntanglementCatalysis`, together with
the identification of each state's canonical eigenvalue distribution (`State.eigenvalueDist`) with
its concrete spectrum *up to a permutation* (i.e. as a `Multiset`).

The theorems of the exercise — `catalysisState_not_loccConvertible` and
`catalysisState_tmul_loccConvertible`, stated for `State.LOCCConvertible` — are proved from
these facts (via Nielsen's theorem) in `AxQM/NC/Ch12/Exercise12_21.lean`.

## Main definitions

* `catalysisStatePsi`, `catalysisStatePhi` : `State (qudit 4)`, `catalysisStateCat` : `State
  (qudit 2)` — the reduced states, diagonal in the computational basis with spectra `λ_ψ`, `λ_φ`,
  `λ_c`.

## Main statements

* `catalysisStatePsi_eigenvalueDist_multiset` / `catalysisStatePhi_eigenvalueDist_multiset` — the
  eigenvalue distribution of `ρ_ψ` / `ρ_φ` has the same multiset as `λ_ψ` / `λ_φ`.
* `catalysisStatePsiCat_eigenvalueDist_multiset` / `catalysisStatePhiCat_eigenvalueDist_multiset` —
  the eigenvalue distribution of `ρ_ψ ⊗ ρ_c` / `ρ_φ ⊗ ρ_c` has the same multiset as the product
  spectrum `λ_ψ ⊗ λ_c` / `λ_φ ⊗ λ_c`.
-/

open Finset AxQM.Concrete

namespace AxQM

/-- The reduced density operator of the source state `|ψ⟩ = √0.4|00⟩ + √0.4|11⟩ + √0.1|22⟩ +
√0.1|33⟩` of the catalysis example (N&C Exercise 12.21): the diagonal state on `qudit 4` with the
squared-Schmidt spectrum `λ_ψ = (0.4, 0.4, 0.1, 0.1)`. -/
noncomputable def catalysisStatePsi : State (qudit 4) where
  op := (quditOrthonormalBasis 4).diagonalOperator fun i => (catalysisPsiSpec i : ℂ)
  isDensity := (quditOrthonormalBasis 4).diagonalOperator_isDensityOp
    catalysisPsiSpec_nonneg catalysisPsiSpec_sum_eq_one

/-- The reduced density operator of the target state `|φ⟩ = √0.5|00⟩ + √0.25|11⟩ + √0.25|22⟩` of the
catalysis example (N&C Exercise 12.21): the diagonal state on `qudit 4` with the squared-Schmidt
spectrum `λ_φ = (0.5, 0.25, 0.25, 0)`. -/
noncomputable def catalysisStatePhi : State (qudit 4) where
  op := (quditOrthonormalBasis 4).diagonalOperator fun i => (catalysisPhiSpec i : ℂ)
  isDensity := (quditOrthonormalBasis 4).diagonalOperator_isDensityOp
    catalysisPhiSpec_nonneg catalysisPhiSpec_sum_eq_one

/-- The reduced density operator of the catalyst `|c⟩ = √0.6|00⟩ + √0.4|11⟩` (N&C Exercise 12.21):
the diagonal state on `qudit 2` with spectrum `λ_c = (0.6, 0.4)`. -/
noncomputable def catalysisStateCat : State (qudit 2) where
  op := (quditOrthonormalBasis 2).diagonalOperator fun i => (catalysisCatSpec i : ℂ)
  isDensity := (quditOrthonormalBasis 2).diagonalOperator_isDensityOp
    catalysisCatSpec_nonneg catalysisCatSpec_sum_eq_one

/-- The eigenvalue distribution of `ρ_ψ` has the same multiset as the spectrum `λ_ψ`: the
computational basis is a known-eigenvalue eigenbasis of `ρ_ψ`. -/
theorem catalysisStatePsi_eigenvalueDist_multiset :
    Multiset.map catalysisStatePsi.eigenvalueDist univ.val
      = Multiset.map catalysisPsiSpec univ.val :=
  catalysisStatePsi.eigenvalueDist_multiset_map_eq (quditOrthonormalBasis 4) catalysisPsiSpec
    fun i => (quditOrthonormalBasis 4).diagonalOperator_apply_self
      (fun k => (catalysisPsiSpec k : ℂ)) i

/-- The eigenvalue distribution of `ρ_φ` has the same multiset as the spectrum `λ_φ`. -/
theorem catalysisStatePhi_eigenvalueDist_multiset :
    Multiset.map catalysisStatePhi.eigenvalueDist univ.val
      = Multiset.map catalysisPhiSpec univ.val :=
  catalysisStatePhi.eigenvalueDist_multiset_map_eq (quditOrthonormalBasis 4) catalysisPhiSpec
    fun i => (quditOrthonormalBasis 4).diagonalOperator_apply_self
      (fun k => (catalysisPhiSpec k : ℂ)) i

/-- The eigenvalue distribution of `ρ_ψ ⊗ ρ_c` has the same multiset as the product spectrum
`λ_ψ ⊗ λ_c`: the tensor of computational bases is an eigenbasis of `ρ_ψ ⊗ ρ_c` with eigenvalues
`λ_ψ(i)·λ_c(j)`. -/
theorem catalysisStatePsiCat_eigenvalueDist_multiset :
    Multiset.map (catalysisStatePsi.tmul catalysisStateCat).eigenvalueDist univ.val
      = Multiset.map catalysisPsiTensorSpec univ.val :=
  (catalysisStatePsi.tmul catalysisStateCat).eigenvalueDist_multiset_map_eq
    ((quditOrthonormalBasis 4).tensorProduct (quditOrthonormalBasis 2)) catalysisPsiTensorSpec
    fun ij => State.tmul_op_tensorProduct_apply_self catalysisStatePsi catalysisStateCat
      (quditOrthonormalBasis 4) (quditOrthonormalBasis 2)
      (fun i => (quditOrthonormalBasis 4).diagonalOperator_apply_self
        (fun k => (catalysisPsiSpec k : ℂ)) i)
      (fun j => (quditOrthonormalBasis 2).diagonalOperator_apply_self
        (fun k => (catalysisCatSpec k : ℂ)) j) ij

/-- The eigenvalue distribution of `ρ_φ ⊗ ρ_c` has the same multiset as the product spectrum
`λ_φ ⊗ λ_c`. -/
theorem catalysisStatePhiCat_eigenvalueDist_multiset :
    Multiset.map (catalysisStatePhi.tmul catalysisStateCat).eigenvalueDist univ.val
      = Multiset.map catalysisPhiTensorSpec univ.val :=
  (catalysisStatePhi.tmul catalysisStateCat).eigenvalueDist_multiset_map_eq
    ((quditOrthonormalBasis 4).tensorProduct (quditOrthonormalBasis 2)) catalysisPhiTensorSpec
    fun ij => State.tmul_op_tensorProduct_apply_self catalysisStatePhi catalysisStateCat
      (quditOrthonormalBasis 4) (quditOrthonormalBasis 2)
      (fun i => (quditOrthonormalBasis 4).diagonalOperator_apply_self
        (fun k => (catalysisPhiSpec k : ℂ)) i)
      (fun j => (quditOrthonormalBasis 2).diagonalOperator_apply_self
        (fun k => (catalysisCatSpec k : ℂ)) j) ij

end AxQM
