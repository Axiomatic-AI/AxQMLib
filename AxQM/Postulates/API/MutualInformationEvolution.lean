/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MutualInformation
import AxQM.Postulates.API.EntropyEvolution
import AxQM.Postulates.Composite
import ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# AxQM — invariance of the quantum mutual information under a local unitary

Applying a unitary `V` to *one* subsystem of a bipartite state leaves the quantum mutual information
unchanged:

`S(A : B) = S(A : V B V†)`   (here the unitary acts on the second, `B`, factor).

Physically: a *local* reversible operation on one party creates and destroys no correlations between
the two parties. Formally this is the special case of Nielsen & Chuang's **Theorem 11.15(3)**
(quantum operations never increase mutual information, p. 523) for a **unitary** operation — for
which the inequality is in fact an equality, since a unitary can be undone.

It is also the second ingredient (labelled *(b)* in `EntropyEvolution`) of N&C's proof of the full
Theorem 11.15(3): that proof dilates a channel on `B` to a unitary interaction `U` on `B ⊗ C` with a
pure ancilla, and uses that this local unitary on the `B ⊗ C` factor leaves the mutual information
`S(A : B, C)` unchanged. The remaining ingredients are the entropy-invariance lemma
`State.vonNeumannEntropy_evolve` (ingredient *(a)*, already proved) and the discarding step, which
reduces to Theorem 11.15(2) but is blocked on a positivity-free data-processing inequality (see the
`## Toward Theorem 11.15(3)` note in `EntropyEvolution`).

## Proof

The mutual information `S(A : B) = S(A) + S(B) − S(A, B)` is invariant because each of its three
terms is:

* `S(A, B)` — the joint entropy — is unchanged by *any* unitary evolution
  (`State.vonNeumannEntropy_evolve`);
* the marginal on the *untouched* party `A` (`reducedLeft`) is literally unchanged
  (`State.reducedLeft_evolve_id_tmul`): tracing out `B` after conjugating it by a unitary is the
  same trace, by the naturality of the partial trace under a unitary on the traced factor
  (`LinearMap.partialTraceRight_conjStarAlgEquiv_congrIsometry`);
* the marginal on the *acted-on* party `B` transforms covariantly, `ρ_B ↦ V ρ_B V†`
  (`State.reducedRight_evolve_id_tmul`), because the identity on the traced-out `A` factor passes
  through the partial trace (`LinearMap.partialTraceLeft_tensorMap_id_comp` and its companion
  `…_comp_tensorMap_id`); its entropy is then unchanged by `State.vonNeumannEntropy_evolve`.

The statements involve no faithfulness hypothesis (the result is positivity-free, like
`State.vonNeumannEntropy_evolve`).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **The isometry equivalence of a tensor of evolutions is the tensor of their isometry
equivalences.** `(U ⊗ V).toIsometryEquiv = congrIsometry U.toIsometryEquiv V.toIsometryEquiv`. The
`Evolution` analogue of `QSystem.Iso.tmul_toIsometry`. Proved by `TensorProduct.ext'`: both sides
act on a pure tensor `a ⊗ b` as `U a ⊗ V b` (definitionally), sidestepping the `QSystem.compose`
instance diamond that blocks a `mapL`-level rewrite. -/
theorem Evolution.tmul_toIsometryEquiv (U : Evolution S) (V : Evolution T) :
    (U.tmul V).toIsometryEquiv
      = TensorProduct.congrIsometry U.toIsometryEquiv V.toIsometryEquiv := by
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  intro a b
  rfl

/-- **The identity evolution's isometry equivalence is the identity.**
`Evolution.id.toIsometryEquiv = LinearIsometryEquiv.refl`. -/
theorem Evolution.id_toIsometryEquiv :
    (Evolution.id (S := S)).toIsometryEquiv = LinearIsometryEquiv.refl ℂ S.space := by
  refine LinearIsometryEquiv.ext fun x => ?_
  rw [Evolution.toIsometryEquiv_apply, Evolution.id_op]
  rfl

/-- **A local unitary on the untouched party leaves its marginal unchanged.** For a state `ρ` on
`S ⊗ T` and a unitary `V` on the right factor `T`, the reduced state on the *left* factor `S` of
`(I_S ⊗ V) ρ (I_S ⊗ V)†` equals `ρ.reducedLeft`. Tracing out `T` after conjugating it by the unitary
`V` gives the same `S`-marginal, by the naturality of the partial trace under a unitary on the
traced factor (`LinearMap.partialTraceRight_conjStarAlgEquiv_congrIsometry`, transported across the
basis change with `LinearMap.partialTraceRight_eq_of_basis`). The mixed-state companion of
`PureState.reducedLeft_evolvePure_tmul_id`. -/
theorem State.reducedLeft_evolve_id_tmul (V : Evolution T) (ρ : State (S ⊗ T)) :
    (((Evolution.id (S := S)).tmul V).evolve ρ).reducedLeft = ρ.reducedLeft := by
  ext1
  rw [State.reducedLeft_op, State.reducedLeft_op]
  congr 1
  -- `I_S ⊗ V` is the tensor isometry `refl_S ⊗ V` (`Evolution.tmul_toIsometryEquiv`); tracing out
  -- `T` after conjugating by it is the naturality lemma below, up to a basis change.
  rw [Evolution.evolve_op_conjStarAlgEquiv, Evolution.tmul_toIsometryEquiv,
    Evolution.id_toIsometryEquiv,
    ← LinearMap.partialTraceRight_conjStarAlgEquiv_congrIsometry
        (stdOrthonormalBasis ℂ T.space) V.toIsometryEquiv ρ.op]
  exact LinearMap.partialTraceRight_eq_of_basis _ _ _

/-- **A local unitary on one party transforms that party's marginal covariantly.** For a state `ρ`
on `S ⊗ T` and a unitary `V` on the right factor `T`, the reduced state on the *right* factor `T` of
`(I_S ⊗ V) ρ (I_S ⊗ V)†` equals `V ρ_B V†` (`V.evolve ρ.reducedRight`). The identity on the
traced-out `S` factor passes straight through the partial trace over `S`
(`LinearMap.partialTraceLeft_tensorMap_id_comp` and `…_comp_tensorMap_id`), leaving the conjugation
by `V` acting on the surviving `T`-marginal. -/
theorem State.reducedRight_evolve_id_tmul (V : Evolution T) (ρ : State (S ⊗ T)) :
    (((Evolution.id (S := S)).tmul V).evolve ρ).reducedRight = V.evolve ρ.reducedRight := by
  -- Express the evolved operator as `(I_S ⊗ V) ρ (I_S ⊗ V)†` at the linear-map level. The adjoint
  -- of `I_S ⊗ V` is `I_S ⊗ V†`; we push it through `TensorProduct.map` via `adjoint_map` under a
  -- `congr` (the `QSystem.compose` instance blocks a direct rewrite; `exact` unifies up to defeq).
  -- The underlying operator of `(Evolution.id).tmul V`, bridged to the generic
  -- `TensorProduct.map` form: proved
  -- in isolation (no `ρ.op`/other bundled sibling adjacent via `∘ₗ`), so `Evolution.tmul_op`/
  -- `Evolution.id_op`/`TensorProduct.toLinearMap_mapL` fire by ordinary syntactic matching.
  have hW : (((Evolution.id (S := S)).tmul V).op).toLinearMap
      = TensorProduct.map LinearMap.id V.op.toLinearMap := by
    rw [Evolution.tmul_op, Evolution.id_op, TensorProduct.toLinearMap_mapL,
      ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id]
  have hWadj : (ContinuousLinearMap.adjoint (((Evolution.id (S := S)).tmul V).op)).toLinearMap
      = TensorProduct.map LinearMap.id (LinearMap.adjoint V.op.toLinearMap) := by
    rw [ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace, hW]
    refine (TensorProduct.adjoint_map (LinearMap.id : S.space →ₗ[ℂ] S.space)
      V.op.toLinearMap).trans ?_
    rw [LinearMap.adjoint_id]
  -- `ρ.op` (an atomic `State (S ⊗ T)`, not itself built from a further `TensorProduct.mapL`) has no
  -- rewrite lemma handing it a generic-instanced form to swap to — name it at the generic type via
  -- `let` (zeta-transparent), then bridge the whole composite via `hkey`, stated fresh with `ρopLM`
  -- anchoring both `∘ₗ` nodes at the generic instances throughout, and closed by rewriting with the
  -- already-isolated `hW`/`hWadj` (no diamond left to cross inside `hkey`'s own proof).
  let ρopLM : S.space ⊗[ℂ] T.space →ₗ[ℂ] S.space ⊗[ℂ] T.space := ρ.op.toLinearMap
  have hkey : TensorProduct.map LinearMap.id V.op.toLinearMap ∘ₗ ρopLM
      ∘ₗ TensorProduct.map LinearMap.id (LinearMap.adjoint V.op.toLinearMap)
      = (((Evolution.id (S := S)).tmul V).op).toLinearMap ∘ₗ ρopLM
          ∘ₗ (ContinuousLinearMap.adjoint (((Evolution.id (S := S)).tmul V).op)).toLinearMap := by
    rw [hW, hWadj]
    rfl
  have hbridge : (((Evolution.id (S := S)).tmul V).evolve ρ).op.toLinearMap
      = TensorProduct.map LinearMap.id V.op.toLinearMap ∘ₗ ρ.op.toLinearMap
          ∘ₗ TensorProduct.map LinearMap.id (LinearMap.adjoint V.op.toLinearMap) := by
    rw [Evolution.evolve_op]
    simp only [ContinuousLinearMap.toLinearMap_comp]
    exact hkey.symm
  ext1
  rw [State.reducedRight_op, hbridge, LinearMap.partialTraceLeft_tensorMap_id_comp]
  apply ContinuousLinearMap.coe_injective
  rw [LinearMap.coe_toContinuousLinearMap, Evolution.evolve_op,
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
    State.reducedRight_op, LinearMap.coe_toContinuousLinearMap,
    ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace]
  congr 1
  exact LinearMap.partialTraceLeft_comp_tensorMap_id (stdOrthonormalBasis ℂ S.space)
    (LinearMap.adjoint V.op.toLinearMap) ρ.op.toLinearMap

/-- **Quantum mutual information is invariant under a local unitary.** For a bipartite state `ρ` on
`S ⊗ T`, applying a unitary `V` to the second party leaves the mutual information unchanged:
`S(A : V B V†) = S(A : B)`.

This is the equality case of Nielsen & Chuang Theorem 11.15(3) for a *unitary* operation — a local
reversible operation creates no correlations — and the local-unitary-invariance ingredient of N&C's
proof of the general (channel) statement. Each term of `S(A:B) = S(A) + S(B) − S(A,B)` is preserved:
the joint entropy and the acted-on marginal's entropy by unitary invariance of the entropy
(`State.vonNeumannEntropy_evolve`), and the untouched marginal itself is unchanged
(`State.reducedLeft_evolve_id_tmul`). -/
theorem State.vonNeumannMutualInfo_evolve_id_tmul (V : Evolution T) (ρ : State (S ⊗ T)) :
    (((Evolution.id (S := S)).tmul V).evolve ρ).vonNeumannMutualInfo = ρ.vonNeumannMutualInfo := by
  simp only [State.vonNeumannMutualInfo_def, State.reducedLeft_evolve_id_tmul,
    State.reducedRight_evolve_id_tmul, State.vonNeumannEntropy_evolve]

end AxQM
