/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SchmidtDecomposition
import AxQM.Postulates.API.Evolution
import ToMathlib.Analysis.InnerProductSpace.OrthonormalIsometry

/-!
# Nielsen & Chuang, Exercise 2.80 (identical Schmidt coefficients ⇒ related by `U ⊗ V`)

Two states with identical Schmidt coefficients related by (U⊗V).

The hypothesis is the predicate `PureState.SameSchmidtCoeffs` (identical Schmidt coefficients) and
the conclusion is an equation of pure states related by a composite **evolution** `U ⊗ V`
(`Evolution.tmul`) acting via `Evolution.evolvePure`.

## Formalisation

* `AxQM.PureState.exists_evolution_tmul_of_sameSchmidtCoeffs` — the exercise
  (Exercise 2.80): if `ψ` and `φ` have identical Schmidt coefficients then there exist evolutions
  `U` on `S` and `V` on `T` with `ψ = (U ⊗ V) φ`.
* `AxQM.PureState.sameSchmidtCoeffs_rfl` — `SameSchmidtCoeffs` is reflexive: every pure
  state has the same Schmidt coefficients as itself (via the Schmidt decomposition, Theorem 2.7).
  This witnesses that the hypothesis of the exercise is inhabited (so the theorem is not vacuous).

The hypothesis predicate `PureState.SameSchmidtCoeffs` and the Schmidt decomposition
`PureState.exists_schmidt_decomposition` are in `AxQM/Postulates/API/SchmidtDecomposition.lean`.

## Proof

Take the two reduced Schmidt decompositions supplied by the hypothesis, over a common coefficient
family `l : Fin n → ℝ`:

  `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩`,   `|φ⟩ = ∑ᵢ λᵢ |i'ᴬ⟩|i'ᴮ⟩`,

with `{|iᴬ⟩}`, `{|i'ᴬ⟩}` orthonormal in `S` and `{|iᴮ⟩}`, `{|i'ᴮ⟩}` orthonormal in `T`. Since
`{|iᴬ⟩}` and `{|i'ᴬ⟩}` are two orthonormal families of the same size, there is a linear isometry
equivalence of `S.space` sending `|i'ᴬ⟩ ↦ |iᴬ⟩`, and likewise on `T`
(`Orthonormal.exists_linearIsometryEquiv_apply_eq`, `ToMathlib`); package these as unitaries
`U : Evolution S`, `V : Evolution T` (`Evolution.ofLinearIsometryEquiv`). Then, term by term,

  `(U ⊗ V)|φ⟩ = ∑ᵢ λᵢ (U|i'ᴬ⟩) ⊗ (V|i'ᴮ⟩) = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩ = |ψ⟩`,

using `Evolution.tmul_op` and `TensorProduct.map_tmul` to distribute `U ⊗ V` over the tensor terms.

The direction `ψ = (U ⊗ V) φ` matches N&C: `U`, `V` carry `φ`'s Schmidt bases *to* `ψ`'s. Only this
forward implication is needed; the converse `φ = (U⁻¹ ⊗ V⁻¹) ψ` is the same statement with the
roles swapped (`SameSchmidtCoeffs` is symmetric).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **`SameSchmidtCoeffs` is reflexive**: every bipartite pure state has the same Schmidt
coefficients as itself. Immediate from the Schmidt decomposition (`exists_schmidt_decomposition`,
Nielsen–Chuang Theorem 2.7): use that single decomposition for both slots. This witnesses that the
hypothesis of Exercise 2.80 is satisfiable. -/
theorem PureState.sameSchmidtCoeffs_rfl (ψ : PureState (S ⊗ T)) : ψ.SameSchmidtCoeffs ψ := by
  obtain ⟨n, l, a, b, hl, ha, hb, _, hdecomp⟩ := ψ.exists_schmidt_decomposition
  exact ⟨n, l, a, a, b, b, hl, ha, hb, ha, hb, hdecomp, hdecomp⟩

/-- **Nielsen & Chuang, Exercise 2.80.** Two bipartite pure states `ψ`, `φ` with identical Schmidt
coefficients (`PureState.SameSchmidtCoeffs`) are related by a **local unitary**: there exist
evolutions `U` on `S` and `V` on `T` with `ψ = (U ⊗ V) φ`.

From the common Schmidt data `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩`, `|φ⟩ = ∑ᵢ λᵢ |i'ᴬ⟩|i'ᴮ⟩`, the orthonormal
Schmidt families `{|i'ᴬ⟩}`, `{|iᴬ⟩}` (resp. `{|i'ᴮ⟩}`, `{|iᴮ⟩}`) are related by a linear isometry
equivalence `LA : |i'ᴬ⟩ ↦ |iᴬ⟩` (resp. `LB : |i'ᴮ⟩ ↦ |iᴮ⟩`), by
`Orthonormal.exists_linearIsometryEquiv_apply_eq`. Packaging `LA`, `LB` as unitaries `U`, `V`
(`Unitary.linearIsometryEquiv`), the map `U ⊗ V` sends each `λᵢ |i'ᴬ⟩⊗|i'ᴮ⟩` to `λᵢ |iᴬ⟩⊗|iᴮ⟩`,
so `(U ⊗ V)|φ⟩ = |ψ⟩`. -/
theorem PureState.exists_evolution_tmul_of_sameSchmidtCoeffs {ψ φ : PureState (S ⊗ T)}
    (h : ψ.SameSchmidtCoeffs φ) :
    ∃ (U : Evolution S) (V : Evolution T), ψ = (U ⊗ V).evolvePure φ := by
  obtain ⟨n, l, a, a', b, b', hl, ha, hb, ha', hb', hψ, hφ⟩ := h
  -- Isometries carrying φ's Schmidt bases to ψ's Schmidt bases, packaged as evolutions `U`, `V`.
  obtain ⟨LA, hLA⟩ := Orthonormal.exists_linearIsometryEquiv_apply_eq ha ha'
  obtain ⟨LB, hLB⟩ := Orthonormal.exists_linearIsometryEquiv_apply_eq hb hb'
  refine ⟨.ofLinearIsometryEquiv LA, .ofLinearIsometryEquiv LB, ?_⟩
  -- `(U ⊗ V)` sends each Schmidt term of `φ` to the corresponding term of `ψ`.
  have key : ∀ i, (TensorProduct.mapL (Evolution.ofLinearIsometryEquiv LA).op
        (Evolution.ofLinearIsometryEquiv LB).op) ((l i : ℂ) • a' i ⊗ₜ[ℂ] b' i)
      = (l i : ℂ) • a i ⊗ₜ[ℂ] b i := by
    intro i
    rw [map_smul, TensorProduct.mapL_apply, TensorProduct.map_tmul,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
      Evolution.ofLinearIsometryEquiv_op_apply, Evolution.ofLinearIsometryEquiv_op_apply,
      hLA i, hLB i]
  apply PureState.ext
  rw [Evolution.evolvePure_vec, Evolution.tmul_op, hψ, hφ]
  exact (Finset.sum_congr rfl fun i _ => (key i).symm).trans
    (map_sum (TensorProduct.mapL (Evolution.ofLinearIsometryEquiv LA).op
      (Evolution.ofLinearIsometryEquiv LB).op) _ Finset.univ).symm

end AxQM
