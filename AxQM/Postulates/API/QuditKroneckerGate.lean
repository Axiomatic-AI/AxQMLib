/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuditGate
import AxQM.Postulates.API.QuditTensorFactor
import AxQM.Postulates.API.LeftPairGate
import AxQM.Postulates.API.CnotPauliPropagation
import AxQM.Concrete.KroneckerReindex
import ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# The `quditGate` of a Kronecker product as a tensor product of `quditGate`s

The `quditGate` promotion (`AxQM/Postulates/API/QuditGate.lean`) turns a `d × d` unitary matrix
into an `Evolution (qudit d)`. This file relates the promotion of a **Kronecker product** to the
tensor product of the two factors' promotions, through the register-factoring isomorphism
`quditProdIso d e : qudit (d · e) ≃ₛ (qudit d) ⊗ (qudit e)`:

  `quditGate (kroneckerFin A B)
    = Evolution.congr (quditProdIso d e).symm (quditGate A ⊗ quditGate B)`,

where `kroneckerFin A B` (`AxQM/Concrete/KroneckerReindex.lean`) is the Kronecker product
`A ⊗ₖ B` packed into the flat index `Fin (d · e)` along `finProdFinEquiv` — exactly the index
convention `quditProdIso` uses. In words: a gate that acts as `A` on the first register factor and
`B` on the second *is* the composite gate `A ⊗ B`, once the flat `d · e`-level register is
identified with the bipartite `d`-by-`e` system.

## Use in Exercise 4.44

This is the general, register-agnostic form of the tensor-split step in the Deutsch-gate
universality reduction (Nielsen & Chuang, Exercise 4.44). A `G`-placement matrix on the
leading three wires of a larger register factors as `C²(·) ⊗ₖ 1` (its action on the other wires is
trivial); this bridge then reads its `quditGate` as the physical doubly-controlled gate on the first
factor tensored with the identity on the rest — the shape from which the physical Deutsch gate
`deutschGate α` is named. Stating it for a general `B` (not only `B = 1`) keeps the law reusable.

## The construction

* `quditGate_kroneckerFin_eq_congr_tmul` — the bridge above, proved by evaluating both operators on
  the computational basis `|finProdFinEquiv (x, y)⟩` of `qudit (d · e)` (`Module.Basis.ext`). The
  matrix side reads off the `(x, y)`-column of the packed Kronecker product; the tensor side
  transports the same column factorwise through `quditProdIso`
  (`quditProdIso_symm_congr_quditBasis`, `Evolution.congr_evolvePure_congr`), and the two coincide
  entry-by-entry.
-/

namespace AxQM

open scoped TensorProduct

noncomputable section

variable {d e : ℕ}

/-- **The packed-Kronecker column read off the matrix side.** Applying
`quditGate (kroneckerFin A B)` to the computational basis vector `|finProdFinEquiv (x, y)⟩` gives
the `(x, y)`-column of the packed Kronecker product, expanded over the packed basis:
`∑_{(s,t)} A_{sx} B_{ty} |finProdFinEquiv (s,t)⟩`. Reads the column off the general
`quditGate_op_quditBasis_vec`, then reindexes the sum along `finProdFinEquiv` and reads each entry
with `kroneckerFin_apply`. -/
private theorem quditGate_kroneckerFin_op_single {A : Matrix (Fin d) (Fin d) ℂ}
    {B : Matrix (Fin e) (Fin e) ℂ}
    (hAB : Concrete.kroneckerFin A B ∈ Matrix.unitaryGroup (Fin (d * e)) ℂ)
    (x : Fin d) (y : Fin e) :
    (quditGate hAB).op (EuclideanSpace.single (finProdFinEquiv (x, y)) 1)
      = ∑ p : Fin d × Fin e, (A p.1 x * B p.2 y) •
          EuclideanSpace.single (finProdFinEquiv p) (1 : ℂ) := by
  rw [← quditBasis_vec (finProdFinEquiv (x, y)),
    quditGate_op_quditBasis_vec hAB, ← Equiv.sum_comp finProdFinEquiv
      (fun k => Concrete.kroneckerFin A B k (finProdFinEquiv (x, y)) • (quditBasis k).vec)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  obtain ⟨s, t⟩ := p
  rw [Concrete.kroneckerFin_apply]
  congr 1

/-- **The packed-Kronecker column read off the tensor side.** Applying the transported tensor gate
`Evolution.congr (quditProdIso d e).symm (quditGate A ⊗ quditGate B)` to `|finProdFinEquiv (x, y)⟩`
gives the same column `∑_{(s,t)} A_{sx} B_{ty} |finProdFinEquiv (s,t)⟩`. The basis vector is the
`quditProdIso`-image of the product state `|x⟩ ⊗ |y⟩`, so the transport law
`Evolution.congr_evolvePure_congr` sends the problem to computing `quditGate A ⊗ quditGate B` on
`|x⟩ ⊗ |y⟩` — the tensor of the two matrix columns — and transporting that factorwise back through
`(quditProdIso d e).symm.toIsometry`, which returns each `|s⟩ ⊗ |t⟩` to
`|finProdFinEquiv (s,t)⟩`. -/
private theorem congr_symm_tmul_op_single {A : Matrix (Fin d) (Fin d) ℂ}
    {B : Matrix (Fin e) (Fin e) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin e) ℂ) (x : Fin d) (y : Fin e) :
    (Evolution.congr (quditProdIso d e).symm ((quditGate hA).tmul (quditGate hB))).op
        (EuclideanSpace.single (finProdFinEquiv (x, y)) 1)
      = ∑ p : Fin d × Fin e, (A p.1 x * B p.2 y) •
          EuclideanSpace.single (finProdFinEquiv p) (1 : ℂ) := by
  -- The symm-isometry returns each product basis vector to the packed basis vector.
  have hrec : ∀ (s : Fin d) (t : Fin e), (quditProdIso d e).symm.toIsometry
        ((quditBasis s).vec ⊗ₜ[ℂ] (quditBasis t).vec)
      = EuclideanSpace.single (finProdFinEquiv (s, t)) (1 : ℂ) := fun s t => by
    rw [← PureState.tmul_vec, ← PureState.congr_vec, quditProdIso_symm_congr_quditBasis,
      quditBasis_vec]
  -- The tensor of the two column sums is one packed double sum of scaled product basis tensors.
  have htensor : (∑ s : Fin d, A s x • (quditBasis s).vec)
        ⊗ₜ[ℂ] (∑ t : Fin e, B t y • (quditBasis t).vec)
      = ∑ p : Fin d × Fin e, (A p.1 x * B p.2 y) •
          ((quditBasis p.1).vec ⊗ₜ[ℂ] (quditBasis p.2).vec) := by
    rw [TensorProduct.sum_tmul, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  rw [← quditBasis_vec (finProdFinEquiv (x, y)),
    ← Evolution.evolvePure_vec, ← quditProdIso_symm_congr_quditBasis,
    Evolution.congr_evolvePure_congr, PureState.congr_vec, Evolution.evolvePure_vec,
    PureState.tmul_vec, Evolution.tmul_op_tmul,
    quditGate_op_quditBasis_vec hA, quditGate_op_quditBasis_vec hB, htensor]
  -- Push the isometry through the packed sum factorwise (`map_sum` on its linear map).
  refine (map_sum (quditProdIso d e).symm.toIsometry.toLinearMap
      (fun p : Fin d × Fin e => (A p.1 x * B p.2 y) •
        ((quditBasis p.1).vec ⊗ₜ[ℂ] (quditBasis p.2).vec)) Finset.univ).trans ?_
  refine Finset.sum_congr rfl (fun p _ => ?_)
  obtain ⟨s, t⟩ := p
  erw [map_smul]
  exact congrArg _ (hrec s t)

/-- **The `quditGate` of a packed Kronecker product is a transported tensor product of
`quditGate`s.** (Nielsen & Chuang, Exercise 4.44.) For unitary matrices `A` on `Fin d`
and `B` on
`Fin e`, the gate of the packed Kronecker product `kroneckerFin A B` on `qudit (d · e)` is the
tensor product gate `quditGate A ⊗ quditGate B` on `(qudit d) ⊗ (qudit e)`, transported back along
register-factoring isomorphism `quditProdIso d e`:

  `quditGate hAB = Evolution.congr (quditProdIso d e).symm ((quditGate hA).tmul (quditGate hB))`.

An evolution is determined by its operator (`Evolution.ext`), and the operators agree on the
computational basis `|finProdFinEquiv (x, y)⟩` of `qudit (d · e)` (`Module.Basis.ext`): both sides
produce the `(x, y)`-column `∑_{(s,t)} A_{sx} B_{ty} |finProdFinEquiv (s,t)⟩` — the matrix side by
`toEuclideanCLM`'s column formula, the tensor side by transporting the tensor of the two matrix
columns factorwise through `quditProdIso`.

This is the general form of the tensor-split step naming the physical Deutsch gate `deutschGate α`
in its universality reduction: with `B = 1` the identity on the trailing register wires, the
`G`-placement's `quditGate` is `deutschGate α` (transported to `qudit 8`) tensored with the
identity. -/
theorem quditGate_kroneckerFin_eq_congr_tmul {A : Matrix (Fin d) (Fin d) ℂ}
    {B : Matrix (Fin e) (Fin e) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin e) ℂ)
    (hAB : Concrete.kroneckerFin A B ∈ Matrix.unitaryGroup (Fin (d * e)) ℂ) :
    quditGate hAB
      = Evolution.congr (quditProdIso d e).symm ((quditGate hA).tmul (quditGate hB)) := by
  apply Evolution.ext
  apply ContinuousLinearMap.coe_injective
  refine Module.Basis.ext (EuclideanSpace.basisFun (Fin (d * e)) ℂ).toBasis (fun k => ?_)
  obtain ⟨⟨x, y⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  have h := (quditGate_kroneckerFin_op_single hAB x y).trans
    (congr_symm_tmul_op_single hA hB x y).symm
  convert h using 0

end

end AxQM
