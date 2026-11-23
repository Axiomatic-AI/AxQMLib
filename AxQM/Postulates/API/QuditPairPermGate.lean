/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.API.Qudit
import AxQM.Postulates.Composite
import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM.Postulates.API — the two-register computational-basis permutation gate

The *classical reversible circuit* on a pair of qudit registers: given a
permutation `σ` of the joint computational-basis labels `Fin d × Fin e`, the gate `quditPairPerm σ`
is the unitary `Evolution` of `qudit d ⊗ qudit e` sending each basis state `|x⟩ ⊗ |y⟩` to
`|(σ (x, y)).1⟩ ⊗ |(σ (x, y)).2⟩`. Every permutation of the basis is realised by such a unitary
(permuting an orthonormal basis is an isometry), so this is the general "permute the computational
basis" gate — the operator a reversible classical circuit on the two registers implements.

## What is formalised

* `quditPairBasis d e` — the computational **product** orthonormal basis of
  `(qudit d ⊗ qudit e).space`, indexed by `Fin d × Fin e`: `Mathlib`'s
  `OrthonormalBasis.tensorProduct` of the two standard bases.
  `quditPairBasis d e (x, y) = |x⟩ ⊗ |y⟩` (`quditPairBasis_apply`).
* `quditPairPerm σ` — the **basis-permutation gate**: `Evolution.ofLinearIsometryEquiv` of the
  linear isometry equivalence permuting `quditPairBasis` by `σ` (`OrthonormalBasis.equiv`). It is a
  genuine `Evolution` (Postulate 5): unitarity is inherited from the isometry, so producing this
  term *is* the fact that permuting the basis is a legitimate quantum operation.
* `quditPairPerm_op_tmul` / `quditPairPerm_evolvePure_quditBasis` — the **defining action**
  `quditPairPerm σ (|x⟩ ⊗ |y⟩) = |(σ (x,y)).1⟩ ⊗ |(σ (x,y)).2⟩`, at the operator and pure-state
  levels: the gate realises exactly the permutation `σ` on the computational basis.

## Design notes

* **Construction.** Mirrors `Evolution.swap` (the special case where `σ` exchanges the factors): a
  basis-permutation gate is `Evolution.ofLinearIsometryEquiv` of an `OrthonormalBasis.equiv`, whose
  action on a basis vector is `equiv_apply_basis`. The two `EuclideanSpace.basisFun` standard bases
  tensor to `quditPairBasis`; `quditPairBasis (x, y) = |x⟩ ⊗ |y⟩` because
  `basisFun i = EuclideanSpace.single i 1 = (quditBasis i).vec`.
* **Typing of `quditPairBasis`.** `quditPairBasis` is typed at the composite space
  `(qudit d ⊗ qudit e).space` (defeq to the raw `EuclideanSpace ⊗ EuclideanSpace`) so that
  `equiv_apply_basis` matches the operator produced by `ofLinearIsometryEquiv`; the raw
  `tensorProduct_apply'` is bridged across the defeq by a term-level `have`, and the residual
  raw-vs-composite `⊗ₜ` is closed by a full-transparency `rfl`.
* **Unitarity.** A value of type `Evolution (qudit d ⊗ qudit e)` cannot be formed without
  discharging unitarity; here it comes from the isometry `OrthonormalBasis.equiv`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {d e : ℕ}

/-- The **computational product basis** of `(qudit d ⊗ qudit e).space`, indexed by
`Fin d × Fin e`: the `Mathlib` tensor product `OrthonormalBasis.tensorProduct` of the two standard
bases `EuclideanSpace.basisFun`. Its basis vector at `(x, y)` is the product computational-basis
state `|x⟩ ⊗ |y⟩` (`quditPairBasis_apply`). -/
def quditPairBasis (d e : ℕ) :
    OrthonormalBasis (Fin d × Fin e) ℂ (qudit d ⊗ qudit e).space :=
  (EuclideanSpace.basisFun (Fin d) ℂ).tensorProduct (EuclideanSpace.basisFun (Fin e) ℂ)

/-- The product-basis vector at a packed index `p` is `|p.1⟩ ⊗ |p.2⟩`. -/
theorem quditPairBasis_apply' (d e : ℕ) (p : Fin d × Fin e) :
    quditPairBasis d e p = (quditBasis p.1).vec ⊗ₜ[ℂ] (quditBasis p.2).vec := by
  have key : quditPairBasis d e p
      = (EuclideanSpace.basisFun (Fin d) ℂ) p.1 ⊗ₜ[ℂ] (EuclideanSpace.basisFun (Fin e) ℂ) p.2 :=
    OrthonormalBasis.tensorProduct_apply' _ _ p
  rw [key]
  simp only [EuclideanSpace.basisFun_apply, quditBasis_vec]
  rfl

/-- The product-basis vector at `(x, y)` is the product computational-basis state `|x⟩ ⊗ |y⟩`. -/
theorem quditPairBasis_apply (d e : ℕ) (x : Fin d) (y : Fin e) :
    quditPairBasis d e (x, y) = (quditBasis x).vec ⊗ₜ[ℂ] (quditBasis y).vec :=
  quditPairBasis_apply' d e (x, y)

/-- **The computational-basis permutation gate** `quditPairPerm σ` on `qudit d ⊗ qudit e`: the
unitary `Evolution` that permutes the joint computational basis by `σ : Equiv.Perm (Fin d × Fin e)`,
`|x⟩ ⊗ |y⟩ ↦ |(σ (x,y)).1⟩ ⊗ |(σ (x,y)).2⟩`. It is `Evolution.ofLinearIsometryEquiv` of the
isometry `OrthonormalBasis.equiv` permuting `quditPairBasis` by `σ`, with unitarity inherited from
that isometry. -/
def quditPairPerm (σ : Equiv.Perm (Fin d × Fin e)) : Evolution (qudit d ⊗ qudit e) :=
  Evolution.ofLinearIsometryEquiv ((quditPairBasis d e).equiv (quditPairBasis d e) σ)

/-- **Action of the basis-permutation gate** on a product vector:
`quditPairPerm σ (|x⟩ ⊗ |y⟩) = |(σ (x,y)).1⟩ ⊗ |(σ (x,y)).2⟩`. -/
theorem quditPairPerm_op_tmul (σ : Equiv.Perm (Fin d × Fin e)) (x : Fin d) (y : Fin e) :
    (quditPairPerm σ).op ((quditBasis x).vec ⊗ₜ[ℂ] (quditBasis y).vec)
      = (quditBasis (σ (x, y)).1).vec ⊗ₜ[ℂ] (quditBasis (σ (x, y)).2).vec := by
  -- The argument `(quditBasis x).vec ⊗ₜ (quditBasis y).vec` is itself typed at the generic
  -- `(qudit d).space ⊗[ℂ] (qudit e).space`, so `rw`'s pattern for
  -- `Evolution.ofLinearIsometryEquiv_op_apply` (needing a syntactically bundled argument) cannot
  -- fire on it; instantiate the lemma directly (an ordinary application, checked up to full defeq).
  have hop_apply := Evolution.ofLinearIsometryEquiv_op_apply
    ((quditPairBasis d e).equiv (quditPairBasis d e) σ)
    ((quditBasis x).vec ⊗ₜ[ℂ] (quditBasis y).vec)
  rw [quditPairPerm, hop_apply, ← quditPairBasis_apply,
    OrthonormalBasis.equiv_apply_basis, quditPairBasis_apply']

/-- **Action of the basis-permutation gate on a product pure state:**
`quditPairPerm σ (|x⟩ ⊗ |y⟩) = |(σ (x,y)).1⟩ ⊗ |(σ (x,y)).2⟩`. The `evolvePure`-level companion of
`quditPairPerm_op_tmul`: the gate realises the permutation `σ` on the computational basis. -/
theorem quditPairPerm_evolvePure_quditBasis (σ : Equiv.Perm (Fin d × Fin e))
    (x : Fin d) (y : Fin e) :
    (quditPairPerm σ).evolvePure ((quditBasis x) ⊗ (quditBasis y))
      = (quditBasis (σ (x, y)).1) ⊗ (quditBasis (σ (x, y)).2) := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, PureState.tmul_vec, PureState.tmul_vec, quditPairPerm_op_tmul]

end AxQM
