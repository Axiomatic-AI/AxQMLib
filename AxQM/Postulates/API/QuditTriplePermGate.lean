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
# AxQM.Postulates.API — the three-register computational-basis permutation gate

The *classical reversible circuit* on a triple of qudit registers: given a
permutation `σ` of the joint computational-basis labels `Fin d × Fin e × Fin f`, the gate
`quditTriplePerm σ` is the unitary `Evolution` of `qudit d ⊗ qudit e ⊗ qudit f` sending each basis
state `|x⟩ ⊗ |y⟩ ⊗ |z⟩` to `|(σ (x,y,z)).1⟩ ⊗ |(σ (x,y,z)).2.1⟩ ⊗ |(σ (x,y,z)).2.2⟩`. Every
permutation of the basis is realised by such a unitary (permuting an orthonormal basis is an
isometry), so this is the general "permute the computational basis" gate on three registers — the
operator a reversible classical circuit on the three registers implements. It is the three-register
companion of `quditPairPerm` (`Postulates/API/QuditPairPermGate.lean`), and is what the
discrete-logarithm black box of Nielsen & Chuang Exercise 5.25 (`NC/Ch5/Exercise5_25.lean`) is built
from.

## What is formalised

* `quditTripleBasis d e f` — the computational **product** orthonormal basis of
  `(qudit d ⊗ qudit e ⊗ qudit f).space`, indexed by `Fin d × Fin e × Fin f`: the iterated
  `Mathlib` `OrthonormalBasis.tensorProduct` of the three standard bases.
  `quditTripleBasis d e f (x, y, z) = |x⟩ ⊗ |y⟩ ⊗ |z⟩` (`quditTripleBasis_apply`).
* `quditTriplePerm σ` — the **basis-permutation gate**: `Evolution.ofLinearIsometryEquiv` of the
  linear isometry equivalence permuting `quditTripleBasis` by `σ` (`OrthonormalBasis.equiv`). It is
  a genuine `Evolution` (Postulate 5): unitarity is inherited from the isometry, so producing this
  term *is* the fact that permuting the basis is a legitimate quantum operation.
* `quditTriplePerm_op_tmul` / `quditTriplePerm_evolvePure_quditBasis` — the **defining action**
  `quditTriplePerm σ (|x⟩ ⊗ |y⟩ ⊗ |z⟩) = |(σ (x,y,z)).1⟩ ⊗ |(σ (x,y,z)).2.1⟩ ⊗ |(σ (x,y,z)).2.2⟩`,
  at the operator (`.vec`) and pure-state (`evolvePure`) levels: the gate realises exactly the
  permutation `σ` on the computational basis.

## Design notes

* **Construction.** Mirrors `quditPairPerm`: a basis-permutation gate is
  `Evolution.ofLinearIsometryEquiv` of an `OrthonormalBasis.equiv`, whose action on a basis vector
  is `OrthonormalBasis.equiv_apply_basis`. The three `EuclideanSpace.basisFun` standard bases tensor
  (right-associatedly, matching the right-associativity of `⊗`) to `quditTripleBasis`, whose value
  at `(x, y, z)` is `|x⟩ ⊗ |y⟩ ⊗ |z⟩` (`quditTripleBasis_apply`) because
  `basisFun i = EuclideanSpace.single i 1 = (quditBasis i).vec`.
* **Typing.** As for the pair gate, the raw iterated `⊗ₜ` of the standard bases and
  the composite `PureState.tmul`'s `.vec` agree only up to the raw-vs-composite instance defeq; the
  basis-apply lemma bridges them with a full-transparency `rfl` after unfolding both to
  `EuclideanSpace.single`. The action lemmas are therefore stated over `PureState.tmul`'s `.vec`
  (the composite-space head).
* **Unitarity.** A value of type `Evolution (qudit d ⊗ qudit e ⊗ qudit f)` cannot be formed
  without discharging unitarity; here it comes from the isometry `OrthonormalBasis.equiv`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {d e f : ℕ}

/-- The **computational product basis** of `(qudit d ⊗ qudit e ⊗ qudit f).space`, indexed by
`Fin d × Fin e × Fin f`: the iterated `Mathlib` tensor product `OrthonormalBasis.tensorProduct` of
the three standard bases `EuclideanSpace.basisFun`, right-associated to match the
right-associativity of `⊗`. Its basis vector at `(x, y, z)` is the product computational-basis state
`|x⟩ ⊗ |y⟩ ⊗ |z⟩` (`quditTripleBasis_apply`). -/
def quditTripleBasis (d e f : ℕ) :
    OrthonormalBasis (Fin d × Fin e × Fin f) ℂ (qudit d ⊗ qudit e ⊗ qudit f).space :=
  (EuclideanSpace.basisFun (Fin d) ℂ).tensorProduct
    ((EuclideanSpace.basisFun (Fin e) ℂ).tensorProduct (EuclideanSpace.basisFun (Fin f) ℂ))

/-- The triple product-basis vector at a packed index `p` is `|p.1⟩ ⊗ |p.2.1⟩ ⊗ |p.2.2⟩` (as the
`.vec` of the composite `PureState.tmul`). Two applications of
`OrthonormalBasis.tensorProduct_apply'` expand the iterated tensor to `basisFun`s, which are the
computational-basis vectors; the residual raw-vs-composite `⊗ₜ` is closed by a full-transparency
`rfl`. -/
theorem quditTripleBasis_apply' (d e f : ℕ) (p : Fin d × Fin e × Fin f) :
    quditTripleBasis d e f p
      = ((quditBasis p.1) ⊗ (quditBasis p.2.1) ⊗ (quditBasis p.2.2)).vec := by
  have key : quditTripleBasis d e f p
      = (EuclideanSpace.basisFun (Fin d) ℂ) p.1 ⊗ₜ[ℂ]
          ((EuclideanSpace.basisFun (Fin e) ℂ).tensorProduct
            (EuclideanSpace.basisFun (Fin f) ℂ)) p.2 :=
    OrthonormalBasis.tensorProduct_apply' _ _ p
  have key2 :
      ((EuclideanSpace.basisFun (Fin e) ℂ).tensorProduct (EuclideanSpace.basisFun (Fin f) ℂ)) p.2
        = (EuclideanSpace.basisFun (Fin e) ℂ) p.2.1
            ⊗ₜ[ℂ] (EuclideanSpace.basisFun (Fin f) ℂ) p.2.2 :=
    OrthonormalBasis.tensorProduct_apply' _ _ p.2
  rw [key, key2, PureState.tmul_vec, PureState.tmul_vec]
  simp only [EuclideanSpace.basisFun_apply, quditBasis_vec]
  rfl

/-- The triple product-basis vector at `(x, y, z)` is the product computational-basis state
`|x⟩ ⊗ |y⟩ ⊗ |z⟩`. The unpacked form of `quditTripleBasis_apply'`, convenient for reverse-rewriting
a `|x⟩ ⊗ |y⟩ ⊗ |z⟩` back to a basis vector. -/
theorem quditTripleBasis_apply (d e f : ℕ) (x : Fin d) (y : Fin e) (z : Fin f) :
    quditTripleBasis d e f (x, y, z)
      = ((quditBasis x) ⊗ (quditBasis y) ⊗ (quditBasis z)).vec :=
  quditTripleBasis_apply' d e f (x, y, z)

/-- **The three-register computational-basis permutation gate** `quditTriplePerm σ` on
`qudit d ⊗ qudit e ⊗ qudit f`: the unitary `Evolution` that permutes the joint computational basis
by `σ : Equiv.Perm (Fin d × Fin e × Fin f)`,
`|x⟩ ⊗ |y⟩ ⊗ |z⟩ ↦ |(σ (x,y,z)).1⟩ ⊗ |(σ (x,y,z)).2.1⟩ ⊗ |(σ (x,y,z)).2.2⟩`. It is
`Evolution.ofLinearIsometryEquiv` of the isometry `OrthonormalBasis.equiv` permuting
`quditTripleBasis` by `σ`, with unitarity inherited from that isometry. The three-register companion
of `quditPairPerm`. -/
def quditTriplePerm (σ : Equiv.Perm (Fin d × Fin e × Fin f)) :
    Evolution (qudit d ⊗ qudit e ⊗ qudit f) :=
  Evolution.ofLinearIsometryEquiv ((quditTripleBasis d e f).equiv (quditTripleBasis d e f) σ)

/-- **Action of the triple basis-permutation gate** on a product state (operator/`.vec` level):
`quditTriplePerm σ (|x⟩ ⊗ |y⟩ ⊗ |z⟩) = |(σ (x,y,z)).1⟩ ⊗ |(σ (x,y,z)).2.1⟩ ⊗ |(σ (x,y,z)).2.2⟩`. -/
theorem quditTriplePerm_op_tmul (σ : Equiv.Perm (Fin d × Fin e × Fin f))
    (x : Fin d) (y : Fin e) (z : Fin f) :
    (quditTriplePerm σ).op ((quditBasis x ⊗ quditBasis y ⊗ quditBasis z).vec)
      = (quditBasis (σ (x, y, z)).1 ⊗ quditBasis (σ (x, y, z)).2.1
          ⊗ quditBasis (σ (x, y, z)).2.2).vec := by
  rw [quditTriplePerm, Evolution.ofLinearIsometryEquiv_op_apply, ← quditTripleBasis_apply,
    OrthonormalBasis.equiv_apply_basis, quditTripleBasis_apply']

/-- **Action of the triple basis-permutation gate on a product pure state:**
`quditTriplePerm σ (|x⟩ ⊗ |y⟩ ⊗ |z⟩) = |(σ (x,y,z)).1⟩ ⊗ |(σ (x,y,z)).2.1⟩ ⊗ |(σ (x,y,z)).2.2⟩`.
The `evolvePure`-level companion of `quditTriplePerm_op_tmul`: the gate realises the permutation `σ`
on the computational basis. -/
theorem quditTriplePerm_evolvePure_quditBasis (σ : Equiv.Perm (Fin d × Fin e × Fin f))
    (x : Fin d) (y : Fin e) (z : Fin f) :
    (quditTriplePerm σ).evolvePure ((quditBasis x) ⊗ (quditBasis y) ⊗ (quditBasis z))
      = (quditBasis (σ (x, y, z)).1) ⊗ (quditBasis (σ (x, y, z)).2.1)
          ⊗ (quditBasis (σ (x, y, z)).2.2) := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, quditTriplePerm_op_tmul]

end AxQM
