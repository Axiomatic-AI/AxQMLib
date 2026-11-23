/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Associator
import AxQM.Postulates.Composite

/-!
# AxQM.Postulates.API — the swap system isomorphism and `.toIsometry` unfolding lemmas

The swap isomorphism and unfolding lemmas for system isomorphisms (`QSystem.Iso`), alongside
`QSystem.Iso.refl/symm/trans/tmul` and `QSystem.assoc` (all defined in `Associator.lean` and
`SystemIso.lean`):

* `QSystem.Iso.comm` — the **swap** `S ⊗ T ≃ₛ T ⊗ S`, exchanging the two factors of a bipartite
  composite (the `QSystem.Iso` packaging of `TensorProduct.commIsometry`).  The SWAP on an
  *identical-system* composite is also available as an `Evolution` (`Evolution.swap`); this is the
  general two-system version, as a `QSystem.Iso`.
* the `.toIsometry`-unfolding lemma family for the combinators
  (`refl`/`trans`/`symm`/`tmul`/`comm`), completing `QSystem.assoc_toIsometry`.

## Use in Problem 4.6

`QSystem.Iso.comm` is needed for the Nielsen & Chuang **Problem 4.6**
gate-teleportation identity ("Universality with prior entanglement").  Gate teleportation of a
`CNOT` teleports the two input qubits `q_A, q_B` through the four-qubit resource state, whose two
input halves are `a_in` (of the first Bell pair) and `b_in` (of the second).  The two Bell-basis
measurements pair `(q_A, a_in)` and `(q_B, b_in)` — but in the natural register
`(q_A ⊗ q_B) ⊗ ((a_in ⊗ a_out) ⊗ (b_in ⊗ b_out))` these partners are *not* adjacent, so bringing
each input qubit beside its Bell-pair partner (the **two independent single-qubit teleportation
setups** `q_A ⊗ |Φ⁺⟩` and `q_B ⊗ |Φ⁺⟩`, on each of which `teleportation_identity` applies) needs a
swap/braid, which `QSystem.assoc` and `QSystem.Iso.tmul` alone cannot provide.  The interchange
reshape `(A ⊗ B) ⊗ (C ⊗ D) ≃ₛ (A ⊗ C) ⊗ (B ⊗ D)` assembled from `assoc`/`tmul`/`comm`
(`AxQM/Postulates/API/Interchange.lean`), and the gate teleportation identity built on it
(`AxQM/Postulates/API/GateTeleportationIdentity.lean`), use `comm` and the `.toIsometry` unfolding
lemmas of this file.

## What is formalised

* `QSystem.Iso.comm` / `QSystem.Iso.comm_toIsometry` / `QSystem.Iso.comm_toIsometry_tmul` — the
  swap iso, its isometry (`commIsometry`), and its pure-tensor action `(x ⊗ y) ↦ (y ⊗ x)`.
* `QSystem.Iso.refl_toIsometry`, `trans_toIsometry`, `symm_toIsometry`, `tmul_toIsometry` — the
  `.toIsometry` of each backbone combinator, unfolded to its underlying isometry (all
  definitional).  With `QSystem.assoc_toIsometry` and `comm_toIsometry`, these reduce any composite
  `QSystem.Iso` to a raw `LinearIsometryEquiv` expression.
* `assoc_symm_toIsometry_tmul_tmul` — the inverse associator on a pure tensor
  `(assoc A B C).symm ((a ⊗ b) ⊗ c) = a ⊗ (b ⊗ c)`, the `.symm` companion of the existing
  `assoc_toIsometry_tmul_tmul`.
* `PureState.congr_symm_congr` / `PureState.congr_congr_symm` — the **state-level roundtrip
  cancellations** for the `PureState.congr` transport bridge: carrying a pure state along `e` and
  back along `e.symm` (or vice versa) is the identity. The canonical roundtrip lemmas of the
  `PureState.congr` API (`SystemIso.lean` exposes only `congr_vec` / `congr_toState`), the
  state-level companions of `QSystem.Iso.symm_toIsometry`.

## Design notes

* **Generality.**  `comm` is stated over two arbitrary systems `S T`; the `≃ₛ` carries
  norm-preservation for free (it is a genuine `QSystem.Iso`), so transporting a state through it
  needs no separate normalisation proof.
* **`.toIsometry` unfolding, not applied rewrites.**  The applied form `(tmul e f).toIsometry x` is
  not matched by `rw`/`simp` (the structure-projection + `≃ₗᵢ` `FunLike` coercion defeats the
  discrimination tree) and forces `whnf` blow-up under `erw`.  The unfolding lemmas here reduce at
  the *function* level (`(tmul e f).toIsometry = congrIsometry …`), after which the well-behaved
  Mathlib `TensorProduct.*Isometry` lemmas apply; this is the robust idiom for computing the action
  of a composite iso (used by the interchange reshape in `AxQM/Postulates/API/Interchange.lean`).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### Definitional `QSystem.Iso` action lemmas

The `.toIsometry` of each transport-backbone combinator, unfolded to its underlying
isometry.  All hold by `rfl`; they let a composite `QSystem.Iso` be reduced to a raw
`LinearIsometryEquiv` expression, whose action on pure tensors is then computed by the
well-behaved `TensorProduct.*Isometry` simp lemmas.  (Rewriting the *applied* form
`(tmul e f).toIsometry (x ⊗ₜ y)` directly is unreliable — the structure-projection coercion is
not matched by `rw`/`simp` and forces `whnf` blow-up under `erw` — so we reduce at the function
level first.) -/

/-- `.toIsometry` of the identity iso is the identity isometry. -/
theorem QSystem.Iso.refl_toIsometry (S : QSystem) :
    (QSystem.Iso.refl S).toIsometry = LinearIsometryEquiv.refl ℂ S.space :=
  rfl

/-- `.toIsometry` of a composite iso is the composite of the two isometries. -/
theorem QSystem.Iso.trans_toIsometry {S T U : QSystem} (e : S ≃ₛ T) (f : T ≃ₛ U) :
    (e.trans f).toIsometry = e.toIsometry.trans f.toIsometry :=
  rfl

/-- `.toIsometry` of an inverse iso is the inverse isometry. -/
theorem QSystem.Iso.symm_toIsometry {S T : QSystem} (e : S ≃ₛ T) :
    e.symm.toIsometry = e.toIsometry.symm :=
  rfl

/-- **Double inverse of a system isomorphism is the identity:** `e.symm.symm = e`, from the
underlying `LinearIsometryEquiv.symm_symm`. -/
theorem QSystem.Iso.symm_symm {S T : QSystem} (e : S ≃ₛ T) : e.symm.symm = e := by
  simp only [QSystem.Iso.symm, LinearIsometryEquiv.symm_symm]

/-- `.toIsometry` of a tensor iso is `TensorProduct.congrIsometry` of the factor isometries. -/
theorem QSystem.Iso.tmul_toIsometry {S S' T T' : QSystem} (e : S ≃ₛ S') (f : T ≃ₛ T') :
    (QSystem.Iso.tmul e f).toIsometry = TensorProduct.congrIsometry e.toIsometry f.toIsometry :=
  rfl

/-- The **inverse associator on a pure tensor**: `(assoc A B C).symm ((a ⊗ b) ⊗ c) = a ⊗ (b ⊗ c)`.
The `.symm` companion of `assoc_toIsometry_tmul_tmul`, obtained by inverting it through
injectivity of the associator isometry. -/
theorem assoc_symm_toIsometry_tmul_tmul {A B C : QSystem} (a : A.space) (b : B.space)
    (c : C.space) :
    (QSystem.assoc A B C).symm.toIsometry ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) = a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c) := by
  change (QSystem.assoc A B C).toIsometry.symm ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) = a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c)
  apply (QSystem.assoc A B C).toIsometry.injective
  -- `(A ⊗ B ⊗ C).space` vs the plain tensor `A.space ⊗[ℂ] B.space ⊗[ℂ] C.space` diverge under
  -- `rw`'s syntactic matching even though defeq; `erw` bridges it.
  erw [LinearIsometryEquiv.apply_symm_apply]

/-! ### The swap (commutation) system isomorphism -/

/-- The **swap** system isomorphism `S ⊗ T ≃ₛ T ⊗ S`: the two orderings of a bipartite composite
are the same quantum system, with the factors exchanged.  The isometry is
`TensorProduct.commIsometry ℂ S.space T.space`.  The `⊗`-commutativity of the transport backbone,
a sibling of `QSystem.assoc` and `QSystem.Iso.tmul`. -/
def QSystem.Iso.comm (S T : QSystem) : (S ⊗ T) ≃ₛ (T ⊗ S) :=
  ⟨TensorProduct.commIsometry ℂ S.space T.space⟩

/-- `.toIsometry` of the swap iso is `TensorProduct.commIsometry`. -/
theorem QSystem.Iso.comm_toIsometry (S T : QSystem) :
    (QSystem.Iso.comm S T).toIsometry = TensorProduct.commIsometry ℂ S.space T.space :=
  rfl

/-- The action of `QSystem.Iso.comm` on a pure tensor: `comm (x ⊗ y) = y ⊗ x`. -/
@[simp]
theorem QSystem.Iso.comm_toIsometry_tmul (S T : QSystem) (x : S.space) (y : T.space) :
    (QSystem.Iso.comm S T).toIsometry (x ⊗ₜ[ℂ] y) = y ⊗ₜ[ℂ] x := by
  rw [QSystem.Iso.comm_toIsometry]
  erw [TensorProduct.commIsometry_apply]
  rw [TensorProduct.comm_tmul]

/-- **Swap naturality.** Reshaping the two factors and then swapping them is the same as swapping
first and then reshaping the (now exchanged) factors:

`(g ⊗ h).trans (comm S' T') = (comm S T).trans (h ⊗ g)`

for `g : S ≃ₛ S'`, `h : T ≃ₛ T'`. The commutation of the swap `QSystem.Iso.comm` with the tensor of
two reshapings, both sides acting as `x ⊗ y ↦ h y ⊗ g x`. A backbone naturality square, sibling of
`QSystem.Iso.comm_toIsometry_tmul`; the plumbing that lets a `reducedRight` naturality fact (which
traces out the *left* factor) be read off from the `reducedLeft` API through the swap bridge
`State.reducedRight_congr_comm` (see `State.reducedRight_congr_tmul_refl`). Both the `left`-factor
(`h := refl`) and `right`-factor (`g := refl`) specializations are instances. -/
theorem QSystem.Iso.tmul_trans_comm {S S' T T' : QSystem} (g : S ≃ₛ S') (h : T ≃ₛ T') :
    (QSystem.Iso.tmul g h).trans (QSystem.Iso.comm S' T')
      = (QSystem.Iso.comm S T).trans (QSystem.Iso.tmul h g) := by
  apply congrArg QSystem.Iso.mk
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  intro x y
  rfl

/-! ### The left-commutation reshape `A ⊗ (B ⊗ C) ≃ₛ B ⊗ (A ⊗ C)` -/

/-- The **left-commutation** system isomorphism `A ⊗ (B ⊗ C) ≃ₛ B ⊗ (A ⊗ C)` — the
transport-backbone counterpart of `TensorProduct.leftComm`. It re-associates to `(A ⊗ B) ⊗ C`, swaps
the front pair to `(B ⊗ A) ⊗ C`, then de-associates to `B ⊗ (A ⊗ C)`, bringing the *middle* factor
`B` to the front while leaving `C` last. Two consumers: it carries a gate acting on the *right*
factor of a data register past a spectator register `A` on the left (the inner isomorphism of the
register-lift `measureObservableCircuit_onRight`), and it is the "shared-`A`" reshape whose
marginals drive the weak-monotonicity bound of Nielsen & Chuang Exercise 11.26
(`State.vonNeumannMutualInfo_add_le_two_mul_vonNeumannEntropy`). A backbone sibling of
`QSystem.assoc` / `QSystem.Iso.comm` / `QSystem.Iso.tmul`. -/
def QSystem.Iso.leftComm (A B C : QSystem) : (A ⊗ (B ⊗ C)) ≃ₛ (B ⊗ (A ⊗ C)) :=
  ((QSystem.assoc A B C).trans ((QSystem.Iso.comm A B).tmul (QSystem.Iso.refl C))).trans
    (QSystem.assoc B A C).symm

/-- The action of `QSystem.Iso.leftComm` on a pure tensor: `a ⊗ (b ⊗ c) ↦ b ⊗ (a ⊗ c)`, bringing
the middle factor to the front. Computed by reducing the composite iso at the function level
(`trans_toIsometry`) and threading the pure-tensor action lemmas for `assoc`, `comm`, and the
tensor of isos through the three stages. -/
@[simp]
theorem QSystem.Iso.leftComm_toIsometry_tmul (A B C : QSystem) (a : A.space) (b : B.space)
    (c : C.space) :
    (QSystem.Iso.leftComm A B C).toIsometry (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c)) = b ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] c) :=
  rfl

/-- The action of the inverse `leftComm` on a pure tensor: `b ⊗ (a ⊗ c) ↦ a ⊗ (b ⊗ c)`. The `.symm`
companion of `leftComm_toIsometry_tmul`, obtained by inverting it through injectivity of the
`leftComm` isometry. -/
@[simp]
theorem QSystem.Iso.leftComm_symm_toIsometry_tmul (A B C : QSystem) (a : A.space) (b : B.space)
    (c : C.space) :
    (QSystem.Iso.leftComm A B C).symm.toIsometry (b ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] c)) = a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c) :=
  rfl

/-- Reshape-frame identity for the `B ⊗ A` marginal: post-composing `leftComm` with the `assoc` back
to `(B ⊗ A) ⊗ C` is the same as re-associating and swapping the front pair `A ↔ B` in place. Both
send `a ⊗ (b ⊗ c) ↦ (b ⊗ a) ⊗ c`; proved by extensionality on pure tensors. -/
theorem QSystem.Iso.leftComm_trans_assoc {A B C : QSystem} :
    (QSystem.Iso.leftComm A B C).trans (QSystem.assoc B A C)
      = (QSystem.assoc A B C).trans ((QSystem.Iso.comm A B).tmul (QSystem.Iso.refl C)) := by
  apply congrArg QSystem.Iso.mk
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  refine TensorProduct.ext_threefold' fun a b c => ?_
  simp only [QSystem.Iso.leftComm]
  rfl

/-- Reshape-frame identity for the `A ⊗ C` marginal: post-composing `leftComm` with the front `comm`
`B ⊗ (A ⊗ C) ≃ₛ (A ⊗ C) ⊗ B` is the same as swapping the inner pair `B ↔ C` and re-associating to
`(A ⊗ C) ⊗ B`. Both send `a ⊗ (b ⊗ c) ↦ (a ⊗ c) ⊗ b`; proved by extensionality on pure tensors. -/
theorem QSystem.Iso.leftComm_trans_comm {A B C : QSystem} :
    (QSystem.Iso.leftComm A B C).trans (QSystem.Iso.comm B (A ⊗ C))
      = (QSystem.Iso.tmul (QSystem.Iso.refl A) (QSystem.Iso.comm B C)).trans
          (QSystem.assoc A C B) := by
  apply congrArg QSystem.Iso.mk
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  refine TensorProduct.ext_threefold' fun a b c => ?_
  simp only [QSystem.Iso.leftComm]
  rfl

/-- Reshape-frame identity: de-associating `A ⊗ (B ⊗ C)` and undoing the `leftComm B A C` swap
equals swapping the front pair `A ↔ B` (`comm A B ⊗ refl C`) then de-associating `(B ⊗ A) ⊗ C`. Both
send `(a ⊗ b) ⊗ c ↦ b ⊗ (a ⊗ c)`; proved by extensionality on triple tensors. The `symm` companion
of `QSystem.Iso.leftComm_trans_assoc`, used to collapse the composite of two single-system dilations
into one joint dilation (`State.dilatedChannelComp_eq_dilatedChannel`). -/
theorem QSystem.Iso.assoc_symm_trans_leftComm_symm {A B C : QSystem} :
    (A.assoc B C).symm.trans (QSystem.Iso.leftComm B A C).symm
      = ((QSystem.Iso.comm A B).tmul (QSystem.Iso.refl C)).trans (B.assoc A C).symm := by
  apply congrArg QSystem.Iso.mk
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  refine TensorProduct.ext_threefold fun a b c => ?_
  simp only [QSystem.Iso.leftComm]
  rfl

/-! ### `PureState.congr` roundtrip cancellation

Transporting a pure state through a system isomorphism and back is the identity — the state-level
companions of `QSystem.Iso.symm_toIsometry`, proved by pushing to the underlying vector
(`PureState.congr_vec`) and cancelling the isometry with `LinearIsometryEquiv.symm_apply_apply` /
`apply_symm_apply`.  These are the roundtrip lemmas the `PureState.congr` bridge lacks
(`SystemIso.lean` exposes only `congr_vec` / `congr_toState`), reusable by any transport proof. -/

/-- **`PureState.congr` roundtrip (forward then back).** Transporting a pure state along `e` and
then back along `e.symm` recovers it: `PureState.congr e.symm (PureState.congr e ψ) = ψ`. -/
theorem PureState.congr_symm_congr {S T : QSystem} (e : S ≃ₛ T) (ψ : PureState S) :
    PureState.congr e.symm (PureState.congr e ψ) = ψ := by
  apply PureState.ext
  rw [PureState.congr_vec, PureState.congr_vec, QSystem.Iso.symm_toIsometry,
    LinearIsometryEquiv.symm_apply_apply]

/-- **`PureState.congr` roundtrip (back then forward).** Transporting a pure state along `e.symm`
and then forward along `e` recovers it: `PureState.congr e (PureState.congr e.symm ψ) = ψ`. -/
theorem PureState.congr_congr_symm {S T : QSystem} (e : S ≃ₛ T) (ψ : PureState T) :
    PureState.congr e (PureState.congr e.symm ψ) = ψ := by
  apply PureState.ext
  rw [PureState.congr_vec, PureState.congr_vec, QSystem.Iso.symm_toIsometry,
    LinearIsometryEquiv.apply_symm_apply]

/-- **`PureState.congr` is its own inner-product adjoint.** Transporting the *second* argument of an
inner product back along `e.symm` equals transporting the *first* forward along `e`:
`⟨x, PureState.congr e.symm y⟩ = ⟨PureState.congr e x, y⟩`. This is the unitary-adjoint identity
`⟨x, U† y⟩ = ⟨U x, y⟩` for the transport `U = PureState.congr e`, since `e.toIsometry` preserves
inner products (`LinearIsometryEquiv.inner_map_map`) and `congr e.symm` is `e.toIsometry.symm`
(`QSystem.Iso.symm_toIsometry`). The bridge any proof comparing amplitudes across a transported
register needs (e.g. matching a state against a transported computational basis). -/
theorem PureState.inner_congr_symm {S T : QSystem} (e : S ≃ₛ T)
    (x : PureState S) (y : PureState T) :
    inner ℂ x.vec (PureState.congr e.symm y).vec
      = inner ℂ (PureState.congr e x).vec y.vec := by
  rw [PureState.congr_vec, PureState.congr_vec, QSystem.Iso.symm_toIsometry,
    ← LinearIsometryEquiv.inner_map_map e.toIsometry x.vec (e.toIsometry.symm y.vec),
    LinearIsometryEquiv.apply_symm_apply]

/-! ### `Evolution.congr` roundtrip cancellation

The gate-level companions of the `PureState.congr` roundtrips above: transporting a gate through a
system isomorphism and back is the identity. Both reduce, via `Evolution.ext` /
`Evolution.congr_op`, to the operator `conjStarAlgEquiv` roundtrip, where `symm_conjStarAlgEquiv`
(`e.conjStarAlgEquiv.symm = e.symm.conjStarAlgEquiv`) turns the two conjugations into a
`StarAlgEquiv` inverse pair. These are the transport-back lemmas any *gate* placement proof needs
(the `Postulates` `Evolution.congr` API exposes only `congr_op`) — e.g. carrying a circuit computed
on a flattened register back onto the register it was placed on. -/

/-- **`Evolution.congr` roundtrip (forward then back).** Transporting a gate along `e` and then back
along `e.symm` recovers it: `Evolution.congr e.symm (Evolution.congr e U) = U`. -/
theorem Evolution.congr_symm_congr {S T : QSystem} (e : S ≃ₛ T) (U : Evolution S) :
    Evolution.congr e.symm (Evolution.congr e U) = U := by
  apply Evolution.ext
  rw [Evolution.congr_op, Evolution.congr_op, QSystem.Iso.symm_toIsometry,
    ← LinearIsometryEquiv.symm_conjStarAlgEquiv, StarAlgEquiv.symm_apply_apply]

/-- **`Evolution.congr` roundtrip (back then forward).** Transporting a gate along `e.symm` and then
forward along `e` recovers it: `Evolution.congr e (Evolution.congr e.symm U) = U`. -/
theorem Evolution.congr_congr_symm {S T : QSystem} (e : S ≃ₛ T) (U : Evolution T) :
    Evolution.congr e (Evolution.congr e.symm U) = U := by
  apply Evolution.ext
  rw [Evolution.congr_op, Evolution.congr_op, QSystem.Iso.symm_toIsometry,
    ← LinearIsometryEquiv.symm_conjStarAlgEquiv, StarAlgEquiv.apply_symm_apply]

/-- **`Evolution.congr` is a composition homomorphism.** Transporting a composite gate along a
system isomorphism transports the factors: `Evolution.congr e (a · b) = Evolution.congr e a ·
Evolution.congr e b`. Since `Evolution.congr` conjugates the operator by the unital ⋆-algebra
equivalence `e.toIsometry.conjStarAlgEquiv`, this is `map_mul` for that equivalence — the
multiplicative sibling of the `congr` roundtrip lemmas above. A gate placement / reassociation proof
that pushes a transport through a composite circuit needs this. -/
theorem Evolution.congr_comp {S T : QSystem} (e : S ≃ₛ T) (a b : Evolution S) :
    Evolution.congr e (a.comp b) = (Evolution.congr e a).comp (Evolution.congr e b) := by
  ext1
  rw [Evolution.congr_op, Evolution.comp_op, Evolution.comp_op, Evolution.congr_op,
    Evolution.congr_op, ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, map_mul]

/-- **`Evolution.congr` preserves the identity gate.** Transporting the identity evolution along a
system isomorphism is again the identity: `Evolution.congr e Evolution.id = Evolution.id`. Since
`Evolution.congr` conjugates the operator by the unital ⋆-algebra equivalence
`e.toIsometry.conjStarAlgEquiv`, this is `map_one` for that equivalence — the unit sibling of
`congr_comp`, so that `Evolution.congr e` is a monoid homomorphism. -/
theorem Evolution.congr_id {S T : QSystem} (e : S ≃ₛ T) :
    Evolution.congr e Evolution.id = Evolution.id := by
  ext1
  rw [Evolution.congr_op, Evolution.id_op, map_one, Evolution.id_op]

/-- **`Evolution.congr` along the identity isomorphism is the identity map.** Transporting a gate
`U` along the reflexive system isomorphism `QSystem.Iso.refl S` leaves it unchanged:
`Evolution.congr (QSystem.Iso.refl S) U = U`. The reflexivity law of `Evolution.congr` (the
`Evolution` sibling of `PureState.congr_refl` / `State.congr_refl`): the conjugation by
`(Iso.refl S).toIsometry = LinearIsometryEquiv.refl` is `StarAlgEquiv.refl`, which fixes `U.op`. A
proof that transports only *one* factor of a product gate (via `e.tmul (Iso.refl T)`) rewrites the
untouched factor with this. -/
theorem Evolution.congr_refl {S : QSystem} (U : Evolution S) :
    Evolution.congr (QSystem.Iso.refl S) U = U := by
  ext1
  rw [Evolution.congr_op, QSystem.Iso.refl_toIsometry,
    LinearIsometryEquiv.conjStarAlgEquiv_refl, StarAlgEquiv.coe_refl, id_eq]

/-- **`Evolution.congr` preserves the monoid unit.** Transporting the unit gate `1` (the identity
evolution) along a system isomorphism is again `1`: `Evolution.congr e 1 = 1`. This is `congr_id`
phrased for the `Evolution`-monoid unit (`Evolution.one_def`) — the `map_one` sibling of
`congr_comp`/`congr_prod`, so `Evolution.congr e` is a monoid homomorphism. Any proof that
transports an identity gate off/onto a register (e.g. an idle-wire budget) rewrites with this. -/
theorem Evolution.congr_one {S T : QSystem} (e : S ≃ₛ T) :
    Evolution.congr e (1 : Evolution S) = 1 := by
  simp only [Evolution.one_def, Evolution.congr_id]

/-- **`Evolution.congr` transports a list product gate-by-gate.** Transporting the sequential
composition (`Evolution`-monoid product) of a list of gates along a system isomorphism is the
product of the transported gates: `Evolution.congr e l.prod = (l.map (Evolution.congr e)).prod`. The
list form of `congr_comp`/`congr_id` (`Evolution.congr e` is a monoid homomorphism), proved by
induction on `l`. A proof that pushes a transport through a whole circuit — a product of
wire-addressed gates — rewrites each gate with this. -/
theorem Evolution.congr_prod {S T : QSystem} (e : S ≃ₛ T) (l : List (Evolution S)) :
    Evolution.congr e l.prod = (l.map (Evolution.congr e)).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, Evolution.one_def, Evolution.congr_id]
  | cons a t ih =>
      rw [List.prod_cons, Evolution.mul_def, Evolution.congr_comp, ← Evolution.mul_def,
        List.map_cons, List.prod_cons, ih]

/-! ### `State.congr` roundtrip cancellation

The mixed-state companions of the `PureState.congr` / `Evolution.congr` roundtrips above:
transporting a density operator through a system isomorphism and back is the identity. Reduces, via
`State.ext` / `State.congr_op`, to the operator `conjStarAlgEquiv` roundtrip
(`symm_conjStarAlgEquiv` turns the two conjugations into a `StarAlgEquiv` inverse pair). The
transport-back lemmas any *state* placement proof needs (the `Postulates` `State.congr` API exposes
only `congr_op`) — e.g. reading a marginal of a re-associated state back off the pre-association
product. -/

/-- **`State.congr` roundtrip (forward then back).** Transporting a state along `e` and then back
along `e.symm` recovers it: `State.congr e.symm (State.congr e ρ) = ρ`. -/
theorem State.congr_symm_congr {S T : QSystem} (e : S ≃ₛ T) (ρ : State S) :
    State.congr e.symm (State.congr e ρ) = ρ := by
  apply State.ext
  rw [State.congr_op, State.congr_op, QSystem.Iso.symm_toIsometry,
    ← LinearIsometryEquiv.symm_conjStarAlgEquiv, StarAlgEquiv.symm_apply_apply]

/-- **`State.congr` roundtrip (back then forward).** Transporting a state along `e.symm` and then
forward along `e` recovers it: `State.congr e (State.congr e.symm ρ) = ρ`. -/
theorem State.congr_congr_symm {S T : QSystem} (e : S ≃ₛ T) (ρ : State T) :
    State.congr e (State.congr e.symm ρ) = ρ := by
  apply State.ext
  rw [State.congr_op, State.congr_op, QSystem.Iso.symm_toIsometry,
    ← LinearIsometryEquiv.symm_conjStarAlgEquiv, StarAlgEquiv.apply_symm_apply]

/-- **`PureState.congr` along the identity is the identity.** Transporting a pure state along the
identity system isomorphism `QSystem.Iso.refl S` leaves it unchanged:
`PureState.congr (QSystem.Iso.refl S) ψ = ψ`. The identity law of the `PureState.congr`
functorial-action API, completing it alongside the composition law `congr_trans` and the roundtrips
above. -/
theorem PureState.congr_refl {S : QSystem} (ψ : PureState S) :
    PureState.congr (QSystem.Iso.refl S) ψ = ψ := by
  apply PureState.ext
  rw [PureState.congr_vec]
  rfl

/-- **`PureState.congr` is functorial in composition.** Transporting a pure state along a composite
system isomorphism `e.trans f` is transporting along `e` and then along `f`:
`PureState.congr (e.trans f) ψ = PureState.congr f (PureState.congr e ψ)`. The functoriality law
completing the `PureState.congr` transport API (`congr_vec` / the roundtrips above). -/
theorem PureState.congr_trans {S T U : QSystem} (e : S ≃ₛ T) (f : T ≃ₛ U) (ψ : PureState S) :
    PureState.congr (e.trans f) ψ = PureState.congr f (PureState.congr e ψ) := by
  apply PureState.ext
  simp only [PureState.congr_vec]
  rfl

/-- **`PureState.congr` distributes over the tensor of isomorphisms.** Transporting a product state
`u ⊗ v` along the tensor isomorphism `e.tmul f` is the product of the transports:
`PureState.congr (e.tmul f) (u ⊗ v) = (PureState.congr e u) ⊗ (PureState.congr f v)`. The monoidal
companion of `congr_trans`, riding the action `QSystem.Iso.tmul_toIsometry_tmul`. -/
theorem PureState.congr_tmul {S S' T T' : QSystem} (e : S ≃ₛ S') (f : T ≃ₛ T')
    (u : PureState S) (v : PureState T) :
    PureState.congr (QSystem.Iso.tmul e f) (u ⊗ v)
      = (PureState.congr e u) ⊗ (PureState.congr f v) := by
  apply PureState.ext
  simp only [PureState.congr_vec, PureState.tmul_vec, QSystem.Iso.tmul_toIsometry_tmul]
  rfl

/-- **`PureState.congr` along `comm` swaps a product pure state.** Transporting `ψ ⊗ φ` along the
swap isomorphism `QSystem.Iso.comm S T` yields `φ ⊗ ψ`. The `comm` companion of
`PureState.congr_tmul`, riding the action `QSystem.Iso.comm_toIsometry_tmul`; the reusable
ancilla-swap reshaping fact recurring across dilation proofs (e.g. reordering a product ancilla
`ωA ⊗ ωB` in `State.dilatedChannelNoComm_eq_dilatedChannel`). -/
theorem PureState.congr_comm_tmul {S T : QSystem} (ψ : PureState S) (φ : PureState T) :
    PureState.congr (QSystem.Iso.comm S T) (ψ.tmul φ) = φ.tmul ψ := by
  apply PureState.ext
  simp only [PureState.congr_vec, PureState.tmul_vec, QSystem.Iso.comm_toIsometry_tmul]
  rfl

/-- The `leftComm` isomorphism (backwards) on a product state exchanges the first two factors:
`(φ ⊗ (ψ ⊗ χ)).congr (leftComm A B C).symm = ψ ⊗ (φ ⊗ χ)`. The `leftComm` companion of the
associator transport `pureState_congr_assocSymm`, riding the action
`QSystem.Iso.leftComm_symm_toIsometry_tmul`. -/
theorem pureState_congr_leftCommSymm {A B C : QSystem} (ψ : PureState A) (φ : PureState B)
    (χ : PureState C) :
    (φ ⊗ (ψ ⊗ χ)).congr (QSystem.Iso.leftComm A B C).symm = ψ ⊗ (φ ⊗ χ) := by
  apply PureState.ext
  rw [PureState.congr_vec, PureState.tmul_vec, PureState.tmul_vec, PureState.tmul_vec,
    PureState.tmul_vec]
  exact QSystem.Iso.leftComm_symm_toIsometry_tmul A B C ψ.vec φ.vec χ.vec

end AxQM
