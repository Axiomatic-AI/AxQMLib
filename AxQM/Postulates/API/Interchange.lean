/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SystemIsoComm
import ToMathlib.Analysis.InnerProductSpace.TensorProductInterchange
import ToMathlib.Analysis.InnerProductSpace.TensorProductInterchangePartialTrace

/-!
# AxQM.Postulates.API — four-factor interchange system isomorphisms

Structural reshapes of a fourfold composite, additions to the transport backbone of system
isomorphisms (`QSystem.Iso`) alongside `QSystem.Iso.refl/symm/trans/tmul/comm` and `QSystem.assoc`.
A fourfold composite `(A ⊗ B) ⊗ (C ⊗ D)` is the same quantum system however its four factors are
re-bracketed and re-ordered; these are the `QSystem.Iso` witnesses for the orderings needed
in Problem 4.6 and Exercise 12.22.

* `QSystem.Iso.interchange` — the **interchange braid** `(A ⊗ B) ⊗ (C ⊗ D) ≃ₛ (A ⊗ C) ⊗ (B ⊗ D)`
  exchanging the two *inner* factors `B` and `C`, the `QSystem.Iso` packaging of
  `TensorProduct.tensorTensorTensorCommIsometry`.
* `QSystem.interchangeBCAD` — the **BCAD interchange** `(A ⊗ B) ⊗ (C ⊗ D) ≃ₛ (B ⊗ C) ⊗ (A ⊗ D)`,
  the four-factor permutation `(A, B, C, D) ↦ (B, C, A, D)`, assembled as "swap the first pair, then
  interchange the middle".
* `QSystem.Iso.interchange_eq_assoc_comm` — the interchange braid **decomposed** into a composite of
  associators and one swap, exposing the braid as `QSystem.Iso` transport plumbing
  that can be peeled through (`State.congr_trans`, the reduced-marginal / product-unitary
  laws).

## Role in Problem 4.6 (interchange braid)

`QSystem.Iso.interchange` is the structural reshape the Nielsen & Chuang **Problem 4.6**
gate-teleportation identity ("Universality with prior entanglement") needs to move between the two
ways of laying out the same six qubits.  In the *physical* register the two input qubits sit
together and the two Bell pairs sit together, `(q_A ⊗ q_B) ⊗ (|Φ⁺⟩ ⊗ |Φ⁺⟩)`; but the single-qubit
`teleportation_identity` (and its parallel form `double_teleportation_identity`) apply on the
*two-setups* register `(q_A ⊗ |Φ⁺⟩) ⊗ (q_B ⊗ |Φ⁺⟩)`, each input beside its own Bell pair.  Passing
between them is exactly `interchange` with `A := q_A`, `B := q_B`, `C := |Φ⁺⟩₁`, `D := |Φ⁺⟩₂`.
`QSystem.assoc` and `QSystem.Iso.tmul` alone re-bracket but cannot swap adjacent factors, and
`QSystem.Iso.comm` swaps a *bipartite* composite but not two interior factors — the interchange
braid is the missing reshape.

## Role in Exercise 8.3 (BCAD interchange)

`QSystem.interchangeBCAD` is the structural piece Nielsen & Chuang **Exercise 8.3** needs (the
different-input/output-space operator-sum representation).  There a principal system `A ⊗ B` and an
environment `C ⊗ D` (prepared in a standard state `|0⟩`) interact by a joint unitary `U`, after
which systems `A` and `D` are discarded, leaving the output on `B ⊗ C`.  Because `A` and `D` are
*not* an adjacent factor of the natural register `(A ⊗ B) ⊗ (C ⊗ D)`, reading off the marginal on
`B ⊗ C` via `State.reducedLeft` (which traces out the *right* factor of a bipartite composite)
first requires regrouping the four factors into `(B ⊗ C) ⊗ (A ⊗ D)` — exactly `interchangeBCAD`.

## Design notes

* **The braid is built at the isometry level.**  Composing the braid out of `QSystem.assoc`
  / `QSystem.Iso.tmul` / `QSystem.Iso.comm` at the `QSystem.Iso` level makes computing its
  pure-tensor action intractable: the `≃ₗᵢ` `FunLike` coercion combined with the composite-system
  module instance (defeq but not syntactically equal to `TensorProduct`'s canonical module — the
  diamond documented in `BellState.lean` and `DoubleTeleportation.lean`) blocks `rw`/`simp` on the
  intermediate tensors.  Instead the isometry `tensorTensorTensorCommIsometry` is built and
  its action proved in `ToMathlib/` at the *raw* `TensorProduct` level; the `QSystem.Iso`
  here is just its packaging, and the action lemma transports through the definitional
  `.toIsometry`.
* **`interchangeBCAD` composes the braid with one swap.**  `interchangeBCAD A B C D` swaps the first
  pair `A ⊗ B ↦ B ⊗ A` with `comm`, then applies `interchange B A C D` (which sends
  `(B ⊗ A) ⊗ (C ⊗ D) ↦ (B ⊗ C) ⊗ (A ⊗ D)`).  Its pure-tensor action follows from
  `interchange_toIsometry_tmul_tmul` together with the `comm`/`tmul` action lemmas — a two-step
  rewrite, not `rfl`, since the braid's action is not definitional.
* **Generality.**  Each iso is stated over four arbitrary systems (the general transport
  fact); being a genuine `QSystem.Iso` it carries norm-preservation for free.  Compare
  `SystemIsoComm.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable (A B C D : QSystem)

/-- The **interchange braid** system isomorphism `(A ⊗ B) ⊗ (C ⊗ D) ≃ₛ (A ⊗ C) ⊗ (B ⊗ D)`:
the two inner factors `B` and `C` of a fourfold composite are exchanged, a pure regrouping of the
same four systems.  The underlying isometry is
`TensorProduct.tensorTensorTensorCommIsometry ℂ A.space B.space C.space D.space`; the swap-of-two-
interior-factors sibling of `QSystem.assoc` (re-bracket), `QSystem.Iso.tmul` (act factor-wise) and
`QSystem.Iso.comm` (swap a bipartite composite). -/
def QSystem.Iso.interchange : ((A ⊗ B) ⊗ (C ⊗ D)) ≃ₛ ((A ⊗ C) ⊗ (B ⊗ D)) :=
  ⟨TensorProduct.tensorTensorTensorCommIsometry ℂ A.space B.space C.space D.space⟩

/-- `.toIsometry` of the interchange braid is `TensorProduct.tensorTensorTensorCommIsometry`. -/
theorem QSystem.Iso.interchange_toIsometry :
    (QSystem.Iso.interchange A B C D).toIsometry
      = TensorProduct.tensorTensorTensorCommIsometry ℂ A.space B.space C.space D.space :=
  rfl

/-- The action of the interchange braid on a pure tensor:
`interchange ((a ⊗ b) ⊗ (c ⊗ d)) = (a ⊗ c) ⊗ (b ⊗ d)` — the two input qubits `a, c` are brought
together and the two ancillae `b, d` together (with `A B C D := q_A, q_B, |Φ⁺⟩₁, |Φ⁺⟩₂` this
turns the physical `(q_A ⊗ q_B) ⊗ (Φ⁺ ⊗ Φ⁺)` register into the two-setups register). -/
@[simp]
theorem QSystem.Iso.interchange_toIsometry_tmul_tmul
    (a : A.space) (b : B.space) (c : C.space) (d : D.space) :
    (QSystem.Iso.interchange A B C D).toIsometry ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))
      = (a ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] d) :=
  TensorProduct.tensorTensorTensorCommIsometry_tmul ℂ A.space B.space C.space D.space a b c d

/-- **The inverse of the interchange braid is the interchange with the two inner factors named in
swapped order.** The braid `interchange A B C D : (A ⊗ B) ⊗ (C ⊗ D) ≃ₛ (A ⊗ C) ⊗ (B ⊗ D)` exchanges
the inner factors `B` and `C`; its inverse `(A ⊗ C) ⊗ (B ⊗ D) → (A ⊗ B) ⊗ (C ⊗ D)` is again a braid
exchanging the two inner factors — namely `interchange A C B D`:

`(interchange A B C D).symm = interchange A C B D`.

The braid is its own kind of inverse (`tensorTensorTensorComm` is a self-inverse family up to
renaming its arguments). Proved at the level of operators: the underlying isometry symm is read
off from
`TensorProduct.tensorTensorTensorComm_symm` after passing to `LinearEquiv` via
`tensorTensorTensorCommIsometry_toLinearEquiv`, and the `QSystem.Iso` equality follows by
`congrArg QSystem.Iso.mk`. Lets a partial trace / transported state written over `interchange`'s
inverse be handled by the same forward-braid marginal laws (e.g.
`State.reducedLeft_congr_interchange_tmul`) — the reframing Nielsen & Chuang Exercise 12.22 needs to
move between the `(A ⊗ B) ∣ (CA ⊗ CB)` and `(A ⊗ CA) ∣ (B ⊗ CB)` cuts. -/
theorem QSystem.Iso.interchange_symm :
    (QSystem.Iso.interchange A B C D).symm = QSystem.Iso.interchange A C B D := by
  have h : (TensorProduct.tensorTensorTensorCommIsometry ℂ A.space B.space C.space D.space).symm
      = TensorProduct.tensorTensorTensorCommIsometry ℂ A.space C.space B.space D.space := by
    apply LinearIsometryEquiv.toLinearEquiv_injective
    rw [LinearIsometryEquiv.toLinearEquiv_symm,
      TensorProduct.tensorTensorTensorCommIsometry_toLinearEquiv,
      TensorProduct.tensorTensorTensorCommIsometry_toLinearEquiv,
      TensorProduct.tensorTensorTensorComm_symm]
  exact congrArg QSystem.Iso.mk h

/-- The **BCAD interchange** system isomorphism `(A ⊗ B) ⊗ (C ⊗ D) ≃ₛ (B ⊗ C) ⊗ (A ⊗ D)`:
the four-factor permutation `(A, B, C, D) ↦ (B, C, A, D)`.  Swap the first pair `A ⊗ B ↦ B ⊗ A`
with `comm`, then interchange the middle via `QSystem.Iso.interchange B A C D`.  This is the
regrouping that exposes `B ⊗ C` as the left factor and `A ⊗ D` as the right factor of a fourfold
composite, so that the marginal on `B ⊗ C` can be read off by tracing out the right factor
(Nielsen & Chuang Exercise 8.3). -/
def QSystem.interchangeBCAD : ((A ⊗ B) ⊗ (C ⊗ D)) ≃ₛ ((B ⊗ C) ⊗ (A ⊗ D)) :=
  (QSystem.Iso.tmul (QSystem.Iso.comm A B) (QSystem.Iso.refl (C ⊗ D))).trans
    (QSystem.Iso.interchange B A C D)

/-- The action of `QSystem.interchangeBCAD` on a pure tensor:
`(a ⊗ b) ⊗ (c ⊗ d) ↦ (b ⊗ c) ⊗ (a ⊗ d)`.  The first pair is swapped by `comm`, then the braid
`interchange B A C D` sends `(b ⊗ a) ⊗ (c ⊗ d) ↦ (b ⊗ c) ⊗ (a ⊗ d)`. -/
theorem QSystem.interchangeBCAD_toIsometry_tmul
    (a : A.space) (b : B.space) (c : C.space) (d : D.space) :
    (QSystem.interchangeBCAD A B C D).toIsometry ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))
      = (b ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] d) := by
  rw [QSystem.interchangeBCAD, QSystem.Iso.trans_toIsometry]
  have htrans := LinearIsometryEquiv.trans_apply
    ((QSystem.Iso.comm A B).tmul (QSystem.Iso.refl (C ⊗ D))).toIsometry
    (QSystem.Iso.interchange B A C D).toIsometry ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))
  have htmul := QSystem.Iso.tmul_toIsometry_tmul (QSystem.Iso.comm A B) (QSystem.Iso.refl (C ⊗ D))
    (a ⊗ₜ[ℂ] b) (c ⊗ₜ[ℂ] d)
  rw [htrans, htmul, QSystem.Iso.comm_toIsometry_tmul, QSystem.Iso.refl_toIsometry]
  have hinter := QSystem.Iso.interchange_toIsometry_tmul_tmul B A C D b a c d
  rw [LinearIsometryEquiv.coe_refl]
  exact hinter

/-- **The interchange braid as a composite of associators and a single swap.** The braid
`QSystem.Iso.interchange E F G H : (E ⊗ F) ⊗ (G ⊗ H) ≃ₛ (E ⊗ G) ⊗ (F ⊗ H)` — which exchanges the two
inner factors `F` and `G` — is *definitionally* the following five-step reshape built from the
transport backbone (`QSystem.assoc`, `QSystem.Iso.comm`, `QSystem.Iso.tmul`, `QSystem.Iso.refl`):

`(E ⊗ F) ⊗ (G ⊗ H)  →  E ⊗ (F ⊗ (G ⊗ H))`  (de-associate, `(assoc E F (G⊗H)).symm`)
`               →  E ⊗ ((F ⊗ G) ⊗ H)`      (re-bracket the tail, `id_E ⊗ assoc F G H`)
`               →  E ⊗ ((G ⊗ F) ⊗ H)`      (swap the inner pair, `id_E ⊗ (comm F G ⊗ id_H)`)
`               →  E ⊗ (G ⊗ (F ⊗ H))`      (de-associate the tail, `id_E ⊗ (assoc G F H).symm`)
`               →  (E ⊗ G) ⊗ (F ⊗ H)`      (re-associate, `assoc E G (F ⊗ H)`).

Whereas `QSystem.Iso.interchange` is packaged directly from the isometry
`TensorProduct.tensorTensorTensorCommIsometry` (so its pure-tensor action is a single lemma but its
composite structure is opaque), this identity exposes it as `QSystem.Iso` plumbing the entire
transport toolkit already understands: rewriting `interchange` to this form and peeling with
`State.congr_trans` / `PureState.congr_trans` lets a state, pure state, or evolution transported
along the braid be reduced through the per-factor `assoc` / `comm` / `tmul` reshape lemmas
(reduced-marginal laws, product-unitary laws, purification identities) — none of which act on the
braid directly. It is the structural key that unblocks tracing a partial trace *through* the
interchange (the Alice/Bob ancilla regrouping of Nielsen & Chuang Exercise 12.22).

Both sides agree on every pure tensor `(e ⊗ f) ⊗ (g ⊗ h) ↦ (e ⊗ g) ⊗ (f ⊗ h)` by `rfl` (each
component's action is definitional there), so the two isometries are equal by
`TensorProduct.ext_fourfold'` — the fourfold ext lemma for exactly this `(E ⊗ F) ⊗ (G ⊗ H)`
bracketing — after peeling the `LinearIsometryEquiv`/`LinearEquiv` coercions with the respective
`toLinearEquiv_injective` / `toLinearMap_injective`; the `QSystem.Iso` equality follows by
`congrArg QSystem.Iso.mk`. -/
theorem QSystem.Iso.interchange_eq_assoc_comm (E F G H : QSystem) :
    QSystem.Iso.interchange E F G H =
      ((((QSystem.assoc E F (G ⊗ H)).symm.trans
            ((QSystem.Iso.refl E).tmul (QSystem.assoc F G H))).trans
          ((QSystem.Iso.refl E).tmul ((QSystem.Iso.comm F G).tmul (QSystem.Iso.refl H)))).trans
        ((QSystem.Iso.refl E).tmul (QSystem.assoc G F H).symm)).trans
        (QSystem.assoc E G (F ⊗ H)) :=
  congrArg QSystem.Iso.mk (LinearIsometryEquiv.toLinearEquiv_injective
    (LinearEquiv.toLinearMap_injective (TensorProduct.ext_fourfold' fun _ _ _ _ => rfl)))

end AxQM
