/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.ControlledZ

/-!
# The Toffoli gate as a Hadamard-conjugated doubly-controlled `Z`

This file provides the algebraic heart of **Nielsen & Chuang, Exercise 4.24** ("verify that
Figure 4.9 implements the Toffoli gate"): the Toffoli gate equals the doubly-controlled-`Z` gate
conjugated on its target by Hadamard,

`toffoliGate = H₃ · C²(Z) · H₃`,   where `H₃ = (H.onRight qubit).onRight qubit`.

This is the operator identity that makes Figure 4.9 work: `X = H Z H`, so the doubly-controlled
`X` (the Toffoli) is the doubly-controlled `Z` sandwiched by `H` on the target. Figure 4.9's actual
circuit is the drawn gate sequence `P · H₃ · Q · H₃` (with `P`, `Q` the two `Hadamard`-free blocks
of one- and two-qubit gates); combined with the identity here, verifying Figure 4.9 reduces to the
`Hadamard`-free (hence superposition-free) monomial identity `P · Q = C²(Z)`. That final step, and
the Figure 4.9 circuit itself, are in `AxQM/NC/Ch4/Exercise4_24.lean`.

## Main results

* `toffoliGate_eq_hadamardConj_ccontrolledZ` — **the reduction:** `toffoliGate = H₃ · C²(Z) · H₃`,
  proved by two applications of the target-conjugation lemma `controlledUnitary_onRight_conj`
  (once through each control layer of `C²( · ) = C(C( · ))`) and the single-qubit identity
  `H Z H = X` (`hadamardGate_comp_pauliZGate_comp_hadamardGate`).

Supporting, reusable gate-algebra lemmas:

* `Evolution.onRight_comp` / `Evolution.onLeft_comp` — the right- and left-factor embeddings are
  homomorphisms for composition: `(V ⊗ 1)ᵣ · (W ⊗ 1)ᵣ = (V · W) ⊗ 1` (`onRight V S = 1 ⊗ V`) and
  `(V ⊗ 1) · (W ⊗ 1) = (V · W) ⊗ 1` (`onLeft V T = V ⊗ 1`).
* `Evolution.id_onRight` / `Evolution.id_onLeft` — `1.onRight S = 1` and `1.onLeft T = 1`.
* `hadamardGate_comp_self` — `H · H = 1` (a restatement of N&C Exercise 2.52, derived from
  `Concrete.hadamardC_mul_self`).
* `hadamardOnRight_sq` / `hadamardOnLeft_sq` — `(H.onRight S)² = 1` and `(H.onLeft S)² = 1`: the
  involutivity for the conjugation lemma's two `V · W = 1` side conditions, and the ancilla-wire
  `H² = 1` cancellation for `measureObservableCircuit_comp`.

-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **The right-factor embedding is a composition homomorphism.** With `V.onRight S = 1 ⊗ V`,
composing two right-factor gates composes their targets: `(1 ⊗ V) · (1 ⊗ W) = 1 ⊗ (V · W)`. -/
theorem Evolution.onRight_comp (S T : QSystem) (V W : Evolution T) :
    (V.onRight S).comp (W.onRight S) = (V.comp W).onRight S := by
  apply Evolution.ext
  change (TensorProduct.mapL 1 V.op).comp (TensorProduct.mapL 1 W.op)
      = TensorProduct.mapL 1 (V.op.comp W.op)
  rw [← TensorProduct.mapL_comp]
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]

/-- **The left-factor embedding is a composition homomorphism.** The mirror of
`Evolution.onRight_comp`: with `V.onLeft T = V ⊗ 1`, composing two left-factor gates composes their
sources, `(V ⊗ 1) · (W ⊗ 1) = (V · W) ⊗ 1`. -/
theorem Evolution.onLeft_comp (S T : QSystem) (V W : Evolution S) :
    (V.onLeft T).comp (W.onLeft T) = (V.comp W).onLeft T := by
  apply Evolution.ext
  change (TensorProduct.mapL V.op 1).comp (TensorProduct.mapL W.op 1)
      = TensorProduct.mapL (V.op.comp W.op) 1
  rw [← TensorProduct.mapL_comp]
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]

/-- **The identity gate on the right factor is the identity.** `1.onRight S = 1`. -/
theorem Evolution.id_onRight (S T : QSystem) :
    (Evolution.id : Evolution T).onRight S = Evolution.id := by
  apply Evolution.ext
  change TensorProduct.mapL (1 : S.space →L[ℂ] S.space) 1 = 1
  exact TensorProduct.mapL_one

/-- **The identity gate on the left factor is the identity.** `1.onLeft T = 1`.  The mirror of
`Evolution.id_onRight`. -/
theorem Evolution.id_onLeft (S T : QSystem) :
    (Evolution.id : Evolution S).onLeft T = Evolution.id := by
  apply Evolution.ext
  change TensorProduct.mapL (1 : S.space →L[ℂ] S.space) (1 : T.space →L[ℂ] T.space) = 1
  exact TensorProduct.mapL_one

/-- **The right-factor embedding carries a list product to the product of images:**
`(l.map (· .onRight S)).prod = (l.prod).onRight S`, i.e. `⨂ⱼ (1 ⊗ Uⱼ) = 1 ⊗ (⨂ⱼ Uⱼ)`. The
`List.prod` form of `Evolution.onRight_comp` / `Evolution.id_onRight` (the right-factor embedding is
a monoid homomorphism), proved by induction on the list. Used to reduce a cascade of right-factor
gates (e.g. the classically-controlled single-wire branch gates of a deferred control cascade) to a
single right-factor gate. -/
theorem Evolution.onRight_list_prod (S T : QSystem) (l : List (Evolution T)) :
    (l.map (fun U => U.onRight S)).prod = l.prod.onRight S := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil]; exact (Evolution.id_onRight S T).symm
  | cons hd tl ih =>
    rw [List.map_cons, List.prod_cons, Evolution.mul_def, ih, List.prod_cons, Evolution.mul_def,
      Evolution.onRight_comp]

/-- **The Hadamard gate is an involution:** `H · H = 1`. This is the content of N&C Exercise 2.52,
derived directly from the concrete matrix involution `Concrete.hadamardC_mul_self`. -/
theorem hadamardGate_comp_self : hadamardGate.comp hadamardGate = Evolution.id := by
  apply Evolution.ext
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC).comp
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC) = 1
  rw [← ContinuousLinearMap.mul_def, ← map_mul, Concrete.hadamardC_mul_self, map_one]

/-- **The Hadamard gate on the right factor squares to the identity:**
`(H.onRight S) · (H.onRight S) = 1`. Supplies the `V · W = 1` side condition of
`controlledUnitary_onRight_conj` for the outer control layer of the Toffoli. -/
theorem hadamardOnRight_sq (S : QSystem) :
    (hadamardGate.onRight S).comp (hadamardGate.onRight S) = Evolution.id := by
  rw [Evolution.onRight_comp, hadamardGate_comp_self, Evolution.id_onRight]

/-- **The Hadamard gate on the left factor squares to the identity:**
`(H.onLeft S) · (H.onLeft S) = 1`, the left-factor mirror of `hadamardOnRight_sq` — the same
3-lemma reduction via `Evolution.onLeft_comp`, `hadamardGate_comp_self` (`H² = 1`) and
`Evolution.id_onLeft`. Supplies the ancilla-wire `H² = 1` cancellation for
`measureObservableCircuit_comp`. -/
theorem hadamardOnLeft_sq (S : QSystem) :
    (hadamardGate.onLeft S).comp (hadamardGate.onLeft S) = Evolution.id := by
  rw [Evolution.onLeft_comp, hadamardGate_comp_self, Evolution.id_onLeft]

/-- **Toffoli gate as a Hadamard-conjugated doubly-controlled `Z`** (Nielsen & Chuang,
Exercise 4.24, the operator identity behind Figure 4.9). On the three-qubit system
`qubit ⊗ (qubit ⊗ qubit)` (controls `q₁, q₂`, target `q₃`),

`toffoliGate = (H on q₃) · C²(Z) · (H on q₃)`,

where `H on q₃ = (hadamardGate.onRight qubit).onRight qubit` and `C²(Z) = ccontrolledUnitary
pauliZGate`. Since `X = H Z H`, the doubly-controlled `X` is the doubly-controlled `Z` conjugated by
`H` on the target. Proved by rewriting `X = H Z H` inside the inner `controlledUnitary` and pushing
the two Hadamards out through each control layer with `controlledUnitary_onRight_conj` (using
`H · H = 1` and `(H.onRight qubit) · (H.onRight qubit) = 1` for its side conditions). -/
theorem toffoliGate_eq_hadamardConj_ccontrolledZ :
    toffoliGate
      = ((hadamardGate.onRight qubit).onRight qubit).comp
          ((ccontrolledUnitary pauliZGate).comp
            ((hadamardGate.onRight qubit).onRight qubit)) := by
  rw [toffoliGate, ccontrolledUnitary, ← hadamardGate_comp_pauliZGate_comp_hadamardGate,
    ← controlledUnitary_onRight_conj pauliZGate hadamardGate hadamardGate hadamardGate_comp_self,
    ccontrolledUnitary,
    ← controlledUnitary_onRight_conj (controlledUnitary pauliZGate)
      (hadamardGate.onRight qubit) (hadamardGate.onRight qubit) (hadamardOnRight_sq qubit)]

end AxQM
