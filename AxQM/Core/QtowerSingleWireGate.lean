/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledNotBasis
import AxQM.Postulates.API.ControlledControlledUnitary

/-!
# Placing a single-qubit gate on one wire of the control tower (N&C Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) reads the Figure 5.1 QFT circuit on the
`(n+1)`-qubit control tower `qtower n qubit` (the register bridge `quditPowTower`). Its
gates come in three shapes: the swap layer (a *wire permutation*, already placed on the tower as
`Evolution.qtowerPermWires`), the controlled-`Rₖ` rotations (two-wire), and the **Hadamards** — each
a single-qubit gate acting on *one wire*. This file defines the wire-addressed placement of a
single-qubit gate on the tower, the direct sibling of `Evolution.qtowerPermWires`, with its
computational-basis action.

## What is formalised

* `towerProd n ψ` — the **product state** `ψ 0 ⊗ ψ 1 ⊗ ⋯ ⊗ ψ n` on `qtower n qubit` built from an
  arbitrary family of single-wire pure states `ψ : Fin (n+1) → PureState qubit`. The
  arbitrary-per-wire generalisation of the computational tower basis `towerKet` (`towerKet` is the
  special case `ψ i = |b i⟩`, `towerKet_eq_towerProd`); it is needed because a single-wire gate can
  send a basis wire to a *superposition* (a Hadamard does), so the output is a product state whose
  wires are no longer all basis states.
* `Evolution.qtowerSingleWire n i g` — the **single-wire gate**: the single-qubit `Evolution` `g`
  placed on wire `i` of `qtower n qubit`, the identity on every other wire. Defined by recursion on
  the tower: on the head wire (`i = 0`) it is `g.onLeft` (`g ⊗ 1`), and on a later wire (`i = i'+1`)
  it wraps the placement on the tail with an idle head, `(qtowerSingleWire i' g).onRight qubit`
  (`1 ⊗ ⋯`) — the peel `qtower (n+1) qubit = qubit ⊗ qtower n qubit` that `towerKet` and
  `mcCtrl` are built on.
* `qtowerSingleWire_evolvePure_towerProd` — the **action**: `qtowerSingleWire n i g` acts on a
  product state `towerProd n ψ` by updating exactly wire `i`, `ψ ↦ Function.update ψ i (g ψᵢ)`,
  leaving every other wire untouched. Proved by recursion on the tower, peeling the head with
  `Evolution.onLeft_evolvePure` / `Evolution.onRight_evolvePure` and matching the update against
  `Fin.tail_update_zero` / `Fin.tail_update_succ` — the analog of `unCtrl_evolvePure_qtowerKet`.
* `qtowerSingleWire_evolvePure_towerKet` — the specialisation to a **computational-basis** input:
  `qtowerSingleWire n i g` sends `towerKet n b` to the product state that is `|b j⟩` on every wire
  `j ≠ i` and `g |b i⟩` on wire `i`. This is the form the wire-addressed re-expression of the
  Figure 5.1 Hadamards (read on the tower through the bridge) is matched against.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The product state on the tower -/

/-- **The product state** `ψ 0 ⊗ ψ 1 ⊗ ⋯ ⊗ ψ n` on `qtower n qubit`, built from an arbitrary family
`ψ : Fin (n+1) → PureState qubit` of single-wire pure states (`ψ 0` the outermost / head wire). The
arbitrary-per-wire generalisation of the computational tower basis `towerKet` (recovered as the
special case `ψ i = |b i⟩`, `towerKet_eq_towerProd`); it is what a single-wire gate produces, since
that gate may send a basis wire to a superposition. -/
def towerProd : (n : ℕ) → (Fin (n + 1) → PureState qubit) → PureState (qtower n qubit)
  | 0, ψ => ψ 0
  | n + 1, ψ => (ψ 0) ⊗ towerProd n (Fin.tail ψ)

/-- Base unfolding of `towerProd`: a single-wire tower is the pure state of its one wire. -/
@[simp] theorem towerProd_zero (ψ : Fin 1 → PureState qubit) : towerProd 0 ψ = ψ 0 := rfl

/-- Step unfolding of `towerProd`: peel the head wire as a left tensor factor,
`towerProd (n+1) ψ = ψ 0 ⊗ towerProd n (Fin.tail ψ)`. -/
theorem towerProd_succ (n : ℕ) (ψ : Fin (n + 2) → PureState qubit) :
    towerProd (n + 1) ψ = (ψ 0) ⊗ towerProd n (Fin.tail ψ) := rfl

/-- **The `towerProd` constructor.** The right-nested tower product state of `Fin.cons x φ` splits
off its head factor: `towerProd (n+1) (Fin.cons x φ) = x ⊗ towerProd n φ`. The constructor companion
of the destructor `towerProd_succ`, packaging a head-plus-tail tensor back into a single tower
product. -/
theorem towerProd_cons (n : ℕ) (x : PureState qubit) (φ : Fin (n + 1) → PureState qubit) :
    towerProd (n + 1) (Fin.cons x φ) = x.tmul (towerProd n φ) := by
  rw [towerProd_succ, Fin.cons_zero, Fin.tail_cons]

/-- **The computational tower basis is the product of its basis wires.** `towerKet n b` is the
product state `towerProd n` of the single-wire computational-basis states `|b j⟩`: both peel the
head wire the same way, so this holds by induction on `n`. This exhibits `towerKet` as the
basis-input special case of `towerProd`, the bridge the single-wire gate action uses to specialise
from an arbitrary product input to a computational-basis one. -/
theorem towerKet_eq_towerProd (n : ℕ) (b : Fin (n + 1) → Fin 2) :
    towerKet n b = towerProd n (fun j => qubitBasis (b j)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [towerKet_succ, towerProd_succ, ih]; rfl

/-- **Updating one basis wire commutes with `towerKet`.** Replacing wire `t.rev` of the
basis-wire family `fun j => |b j⟩` by `|z⟩` gives the tower product of the bit-string `b` updated at
`t.rev`:
`towerProd n (Function.update (fun j => |b j⟩) t.rev |z⟩) = towerKet n (Function.update b t.rev z)`.
Both sides are the product of the same per-wire basis kets (`towerKet_eq_towerProd` then a pointwise
`Function.update` comparison). The shared ket-bookkeeping step every non-diagonal single-wire gate's
tower re-expression (`AxQM/Core/QftTowerHadamard.lean`,
`AxQM/Core/FourGateReachableWireTower.lean`, `AxQM/Core/PauliDiagWireTower.lean`) uses to name the
updated branch ket. -/
theorem towerProd_update_qubitBasis {n : ℕ} (b : Fin (n + 1) → Fin 2) (t : Fin (n + 1))
    (z : Fin 2) :
    towerProd n (Function.update (fun j => qubitBasis (b j)) t.rev (qubitBasis z))
      = towerKet n (Function.update b t.rev z) := by
  rw [towerKet_eq_towerProd]
  congr 1
  funext j
  rcases eq_or_ne j t.rev with rfl | hj
  · rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]

/-- **The reversed, wire-`t`-updated digit-string is the wire-`t.rev`-updated string.**
`(fun i => Function.update (fun i' => b i'.rev) t z i.rev) = Function.update b t.rev z` — the
`Fin.rev` bookkeeping that aligns the big-endian register bridge with the little-endian wire
indexing when a single wire is updated. Off wire `t.rev` both sides restrict to `b ∘ Fin.rev ∘ rev =
b` (`Fin.rev_rev`); at wire `t.rev` both are `z`. Shared by every single-wire gate's tower
re-expression. -/
theorem update_rev_eq {n : ℕ} (b : Fin (n + 1) → Fin 2) (t : Fin (n + 1)) (z : Fin 2) :
    (fun i => Function.update (fun i' => b i'.rev) t z i.rev) = Function.update b t.rev z := by
  funext i
  rcases eq_or_ne i t.rev with rfl | hi
  · rw [Fin.rev_rev, Function.update_self, Function.update_self]
  · have hi' : i.rev ≠ t := fun h => hi (by rw [← h, Fin.rev_rev])
    rw [Function.update_of_ne hi', Function.update_of_ne hi, Fin.rev_rev]

/-! ### The single-wire gate on the tower -/

/-- **A single-qubit gate placed on one wire of the control tower** `qtower n qubit`: the gate `g`
acts on wire `i`, the identity on every other wire. Defined by recursion on the tower — on the head
wire (`i = 0`) it is `g.onLeft (qtower n qubit)` (`g ⊗ 1`), and on a later wire (`i = i'+1`) it
wraps the placement on the tail with an idle head,
`(Evolution.qtowerSingleWire n i' g).onRight qubit`
(`1 ⊗ ⋯`). The wire-addressed placement of a one-qubit gate on the tower — the shape of the
Figure 5.1 Hadamards — the single-gate sibling of the wire-permutation gate
`Evolution.qtowerPermWires`; its basis action is `qtowerSingleWire_evolvePure_towerKet`. -/
def Evolution.qtowerSingleWire :
    (n : ℕ) → Fin (n + 1) → Evolution qubit → Evolution (qtower n qubit)
  | 0, _, g => g
  | n + 1, i, g =>
      Fin.cases (g.onLeft (qtower n qubit))
        (fun i' => (Evolution.qtowerSingleWire n i' g).onRight qubit) i

/-- Head-wire unfolding: on wire `0` the single-wire gate is `g` on the head factor,
`g.onLeft (qtower n qubit) = g ⊗ 1`. -/
theorem Evolution.qtowerSingleWire_zero (n : ℕ) (g : Evolution qubit) :
    Evolution.qtowerSingleWire (n + 1) 0 g = g.onLeft (qtower n qubit) := by
  rfl

/-- Later-wire unfolding: on wire `i'+1` the single-wire gate wraps the tail placement with an idle
head, `(Evolution.qtowerSingleWire n i' g).onRight qubit = 1 ⊗ ⋯`. -/
theorem Evolution.qtowerSingleWire_succ (n : ℕ) (i' : Fin (n + 1)) (g : Evolution qubit) :
    Evolution.qtowerSingleWire (n + 1) i'.succ g
      = (Evolution.qtowerSingleWire n i' g).onRight qubit := by
  rfl

/-- **The single-wire placement of the identity gate is the identity.** Placing the identity gate on
any wire `i` of the tower leaves every wire — including `i` — untouched, so
`qtowerSingleWire n i 1 = 1`. By recursion on the tower: the head wire (`i = 0`) is
`Evolution.id_onLeft`, a later wire (`i = i'+1`) reduces to the tail placement (induction
hypothesis) with an idle head, `Evolution.id_onRight`. Together with
`Evolution.qtowerSingleWire_comp` this exhibits `qtowerSingleWire n i` as a monoid homomorphism
in the placed gate (identity to identity, composition to composition). -/
theorem Evolution.qtowerSingleWire_id :
    ∀ (n : ℕ) (i : Fin (n + 1)),
      Evolution.qtowerSingleWire n i Evolution.id = Evolution.id
  | 0, _ => rfl
  | n + 1, i => by
      refine Fin.cases ?_ (fun i' => ?_) i
      · rw [Evolution.qtowerSingleWire_zero]
        exact Evolution.id_onLeft _ _
      · rw [Evolution.qtowerSingleWire_succ, Evolution.qtowerSingleWire_id n i']
        exact Evolution.id_onRight _ _

/-- **The single-wire placement respects composition.** Placing a composite gate `g · h` on wire `i`
is the composite of the individual placements: `qtowerSingleWire n i (g · h) =
(qtowerSingleWire n i g) · (qtowerSingleWire n i h)` — the placement touches only wire `i`, so the
two factors act on that wire in sequence and idly elsewhere. By recursion on the tower, from
`Evolution.onLeft_comp` (head wire) and `Evolution.onRight_comp` (later wire); together with
`Evolution.qtowerSingleWire_id` this makes `qtowerSingleWire n i` a monoid homomorphism in the
placed gate. -/
theorem Evolution.qtowerSingleWire_comp :
    ∀ (n : ℕ) (i : Fin (n + 1)) (g h : Evolution qubit),
      Evolution.qtowerSingleWire n i (g.comp h)
        = (Evolution.qtowerSingleWire n i g).comp (Evolution.qtowerSingleWire n i h)
  | 0, _, _, _ => rfl
  | n + 1, i, g, h => by
      refine Fin.cases ?_ (fun i' => ?_) i
      · rw [Evolution.qtowerSingleWire_zero, Evolution.qtowerSingleWire_zero,
          Evolution.qtowerSingleWire_zero]
        exact (Evolution.onLeft_comp _ _ g h).symm
      · rw [Evolution.qtowerSingleWire_succ, Evolution.qtowerSingleWire_succ,
          Evolution.qtowerSingleWire_succ, Evolution.qtowerSingleWire_comp n i' g h]
        exact (Evolution.onRight_comp _ _ _ _).symm

/-- **Computational action of the single-wire gate on a product input.** Placing `g` on wire `i`
acts on the product state `towerProd n ψ` by updating exactly that wire and leaving the rest fixed:

  `(qtowerSingleWire n i g) (ψ 0 ⊗ ⋯ ⊗ ψ n) = ψ 0 ⊗ ⋯ ⊗ (g ψᵢ) ⊗ ⋯ ⊗ ψ n`,

i.e. `towerProd n (Function.update ψ i (g.evolvePure (ψ i)))`. Proved by recursion on the tower: the
head wire is peeled with `Evolution.onLeft_evolvePure` (`i = 0`, `Fin.tail_update_zero`) or
`Evolution.onRight_evolvePure` (`i = i'+1`, `Fin.tail_update_succ`), the analog of
`unCtrl_evolvePure_qtowerKet`. This is the wire-locality of the placement: it touches only wire `i`.
-/
theorem qtowerSingleWire_evolvePure_towerProd :
    ∀ (n : ℕ) (i : Fin (n + 1)) (g : Evolution qubit) (ψ : Fin (n + 1) → PureState qubit),
      (Evolution.qtowerSingleWire n i g).evolvePure (towerProd n ψ)
        = towerProd n (Function.update ψ i (g.evolvePure (ψ i)))
  | 0, i, g, ψ => by
      obtain rfl := Fin.fin_one_eq_zero i
      simp only [qtower, Evolution.qtowerSingleWire, towerProd_zero, Function.update_self]
  | n + 1, i, g, ψ => by
      refine Fin.cases ?_ ?_ i
      · simp only [qtower, Evolution.qtowerSingleWire_zero, towerProd_succ,
          Evolution.onLeft_evolvePure, Function.update_self, Fin.tail_update_zero]
      · intro i'
        simp only [qtower, Evolution.qtowerSingleWire_succ, towerProd_succ,
          Evolution.onRight_evolvePure,
          qtowerSingleWire_evolvePure_towerProd n i' g (Fin.tail ψ),
          Function.update_of_ne (Fin.succ_ne_zero i').symm, Fin.tail_update_succ]
        rfl

/-- **Computational action of the single-wire gate on a basis input.** Placing `g` on wire `i` sends
the computational tower basis state `towerKet n b` to the product state that is `|b j⟩` on every
wire `j ≠ i` and `g |b i⟩` on wire `i`:

  `(qtowerSingleWire n i g) (towerKet n b)
     = towerProd n (Function.update (fun j => |b j⟩) i (g |b i⟩))`.

The specialisation of `qtowerSingleWire_evolvePure_towerProd` to a basis input via
`towerKet_eq_towerProd`. This is the form the Figure 5.1 Hadamards — read on the tower through the
register bridge — are re-expressed against. -/
theorem qtowerSingleWire_evolvePure_towerKet (n : ℕ) (i : Fin (n + 1)) (g : Evolution qubit)
    (b : Fin (n + 1) → Fin 2) :
    (Evolution.qtowerSingleWire n i g).evolvePure (towerKet n b)
      = towerProd n (Function.update (fun j => qubitBasis (b j)) i
          (g.evolvePure (qubitBasis (b i)))) := by
  rw [towerKet_eq_towerProd, qtowerSingleWire_evolvePure_towerProd]

end AxQM
