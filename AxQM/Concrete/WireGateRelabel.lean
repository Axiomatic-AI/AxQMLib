/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledSingleQubit

/-!
# Concrete: relabelling the wires of a fibrewise gate (N&C Ex 4.44)

Every statement here concerns matrices — the fibrewise gate `wireGate` and its instances
`mcCtrlSingleQubit` / `singleQubitOnWire` — the encoding equivalence, and a wire permutation.

## Why this file: moving a wire-addressed gate onto arbitrary wires

The register-realisation of the Deutsch gate `G = C²(iR_x(πα))` (Nielsen & Chuang, Exercise 4.44)
places `G` on *varying* triples of register wires: the whole reachability/compression argument
(`Concrete/DeutschWirePlacement.lean`, `…DeutschCompressedUniversality.lean`) reaches gates
`mcCtrlSingleQubit fullEnc {a, b} j g` for arbitrary distinct control wires `a, b` and target wire
`j`. Naming those placements as the *physical* Deutsch gate needs the base three-wire bridge
(`Concrete/DeutschRegisterBridge.lean`, controls `{0, 1}`, target `2`) transported onto the
arbitrary wires `{a, b}`, `j`. This file supplies the wire-move at the matrix level: a
*wire-addressed fibrewise gate is unchanged if the wires are permuted, provided the encoding is
correspondingly relabelled*.

Concretely, a wire permutation `σ : Equiv.Perm (Fin m)` induces the bit-string relabelling
`wireStringPerm σ : (Fin m → Fin 2) ≃ (Fin m → Fin 2)`, `y ↦ y ∘ σ.symm`, and precomposing the
encoding with it moves each wire index by `σ.symm`:

* `wireGate_wireStringPerm` — the general identity for the fibrewise gate,
  `wireGate enc j f = wireGate ((wireStringPerm σ).trans enc) (σ.symm j) (fun w => f (w ∘ σ.symm))`;
* `mcCtrlSingleQubit_wireStringPerm` — its specialisation to the multiply-controlled single-qubit
  gate, moving the control set to `S.map σ.symm.toEmbedding` and the target to `σ.symm j`;
* `singleQubitOnWire_wireStringPerm` — the uncontrolled corollary (the `S = ∅` case).

Choosing `σ` so that `σ.symm` sends the arbitrary wires `a, b, j` to the canonical `0, 1, 2` reduces
a placement on arbitrary wires to the base three-wire placement.
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- **The bit-string relabelling induced by a wire permutation.** For `σ : Equiv.Perm (Fin m)`,
`wireStringPerm σ` sends a bit-string `y : Fin m → Fin 2` to `y ∘ σ.symm` — the string whose value
at wire `k` is the old value at wire `σ.symm k`. Its inverse is precomposition with `σ`.
Precomposing an encoding `enc : (Fin m → Fin 2) ≃ Fin d` with it — `(wireStringPerm σ).trans enc` —
relabels the register wires by `σ`, moving a gate's target/control wires by `σ.symm`. -/
def wireStringPerm (σ : Equiv.Perm (Fin m)) : (Fin m → Fin 2) ≃ (Fin m → Fin 2) where
  toFun y k := y (σ.symm k)
  invFun z k := z (σ k)
  left_inv y := by funext k; simp
  right_inv z := by funext k; simp

@[simp] theorem wireStringPerm_apply (σ : Equiv.Perm (Fin m)) (y : Fin m → Fin 2) (k : Fin m) :
    wireStringPerm σ y k = y (σ.symm k) := rfl

@[simp] theorem wireStringPerm_symm_apply (σ : Equiv.Perm (Fin m)) (z : Fin m → Fin 2) (k : Fin m) :
    (wireStringPerm σ).symm z k = z (σ k) := rfl

/-- **The wire-relabelling identity for a fibrewise gate.** For a wire permutation
`σ : Equiv.Perm (Fin m)`, placing the fibrewise gate `wireGate enc j f` is the same as placing the
relabelled gate on the relabelled register: with the encoding precomposed by the string relabel
`wireStringPerm σ`, the target moves from `j` to `σ.symm j` and the block family `f` is reindexed to
`fun w => f (w ∘ σ.symm)`.

The `(i, i')` entries agree: the fibre condition "the bits off the target agree" is invariant under
the wire permutation (reindex the universally quantified wire by `σ`), the target values
`enc.symm i j` are unchanged (the moved target `σ.symm j` reads the same bit through the relabelled
encoding, `Equiv.apply_symm_apply`), and the block representative `update (enc.symm i) j 0`
transported through the relabel is exactly `fun k => update ((relabelled enc).symm i) (σ.symm j) 0
(σ.symm k)`. -/
theorem wireGate_wireStringPerm (σ : Equiv.Perm (Fin m)) (enc : (Fin m → Fin 2) ≃ Fin d)
    (j : Fin m) (f : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) :
    wireGate enc j f
      = wireGate ((wireStringPerm σ).trans enc) (σ.symm j)
          (fun w => f (fun k => w (σ.symm k))) := by
  have hE : ∀ (i : Fin d) (k : Fin m),
      ((wireStringPerm σ).trans enc).symm i k = enc.symm i (σ k) := fun i k => by
    rw [Equiv.symm_trans_apply, wireStringPerm_symm_apply]
  ext i i'
  rw [wireGate_apply, wireGate_apply]
  have hj : ((wireStringPerm σ).trans enc).symm i (σ.symm j) = enc.symm i j := by
    rw [hE i (σ.symm j), Equiv.apply_symm_apply]
  have hj' : ((wireStringPerm σ).trans enc).symm i' (σ.symm j) = enc.symm i' j := by
    rw [hE i' (σ.symm j), Equiv.apply_symm_apply]
  have hcond : (∀ k, k ≠ σ.symm j → ((wireStringPerm σ).trans enc).symm i k
        = ((wireStringPerm σ).trans enc).symm i' k)
      ↔ (∀ k, k ≠ j → enc.symm i k = enc.symm i' k) := by
    constructor
    · intro h l hl
      have hk : σ.symm l ≠ σ.symm j := fun he => hl (σ.symm.injective he)
      have := h (σ.symm l) hk
      rwa [hE i (σ.symm l), hE i' (σ.symm l), Equiv.apply_symm_apply] at this
    · intro h k hk
      have hl : σ k ≠ j := fun he => hk (by rw [← he, Equiv.symm_apply_apply])
      rw [hE i k, hE i' k]
      exact h (σ k) hl
  have hblk : (fun k => Function.update (((wireStringPerm σ).trans enc).symm i) (σ.symm j) 0
        (σ.symm k)) = Function.update (enc.symm i) j 0 := by
    funext k
    rcases eq_or_ne k j with rfl | hk
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun he => hk (σ.symm.injective he)),
        Function.update_of_ne hk, hE i (σ.symm k), Equiv.apply_symm_apply]
  refine if_congr hcond.symm ?_ rfl
  simp only [hblk, hj, hj']

/-- **The wire-relabelling identity for the multiply-controlled single-qubit gate.** Placing
`mcCtrlSingleQubit enc S j M2` — apply `M2` to wire `j` when every control wire in `S` is `1` — is
the same as placing the gate on the relabelled register (encoding precomposed with `wireStringPerm
σ`), with the control set moved to `S.map σ.symm.toEmbedding` and the target to `σ.symm j`.

The specialisation of `wireGate_wireStringPerm` at the multiply-controlled block
`fun y => if ∀ k ∈ S, y k = 1 then M2 else 1`: the reindexed block's control condition
`∀ k ∈ S, w (σ.symm k) = 1` is exactly `∀ k ∈ S.map σ.symm.toEmbedding, w k = 1`
(`Finset.forall_mem_map`). -/
theorem mcCtrlSingleQubit_wireStringPerm (σ : Equiv.Perm (Fin m)) (enc : (Fin m → Fin 2) ≃ Fin d)
    (S : Finset (Fin m)) (j : Fin m) (M2 : Matrix (Fin 2) (Fin 2) ℂ) :
    mcCtrlSingleQubit enc S j M2
      = mcCtrlSingleQubit ((wireStringPerm σ).trans enc) (S.map σ.symm.toEmbedding) (σ.symm j)
          M2 := by
  rw [mcCtrlSingleQubit, wireGate_wireStringPerm σ enc j, mcCtrlSingleQubit]
  congr 1
  funext w
  dsimp only
  refine if_congr ?_ rfl rfl
  simp only [Finset.forall_mem_map, Equiv.coe_toEmbedding]

/-- **The wire-relabelling identity for the uncontrolled single-qubit wire gate.** Placing
`singleQubitOnWire enc j g` — apply `g` to wire `j` — is the same as placing it on the relabelled
register with the target moved to `σ.symm j`. The `S = ∅` case of
`mcCtrlSingleQubit_wireStringPerm` (through `mcCtrlSingleQubit_empty`; the empty control set stays
empty under `Finset.map`). -/
theorem singleQubitOnWire_wireStringPerm (σ : Equiv.Perm (Fin m)) (enc : (Fin m → Fin 2) ≃ Fin d)
    (j : Fin m) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    singleQubitOnWire enc j g
      = singleQubitOnWire ((wireStringPerm σ).trans enc) (σ.symm j) g := by
  rw [← mcCtrlSingleQubit_empty enc j g, mcCtrlSingleQubit_wireStringPerm σ, Finset.map_empty,
    mcCtrlSingleQubit_empty]

end AxQM.Concrete
