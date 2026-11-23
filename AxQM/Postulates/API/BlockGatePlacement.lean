/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TensorPowSplit
import AxQM.Postulates.API.LeftPairGate
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.SystemIsoComm
import AxQM.Postulates.PiTensorState

/-!
# Placing a gate on a contiguous block of wires (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit implementing
`Cⁿ(X)`. Reducing the multiply-controlled-`NOT` blocks `Cᵏ(X)` of the tight `(n+1)`-wire circuit to
two-control gates requires placing a `Toffoli`/`CNOT` on a chosen set of wires. This is done in two
moves on the **symmetric** register `S ^⊗ₛ (a+b)`: first place the gate on the *first* `a` wires (a
contiguous block), then relabel the wires by a permutation (`Evolution.permWires`) to send that
block to the target wire set. This file gives the first move.

The block-split isomorphism `QSystem.tensorPowAdd` gives
`S ^⊗ₛ (a+b) ≃ₛ (S ^⊗ₛ a) ⊗ (S ^⊗ₛ b)`. Here it is used to *place a gate*: a gate
`G : Evolution (S ^⊗ₛ a)` on the first block is lifted to `G.onLeft (S ^⊗ₛ b)` (act as `G` on the
`a`-wire block, identity on the `b`-wire block) and transported back onto the whole register through
`(tensorPowAdd S a b).symm` by `Evolution.congr`.

## What is formalised

* `Evolution.onBlock G b` — the **block-placement gate** on `S ^⊗ₛ (a+b)`: given a gate
  `G : Evolution (S ^⊗ₛ a)` on the first `a` wires, the closed-system `Evolution` acting as `G` on
  those wires and as the identity on the remaining `b`, defined as `G.onLeft (S ^⊗ₛ b)` transported
  across `(QSystem.tensorPowAdd S a b).symm` via `Evolution.congr`.
* `QSystem.tensorPowAdd_congr_piTensor` — the **product-state split dictionary**: the block-split
  isomorphism carries a symmetric product basis state `⨂ᵢ |f i⟩` on `S ^⊗ₛ (a+b)` to the pair of
  product states `(⨂ᵢ |f (castAdd i)⟩) ⊗ (⨂ⱼ |f (natAdd j)⟩)` on the two blocks — the `PureState`
  companion of `QSystem.tensorPowAdd_toIsometry_tprod`.
* `Evolution.onBlock_evolvePure_congr` — the **transport action**: on a state transported from a
  pair `u ⊗ v` (with `u` on the first block, `v` on the second), `onBlock G b` acts as `G` on `u`,
  `(G.onBlock b).evolvePure ((u ⊗ v).congr e⁻¹) = ((G.evolvePure u) ⊗ v).congr e⁻¹`. Immediate from
  the transport law `Evolution.congr_evolvePure_congr` and `Evolution.onLeft_evolvePure`.
* `Evolution.onBlock_evolvePure_piTensor` — the **computational-basis action** in product form: on a
  symmetric product input `⨂ᵢ |f i⟩`, `onBlock G b` applies `G` to the first-block product
  `⨂ᵢ |f (castAdd i)⟩` and leaves the second-block product `⨂ⱼ |f (natAdd j)⟩` untouched,
  reassembled through `(tensorPowAdd S a b).symm`. This is the placement dictionary used once
  the wires are relabelled by `Evolution.permWires`.

## Design notes

* **Why the `onLeft`-then-transport route.** Placing a gate on the *first* `a` factors is exactly
  what `Evolution.onLeft` does after the register is regrouped as `(S ^⊗ₛ a) ⊗ (S ^⊗ₛ b)` — the
  shape `QSystem.tensorPowAdd` produces. Transporting the regrouped gate back with `Evolution.congr`
  keeps every proof a one-line application of the transport law `Evolution.congr_evolvePure_congr`,
  reusing the existing block actions rather than re-deriving `PiTensorProduct` surgery.
* **Why the product-state form.** The `Cᵏ(X)`-block reduction of Exercise 4.29 reads gate effects on
  *computational basis* inputs (products `⨂ᵢ |f i⟩`), so `onBlock_evolvePure_piTensor` — not just
  the abstract transport action — is the usable interface. Its proof splits the input product with
  `QSystem.tensorPowAdd_congr_piTensor` (then `PureState.congr_symm_congr` to pass to the `.symm`
  side) and applies `onBlock_evolvePure_congr`; the `_toIsometry_tprod` action already used in the
  dictionary lemma is the only further ingredient.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem} {a : ℕ}

/-- **Product-state split dictionary for the block isomorphism.** The block-split isomorphism
`QSystem.tensorPowAdd S a b` carries the symmetric product basis state `⨂ᵢ |f i⟩` on `S ^⊗ₛ (a+b)`
to the pair of block product states `(⨂ᵢ |f (Fin.castAdd b i)⟩) ⊗ (⨂ⱼ |f (Fin.natAdd a j)⟩)` — the
first `a` wires and the last `b` wires. The `PureState` companion of the product
action `QSystem.tensorPowAdd_toIsometry_tprod`, used to feed a computational-basis input into the
block-placement gate. -/
theorem QSystem.tensorPowAdd_congr_piTensor (a b : ℕ) (f : Fin (a + b) → PureState S) :
    PureState.congr (QSystem.tensorPowAdd S a b) (PureState.piTensor f)
      = PureState.piTensor (fun i => f (Fin.castAdd b i))
          ⊗ PureState.piTensor (fun j => f (Fin.natAdd a j)) := by
  apply PureState.ext
  simp only [PureState.tmul_vec, PureState.piTensor_vec]
  exact QSystem.tensorPowAdd_toIsometry_tprod S a b (fun i => (f i).vec)

/-- **Backward product dictionary for the block isomorphism.** The `.symm` companion of
`QSystem.tensorPowAdd_congr_piTensor`: the inverse block-split `(QSystem.tensorPowAdd S a b).symm`
reassembles a pair of symmetric products `(⨂ᵢ Pᵢ) ⊗ (⨂ⱼ Qⱼ)` on the two blocks into the single
symmetric product `⨂ (Fin.append P Q)` on `S ^⊗ₛ (a+b)`. This is the direction consumed when a gate
computed on the split register `(S ^⊗ₛ a) ⊗ (S ^⊗ₛ b)` (e.g. a placed block gate) is transported
back onto the whole `(a+b)`-wire register on a computational product input. Proved from the forward
dictionary through the `PureState.congr` roundtrip `PureState.congr_symm_congr` (bridged in term
mode: the goal's `⊗` carries the system head `S ^⊗ₛ a` while the intermediate `have` carries the
defeq-but-syntactically-distinct `⨂ₛ i, S`, so `rw` cannot apply the intermediate equation). -/
theorem QSystem.tensorPowAdd_symm_congr_piTensor (a b : ℕ)
    (P : Fin a → PureState S) (Q : Fin b → PureState S) :
    PureState.congr (QSystem.tensorPowAdd S a b).symm
        ((PureState.piTensor P) ⊗ (PureState.piTensor Q))
      = PureState.piTensor (Fin.append P Q) := by
  have heq : PureState.congr (QSystem.tensorPowAdd S a b) (PureState.piTensor (Fin.append P Q))
      = (PureState.piTensor P) ⊗ (PureState.piTensor Q) := by
    rw [QSystem.tensorPowAdd_congr_piTensor]
    congr 1
    · exact congrArg PureState.piTensor (funext fun i => Fin.append_left P Q i)
    · exact congrArg PureState.piTensor (funext fun j => Fin.append_right P Q j)
  exact (congrArg (PureState.congr (QSystem.tensorPowAdd S a b).symm) heq.symm).trans
    (PureState.congr_symm_congr _ _)

/-- **The block-placement gate** on `S ^⊗ₛ (a+b)`: given a gate `G : Evolution (S ^⊗ₛ a)` on the
first `a` wires, the closed-system `Evolution` that acts as `G` on those `a` wires and as the
identity on the remaining `b`. It is `G.onLeft (S ^⊗ₛ b)` — the gate on the left block of the split
register `(S ^⊗ₛ a) ⊗ (S ^⊗ₛ b)` — transported back onto the full `(a+b)`-wire register through the
block-split isomorphism `(QSystem.tensorPowAdd S a b).symm` via `Evolution.congr`. Its
computational-basis action is `Evolution.onBlock_evolvePure_piTensor`. -/
def Evolution.onBlock (G : Evolution (S ^⊗ₛ a)) (b : ℕ) : Evolution (S ^⊗ₛ (a + b)) :=
  (G.onLeft (S ^⊗ₛ b)).congr (QSystem.tensorPowAdd S a b).symm

/-- **Transport action of the block-placement gate.** Feeding `Evolution.onBlock G b` a state
transported from a pair `u ⊗ v` (with `u` on the first `a`-wire block and `v` on the last `b`-wire
block) applies `G` to `u` alone:
`(G.onBlock b).evolvePure ((u ⊗ v).congr eˢ) = ((G u) ⊗ v).congr eˢ` where
`eˢ = (QSystem.tensorPowAdd S a b).symm`. Immediate from unfolding `onBlock`, the transport law
`Evolution.congr_evolvePure_congr`, and `Evolution.onLeft_evolvePure`. -/
theorem Evolution.onBlock_evolvePure_congr (G : Evolution (S ^⊗ₛ a)) (b : ℕ)
    (u : PureState (S ^⊗ₛ a)) (v : PureState (S ^⊗ₛ b)) :
    (G.onBlock b).evolvePure (PureState.congr (QSystem.tensorPowAdd S a b).symm (u ⊗ v))
      = PureState.congr (QSystem.tensorPowAdd S a b).symm ((G.evolvePure u) ⊗ v) := by
  unfold Evolution.onBlock
  rw [Evolution.congr_evolvePure_congr, Evolution.onLeft_evolvePure]

/-- **Computational-basis action of the block-placement gate.** On a symmetric product input
`⨂ᵢ |f i⟩` (a computational basis state of `S ^⊗ₛ (a+b)`), `Evolution.onBlock G b` applies `G` to
the first-block product `⨂ᵢ |f (Fin.castAdd b i)⟩` and leaves the second-block product
`⨂ⱼ |f (Fin.natAdd a j)⟩` untouched, the two reassembled through
`(QSystem.tensorPowAdd S a b).symm`. This is the wire-addressed placement dictionary the
`Cᵏ(X)`-block `Toffoli` reduction consumes (after the block is relabelled onto the target wires by
`Evolution.permWires`). Proved by splitting the input product with
`QSystem.tensorPowAdd_congr_piTensor` (via the `PureState.congr` roundtrip
`PureState.congr_symm_congr`) and applying `Evolution.onBlock_evolvePure_congr`. -/
theorem Evolution.onBlock_evolvePure_piTensor (G : Evolution (S ^⊗ₛ a)) (b : ℕ)
    (f : Fin (a + b) → PureState S) :
    (G.onBlock b).evolvePure (PureState.piTensor f)
      = PureState.congr (QSystem.tensorPowAdd S a b).symm
          ((G.evolvePure (PureState.piTensor fun i => f (Fin.castAdd b i)))
            ⊗ PureState.piTensor fun j => f (Fin.natAdd a j)) := by
  rw [← PureState.congr_symm_congr (QSystem.tensorPowAdd S a b) (PureState.piTensor f),
    QSystem.tensorPowAdd_congr_piTensor a b f]
  exact Evolution.onBlock_evolvePure_congr G b _ _

end AxQM
