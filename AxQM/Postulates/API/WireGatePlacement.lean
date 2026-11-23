/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BlockGatePlacement
import AxQM.Postulates.API.WirePermutation
import AxQM.Postulates.API.Qubit

/-!
# Placing a gate on an arbitrary set of wires (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit implementing
`Cⁿ(X)`. Bottoming the multiply-controlled-`NOT` blocks of the tight `(n+1)`-wire circuit to
genuine two-control gates (`Toffoli`/`CNOT`/`NOT`) requires placing such a gate on a **chosen,
non-contiguous set of wires** of the register. This file combines `Evolution.onBlock` and
`Evolution.permWires` into a general arbitrary-wire placement gate.

The two combinators do half the job each:

* `Evolution.onBlock G b` places a gate `G : Evolution (S ^⊗ₛ a)` on the **first** `a` wires of
  `S ^⊗ₛ (a+b)` (a contiguous block at the front);
* `Evolution.permWires σ` **relabels** the wires by a permutation `σ : Equiv.Perm (Fin (a+b))`.

Conjugating the front-block gate by a wire permutation moves the block to any chosen wire set:
`Evolution.onWires G b σ := permWires σ ∘ onBlock G b ∘ permWires σ⁻¹` places `G` on exactly the
wires `σ 0, …, σ (a-1)` (the image of the front block under `σ`), leaving the rest untouched. This
is the construction "conjugate a contiguous gate by the wire permutation that gathers the chosen
wires".

## What is formalised

* `QSystem.tensorPowAdd_symm_tmul_piTensor` — the **block-reassembly dictionary**: the *inverse*
  block-split isomorphism carries a pair of block product states `(⨂ᵢ |p i⟩) ⊗ (⨂ⱼ |q j⟩)` back
  to the single product `⨂ₖ |(Fin.append p q) k⟩` on `S ^⊗ₛ (a+b)`. The fold that turns
  `Evolution.onBlock`'s split output back into a product state so a further wire permutation can
  act on it (the reverse of `QSystem.tensorPowAdd_congr_piTensor`).
* `Evolution.onWires G b σ` — the **arbitrary-wire placement gate** on `S ^⊗ₛ (a+b)`: the gate `G`
  placed on the wires `σ 0, …, σ (a-1)`, built by conjugating `Evolution.onBlock G b` by
  `Evolution.permWires σ`.
* `Evolution.onWires_evolvePure_qubitBasis` — its **computational-basis truth table for a classical
  gate** on the qubit register `qubit ^⊗ₛ (a+b)`. When `G` is *classical* — it permutes the
  computational basis, `G (⨂ᵢ |c i⟩) = ⨂ᵢ |γ c i⟩` for a classical bit-string action
  `γ : (Fin a → Fin 2) → (Fin a → Fin 2)` (the case of a `Toffoli`/`CNOT`/`NOT`) — then
  `Evolution.onWires G b σ` applies `γ` to the bits carried on the target wires
  `σ (Fin.castAdd b ·)` and leaves the other wires unchanged, read back in the original wire layout
  via `σ⁻¹`. This is the wire-addressed truth table for the `Cᵏ(X)`-block `Toffoli` reduction.

## Design notes

* **Why a computational-basis (not all-product-states) hypothesis.** A general gate `G` may
  entangle, so `onWires G b σ` need not map an arbitrary product input to a product output — there
  is no closed-form product action for superposition inputs. Crucially, a computational-basis
  *permutation* is **not** the same as a product-preserving map: `Toffoli`/`CNOT` map every
  computational-basis product to a computational-basis product, yet they **entangle** superposition
  products (e.g. `CNOT |+⟩|0⟩ = (|00⟩+|11⟩)/√2`). So the correct, satisfiable hypothesis for the
  `Toffoli`/`CNOT`/`NOT` gates the exercise places is basis-preservation on the `Fin 2`-indexed
  computational basis (`hG` below), *not* preservation of every product pure state. Under it every
  step of the conjugation keeps a computational-basis product a computational-basis product, giving
  a clean bit-string truth table. Keeping `γ` an arbitrary bit-string function makes the lemma
  reusable for every classical block gate.
* **Why conjugation, reusing existing dictionaries — not fresh `reindex` surgery.**
  `Evolution.permWires`/`Evolution.onBlock` already come with their computational-basis
  actions; conjugating reuses them (via the pre-existing `Evolution.evolvePure_comp`) and the group
  law `Evolution.permWires` satisfies, keeping every step a one-line application of an existing
  dictionary plus the reassembly fold. The inner permutation is written `σ.symm` (`= σ⁻¹` in
  `Equiv.Perm`) so `permWires σ.symm` contributes `σ.symm.symm = σ` with a single `Equiv.symm_symm`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem} {a : ℕ}

/-- **Block-reassembly dictionary for the inverse block isomorphism.** The inverse block-split
isomorphism `(QSystem.tensorPowAdd S a b).symm` carries a pair of block product states
`(⨂ᵢ |p i⟩) ⊗ (⨂ⱼ |q j⟩)` — the first `a` wires and the last `b` — back to the single product
state `⨂ₖ |(Fin.append p q) k⟩` on `S ^⊗ₛ (a+b)`. The reverse of
`QSystem.tensorPowAdd_congr_piTensor`, used to fold `Evolution.onBlock`'s split output back into a
product state so a further wire permutation can act on it. -/
theorem QSystem.tensorPowAdd_symm_tmul_piTensor (a b : ℕ)
    (p : Fin a → PureState S) (q : Fin b → PureState S) :
    PureState.congr (QSystem.tensorPowAdd S a b).symm
        (PureState.piTensor p ⊗ PureState.piTensor q)
      = PureState.piTensor (Fin.append p q) := by
  rw [← PureState.congr_symm_congr (QSystem.tensorPowAdd S a b)
      (PureState.piTensor (Fin.append p q)),
    QSystem.tensorPowAdd_congr_piTensor a b (Fin.append p q)]
  congr 2 <;> simp only [Fin.append_left, Fin.append_right] <;> rfl

/-- **The arbitrary-wire placement gate** on `S ^⊗ₛ (a+b)`: given a gate `G : Evolution (S ^⊗ₛ a)`
and a wire permutation `σ : Equiv.Perm (Fin (a+b))`, the closed-system `Evolution` that acts as `G`
on the wire set `σ 0, …, σ (a-1)` (the image of the front `a`-wire block under `σ`) and as the
identity on the remaining wires. It is the front-block gate `Evolution.onBlock G b` conjugated by
the wire permutation `Evolution.permWires σ` — relabel the target wires to the front, run `G`
there, then relabel back. Its computational-basis truth table for a classical `G` is
`Evolution.onWires_evolvePure_qubitBasis`. -/
def Evolution.onWires (G : Evolution (S ^⊗ₛ a)) (b : ℕ) (σ : Equiv.Perm (Fin (a + b))) :
    Evolution (S ^⊗ₛ (a + b)) :=
  (Evolution.permWires σ).comp ((G.onBlock b).comp (Evolution.permWires σ.symm))

/-- **The identity wire permutation places a gate on the front block.** Conjugating by the identity
permutation is trivial, so arbitrary-wire placement `Evolution.onWires` degenerates to the
contiguous front-block placement `Evolution.onBlock`: `G.onWires b 1 = G.onBlock b`. Both
conjugating factors `Evolution.permWires 1` are the identity evolution
(`Evolution.permWires_one`, using `Equiv.Perm.one_symm` for the inner `σ.symm`), and composing with
the identity is a no-op (`Evolution.id_comp`, `Evolution.comp_id`). The special case in which the
chosen wires already are the front `a`-wire block — used to read off the block-embedded form of a
gate placed on contiguous wires. -/
theorem Evolution.onWires_one (G : Evolution (S ^⊗ₛ a)) (b : ℕ) :
    G.onWires b (1 : Equiv.Perm (Fin (a + b))) = G.onBlock b := by
  rw [Evolution.onWires, ← Equiv.Perm.inv_def 1, inv_one, Evolution.permWires_one,
      Evolution.id_comp,
    Evolution.comp_id]

/-- **Computational-basis truth table of the arbitrary-wire placement gate for a classical gate.**
Let `G : Evolution (qubit ^⊗ₛ a)` be *classical*: it permutes the computational basis,
`G (⨂ᵢ |c i⟩) = ⨂ᵢ |γ c i⟩` for a classical bit-string action
`γ : (Fin a → Fin 2) → (Fin a → Fin 2)` (the case of a `Toffoli`/`CNOT`/`NOT`, which map every
computational-basis product to a computational-basis product — unlike an arbitrary product state,
which they may entangle). Then on the computational-basis input `⨂ₖ |c k⟩`,
`Evolution.onWires G b σ` applies `γ` to the bits `c` carries on the target wires
`σ (Fin.castAdd b ·)` and leaves the other wires' bits unchanged, the whole read back in the
original wire layout by `σ⁻¹`:
`onWires G b σ (⨂ₖ |c k⟩) = ⨂ₖ |Fin.append (γ (c ∘ σ ∘ castAdd)) (c ∘ σ ∘ natAdd) (σ⁻¹ k)⟩`.
The wire-addressed truth table the `Cᵏ(X)`-block `Toffoli` reduction consumes. Proved by evaluating
the conjugation `permWires σ ∘ onBlock G b ∘ permWires σ⁻¹` step by step
(`Evolution.evolvePure_comp`), each step carrying a computational-basis product to a
computational-basis product via the dictionary lemmas, and pulling `qubitBasis` through the final
`Fin.append`. -/
theorem Evolution.onWires_evolvePure_qubitBasis {a : ℕ} (G : Evolution (qubit ^⊗ₛ a)) (b : ℕ)
    (σ : Equiv.Perm (Fin (a + b)))
    (γ : (Fin a → Fin 2) → (Fin a → Fin 2))
    (hG : ∀ c : Fin a → Fin 2,
      G.evolvePure (PureState.piTensor fun i => qubitBasis (c i))
        = PureState.piTensor fun i => qubitBasis (γ c i))
    (c : Fin (a + b) → Fin 2) :
    (G.onWires b σ).evolvePure (PureState.piTensor fun i => qubitBasis (c i))
      = PureState.piTensor fun i =>
          qubitBasis (Fin.append (γ fun j => c (σ (Fin.castAdd b j)))
            (fun j => c (σ (Fin.natAdd a j))) (σ.symm i)) := by
  -- `Fin.append` of two `qubitBasis` families is the `qubitBasis` of the appended bit-strings.
  have happ : ∀ (u : Fin a → Fin 2) (w : Fin b → Fin 2),
      (Fin.append (fun i => qubitBasis (u i)) fun j => qubitBasis (w j))
        = fun k => qubitBasis (Fin.append u w k) := by
    intro u w
    funext k
    induction k using Fin.addCases with
    | left i => simp only [Fin.append_left]
    | right j => simp only [Fin.append_right]
  let ψ0 : PureState (qubit ^⊗ₛ (a + b)) := PureState.piTensor fun i => qubitBasis (c i)
  change (G.onWires b σ).evolvePure ψ0 = _
  rw [Evolution.onWires, Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    Evolution.permWires_evolvePure_piTensor]
  simp only [Equiv.symm_symm]
  rw [Evolution.onBlock_evolvePure_piTensor, hG, QSystem.tensorPowAdd_symm_tmul_piTensor,
    Evolution.permWires_evolvePure_piTensor, happ]

end AxQM
