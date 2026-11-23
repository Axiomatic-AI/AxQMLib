/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.TensorPowMultiControlledX
import AxQM.Core.EvolutionQubitBasisExt
import AxQM.Postulates.API.WireGatePlacement

/-!
# Placing `Cᵏ(X)` on a chosen set of wires (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The recursive Barenco construction (Exercise
4.30's `barencoNCircuit`, and the classical halving circuit of `Concrete/MultiControlledNot*`)
bottoms out into a sequence of multiply-controlled `NOT` blocks `Cᵏ(X)` (`k ≤ 2` are exactly the
`Toffoli`/`CNOT`/`NOT` gates), **each acting on a chosen, non-contiguous set of `k + 1` wires** of
the register. This file turns such a block into a genuine closed-system `Evolution`.

Two earlier constructions provide the two halves:

* `Evolution.tensorPowMcCtrlX k : Evolution (qubit ^⊗ₛ (k+1))` — the grounded `Cᵏ(X)`
  transported onto the symmetric power, with computational-basis action
  `tensorPowMcCtrlX_evolvePure_piTensor` equal to the classical `Concrete.mcNot (cnxControls k)
  (Fin.last k)`;
* `Evolution.onWires G b σ` — placing a gate `G : Evolution (qubit ^⊗ₛ a)` on the wire
  set `σ '' (front a wires)` of `qubit ^⊗ₛ (a+b)`, with the computational-basis truth table
  `Evolution.onWires_evolvePure_qubitBasis` for a classical `G`.

Feeding the classical `Cᵏ(X)` gate into the placement combinator realises `Cᵏ(X)` on any chosen
wires; reading off its truth table is the wire-addressed multiply-controlled `NOT` the circuit
assembly composes.

## What is formalised

* `Evolution.placedMcCtrlX k b σ` — the `Cᵏ(X)` gate (`k` controls, one target = `k + 1` wires)
  placed on the `(k+1)`-wire set `σ 0, …, σ k` of the `(k+1+b)`-wire register `qubit ^⊗ₛ (k+1+b)`,
  built as `(Evolution.tensorPowMcCtrlX k).onWires b σ`. A genuine closed-system `Evolution` on the
  whole register — no work qubit beyond the `b` ambient wires it acts on as identity.
* `placedMcCtrlX_evolvePure_qubitBasis` — its **computational-basis truth table**: it acts on the
  product basis `⨂ₖ |c k⟩` exactly as the classical multiply-controlled `NOT`
  `Concrete.mcNot Cσ tσ` whose controls `Cσ = (cnxControls k).image (σ ∘ Fin.castAdd b)` are the
  images of the `k` front control wires and whose target `tσ = σ (Fin.castAdd b (Fin.last k))` is
  the image of the front target wire. So the placed quantum `Cᵏ(X)` **is** the reversible bit-string
  permutation that flips wire `tσ` iff every control wire in `Cσ` is set — the wire-addressed
  `Toffoli`/`CNOT`/`NOT` truth table the assembly uses.

The wire assignment is carried by the permutation `σ`, an explicit input; choosing `σ` to gather a
prescribed control set `C` and target `t` onto the front block (so `Cσ = C`, `tσ = t`) is a
`Finset`-level construction that is not carried out in this file.

Two further facts specialise the placement to the case in which the target wires already are the
leading `k + 1` wires (the shape a Barenco `Cᵏ(X)` block takes once the control tower is flattened):

* `Evolution.placedMcCtrlX_one` — at the identity permutation the placement is the block embedding
  `(Evolution.tensorPowMcCtrlX k).onBlock b` (`Evolution.onWires_one`);
* `tensorPowMcCtrlX_onBlock_evolvePure_qubitBasis` — its computational-basis truth table, flipping
  the front target wire `Fin.castAdd b (Fin.last k)` iff the front controls
  `(cnxControls k).image (Fin.castAdd b)` are all set.

## Design notes

* **Why `σ`-parametrised, not `(C, t)`-parametrised.** `Evolution.onWires` already takes the wire
  permutation as input, and its truth table `onWires_evolvePure_qubitBasis` is stated over that
  permutation. Reading the placed gate's controls/target *off* `σ` (as `Cσ`/`tσ`) keeps this a
  one-step specialisation of the placement dictionary, with no `Finset`→permutation
  construction; the reverse direction — build `σ` realising a *given* `(C, t)` — is a separate
  combinatorial step (order-isos of `C ∪ {t}` and its complement) belonging to the assembly, where
  the wires are concretely given.
* **The truth-table proof.** `onWires_evolvePure_qubitBasis` (with `γ = mcNot (cnxControls k)
  (Fin.last k)` and `hG = tensorPowMcCtrlX_evolvePure_piTensor k`) rewrites the placed gate's action
  to `⨂ₖ |Fin.append (γ (c ∘ σ ∘ castAdd)) (c ∘ σ ∘ natAdd) (σ⁻¹ k)⟩`. Substituting `k = σ p` and
  casing `p` over `Fin.addCases`: on the front target wire (`p = castAdd (Fin.last k)`) both sides
  flip by the same control bit — the classical `ctrlBit` matches through the relabelling by
  `Concrete.ctrlBit_image`; on a front control wire (`p = castAdd j`, `j ≠ last`) and on an ambient
  wire (`p = natAdd j`) neither side touches the bit (`mcNot_apply_of_ne`, the two wires distinct
  from `tσ` by injectivity of `σ` and `Fin.castAdd`, and `natAdd ≠ castAdd`).
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **`Cᵏ(X)` placed on a chosen set of wires.** Given a wire permutation
`σ : Equiv.Perm (Fin (k + 1 + b))`, the multiply-controlled `NOT` `Cᵏ(X)` (`k` controls, one target,
so `k + 1` wires) placed on the wire set `σ 0, …, σ k` of the `(k+1+b)`-wire register
`qubit ^⊗ₛ (k+1+b)`, built by placing the symmetric-register `Cᵏ(X)` gate
`Evolution.tensorPowMcCtrlX k` via the arbitrary-wire combinator `Evolution.onWires`. A genuine
closed-system `Evolution` acting as `Cᵏ(X)` on its `k + 1` target wires and as the identity on the
other `b`. For `k ≤ 2` this is a `Toffoli`/`CNOT`/`NOT` addressed to arbitrary wires; its
computational-basis truth table is `placedMcCtrlX_evolvePure_qubitBasis`. -/
def Evolution.placedMcCtrlX (k b : ℕ) (σ : Equiv.Perm (Fin (k + 1 + b))) :
    Evolution (qubit ^⊗ₛ (k + 1 + b)) :=
  (Evolution.tensorPowMcCtrlX k).onWires b σ

/-- Definitional unfolding of `Evolution.placedMcCtrlX` as the placed symmetric-register `Cᵏ(X)`. -/
theorem Evolution.placedMcCtrlX_def (k b : ℕ) (σ : Equiv.Perm (Fin (k + 1 + b))) :
    Evolution.placedMcCtrlX k b σ = (Evolution.tensorPowMcCtrlX k).onWires b σ :=
  rfl

/-- **Computational-basis truth table of the placed `Cᵏ(X)`.** The gate `Evolution.placedMcCtrlX k b
σ` acts on the computational product basis state `⨂ₖ |c k⟩` exactly as the classical
multiply-controlled `NOT` `Concrete.mcNot Cσ tσ`, whose controls
`Cσ = (cnxControls k).image (fun j => σ (Fin.castAdd b j))` are the wires the `k` front
controls are relabelled to, and whose target `tσ = σ (Fin.castAdd b (Fin.last k))` is the wire the
front target is relabelled to:
`placedMcCtrlX k b σ (⨂ₖ |c k⟩) = ⨂ₖ |mcNot Cσ tσ c k⟩`.

So the placed quantum `Cᵏ(X)` **is** the reversible bit-string permutation that flips wire `tσ` iff
every wire in `Cσ` is set — the wire-addressed `Toffoli`/`CNOT`/`NOT` truth table the `O(n²)`
circuit assembly composes. Proved from the placement dictionary
`Evolution.onWires_evolvePure_qubitBasis` with classical action
`Concrete.mcNot (cnxControls k) (Fin.last k)` supplied by the symmetric-register truth table
`tensorPowMcCtrlX_evolvePure_piTensor`, then a wire-by-wire comparison over
`Fin.addCases`. -/
theorem placedMcCtrlX_evolvePure_qubitBasis (k b : ℕ) (σ : Equiv.Perm (Fin (k + 1 + b)))
    (c : Fin (k + 1 + b) → Fin 2) :
    (Evolution.placedMcCtrlX k b σ).evolvePure (PureState.piTensor fun i => qubitBasis (c i))
      = PureState.piTensor fun i =>
          qubitBasis (Concrete.mcNot ((cnxControls k).image fun j => σ (Fin.castAdd b j))
            (σ (Fin.castAdd b (Fin.last k))) c i) := by
  rw [Evolution.placedMcCtrlX_def,
    Evolution.onWires_evolvePure_qubitBasis (Evolution.tensorPowMcCtrlX k) b σ
      (Concrete.mcNot (cnxControls k) (Fin.last k))
      (tensorPowMcCtrlX_evolvePure_piTensor k) c]
  refine congrArg PureState.piTensor ?_
  funext i
  refine congrArg qubitBasis ?_
  obtain ⟨p, rfl⟩ : ∃ p, i = σ p := ⟨σ.symm i, (σ.apply_symm_apply i).symm⟩
  rw [Equiv.symm_apply_apply]
  induction p using Fin.addCases with
  | left j =>
    rw [Fin.append_left]
    by_cases hj : j = Fin.last k
    · subst hj
      simp only [Concrete.mcNot_apply_self, Concrete.ctrlBit_image]
    · have hne : σ (Fin.castAdd b j) ≠ σ (Fin.castAdd b (Fin.last k)) :=
        fun h => hj (Fin.castAdd_injective _ _ (σ.injective h))
      rw [Concrete.mcNot_apply_of_ne _ _ _ hj,
        Concrete.mcNot_apply_of_ne _ _ _ hne]
  | right j =>
    rw [Fin.append_right]
    have hne : σ (Fin.natAdd (k + 1) j) ≠ σ (Fin.castAdd b (Fin.last k)) := by
      apply σ.injective.ne
      simp [Fin.ext_iff]; omega
    rw [Concrete.mcNot_apply_of_ne _ _ _ hne]

/-- **The placed `Cᵏ(X)` gate depends only on its wire data `(Cσ, tσ)`.** If two wire permutations
`σ, τ : Equiv.Perm (Fin (k + 1 + b))` gather the `k` front control wires onto the same control set
(`Cσ = (cnxControls k).image (σ ∘ Fin.castAdd b)`) and the front target wire onto the same target
(`tσ = σ (Fin.castAdd b (Fin.last k))`), then the placement gates `Evolution.placedMcCtrlX k b σ`
and `Evolution.placedMcCtrlX k b τ` are **equal**.

This turns the wire-data reading of `placedMcCtrlX_evolvePure_qubitBasis` into a genuine `Evolution`
identity via the computational-basis extensionality `Evolution.ext_qubitBasis`: both gates are
classical (basis-permuting) and their truth tables `mcNot Cσ tσ` / `mcNot Cτ tτ` coincide under the
hypotheses, so agreement on every basis state forces the gates equal. It certifies that the placed
`Cᵏ(X)` is well-defined as a function of the *abstract* control set and target wire — not of the
particular gathering permutation — which is exactly what the circuit-assembly stage relies on when
it constructs a `σ` realising a prescribed `(C, t)` (the design note of `placedMcCtrlX`). -/
theorem Evolution.placedMcCtrlX_congr {k b : ℕ} {σ τ : Equiv.Perm (Fin (k + 1 + b))}
    (hC : ((cnxControls k).image fun j => σ (Fin.castAdd b j))
        = (cnxControls k).image fun j => τ (Fin.castAdd b j))
    (ht : σ (Fin.castAdd b (Fin.last k)) = τ (Fin.castAdd b (Fin.last k))) :
    Evolution.placedMcCtrlX k b σ = Evolution.placedMcCtrlX k b τ := by
  refine Evolution.ext_qubitBasis fun c => ?_
  rw [placedMcCtrlX_evolvePure_qubitBasis, placedMcCtrlX_evolvePure_qubitBasis, hC, ht]

/-- **`Cᵏ(X)` placed by the identity permutation is the contiguous front-block gate.** With the
identity wire permutation the `k + 1` target wires stay the front block, so the placement
`Evolution.placedMcCtrlX` degenerates to the block-embedded symmetric-register `Cᵏ(X)`:
`Evolution.placedMcCtrlX k b 1 = (Evolution.tensorPowMcCtrlX k).onBlock b`. Immediate from
`Evolution.onWires_one`. This is the shape a `Cᵏ(X)` block whose controls-and-target *already* are
the leading `k + 1` wires takes — for instance the multiply-controlled `NOT` blocks
`mcCtrl k (pauliXGate.onLeft M)` of the Barenco reduction (Exercise 4.30's `barencoNCircuit`), whose
controls are the outer tower wires and whose idle target-module `M` is the inner block. -/
theorem Evolution.placedMcCtrlX_one (k b : ℕ) :
    Evolution.placedMcCtrlX k b 1 = (Evolution.tensorPowMcCtrlX k).onBlock b := by
  rw [Evolution.placedMcCtrlX_def, Evolution.onWires_one]

/-- **Computational-basis truth table of the block-embedded `Cᵏ(X)`.** The contiguous front-block
placement `(Evolution.tensorPowMcCtrlX k).onBlock b` on `qubit ^⊗ₛ (k+1+b)` acts on the product
basis state `⨂ₖ |c k⟩` exactly as the classical multiply-controlled `NOT` flipping the front target
wire `Fin.castAdd b (Fin.last k)` iff every front control wire — the set
`(cnxControls k).image (Fin.castAdd b)` — is set:
`onBlock b (⨂ₖ |c k⟩) = ⨂ₖ |mcNot ((cnxControls k).image (castAdd b)) (castAdd b (last k)) c k⟩`.
The special case of `placedMcCtrlX_evolvePure_qubitBasis` at the identity permutation
(`placedMcCtrlX_one`), where the wire images `σ ∘ Fin.castAdd b` collapse to `Fin.castAdd b`. -/
theorem tensorPowMcCtrlX_onBlock_evolvePure_qubitBasis (k b : ℕ) (c : Fin (k + 1 + b) → Fin 2) :
    ((Evolution.tensorPowMcCtrlX k).onBlock b).evolvePure
        (PureState.piTensor fun i => qubitBasis (c i))
      = PureState.piTensor fun i =>
          qubitBasis (Concrete.mcNot ((cnxControls k).image (Fin.castAdd b))
            (Fin.castAdd b (Fin.last k)) c i) := by
  rw [← Evolution.placedMcCtrlX_one, placedMcCtrlX_evolvePure_qubitBasis]
  simp only [Equiv.Perm.coe_one, id_eq]
  rfl

end AxQM
