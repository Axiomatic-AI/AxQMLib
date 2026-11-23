/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GateTeleportation
import AxQM.Postulates.API.GateTeleportResourceExplicit

/-!
# AxQM.Postulates.API — the gate-teleportation protocol reshape

The **protocol register reshape** of Nielsen & Chuang **Problem 4.6** ("Universality with prior
entanglement") — the six-qubit regrouping that lays out the gate-teleportation register for the
two Bell measurements and the co-located `CNOT` output — together with the two operator-action
facts it consumes, and the key geometric identity they combine to give:
**the resource `CNOT`, transported through the protocol reshape, becomes a `CNOT` on the two
co-located teleported outputs.**

The statement of Problem 4.6 is in `AxQM/NC/Ch4/Problem4_6.lean`; compare the reshapes in
`AxQM/Postulates/API/Interchange.lean` and
`AxQM/Postulates/API/GateTeleportResourceExplicit.lean`.

## Role in Problem 4.6

Gate teleportation implements a `CNOT` (the missing two-qubit gate; single-qubit gates are shared)
from the resource set `{single-qubit unitaries, Bell-basis measurement, four-qubit state
preparation}`.  The two input qubits `q_A, q_B` are teleported through the four-qubit resource
`cnotGateTeleportResource` (`|χ⟩`, a `CNOT` pre-applied to the two *output* halves of two Bell
pairs); the two Bell measurements pair `(q_A, a_in)` and `(q_B, b_in)`, and — because the resource
`CNOT` acts on the output halves `a_out, b_out` — the teleported outputs come out `CNOT`-entangled.

The six qubits of the physical register `(q_A ⊗ q_B) ⊗ ((a_in ⊗ a_out) ⊗ (b_out ⊗ b_in))` are laid
out with the inputs together and the resource together; to read off the protocol they must be
regrouped so that (i) the two *measured* pairs `(q_A, a_in)` and `(q_B, b_in)` form the left block
and (ii) the two *output* halves `a_out, b_out` form the right factor on which the resource `CNOT`
acts.  That regrouping is `gateTeleportProtocolReshape`.  Because the resource `CNOT` sits on the
output halves, transporting it through this reshape turns it into a plain `CNOT` on the co-located
output factor — the fact `gateTeleportProtocolReshape_cnotOnOutputs_qubitBasis` records, on the
computational basis.

## What is formalised

* `gateTeleportProtocolReshape` — the reshape system isomorphism
  `(q ⊗ q) ⊗ ((q ⊗ q) ⊗ (q ⊗ q)) ≃ₛ ((q ⊗ q) ⊗ (q ⊗ q)) ⊗ (q ⊗ q)` sending
  `(q_A ⊗ q_B) ⊗ ((a_in ⊗ a_out) ⊗ (b_out ⊗ b_in))` to
  `((q_A ⊗ a_in) ⊗ (q_B ⊗ b_in)) ⊗ (a_out ⊗ b_out)`: measured pairs blocked on the left, teleported
  outputs co-located on the right.  Assembled from the interchange braid, the associator and the
  swap of the transport backbone.
* `gateTeleportProtocolReshape_toIsometry_tmul` — its pure-tensor action
  `(a ⊗ b) ⊗ ((c ⊗ d) ⊗ (e ⊗ f)) ↦ ((a ⊗ c) ⊗ (b ⊗ f)) ⊗ (d ⊗ e)`.
* `cnotOnOutputs_op_qubitBasis` — the **computational-basis action of the resource `CNOT`**
  `cnotOnOutputs.op ((|c⟩ ⊗ |d⟩) ⊗ (|e⟩ ⊗ |f⟩)) = (|c⟩ ⊗ |d⟩) ⊗ (|e ⊕ d⟩ ⊗ |f⟩)`: `CNOT` with
  control `a_out = d`, target `b_out = e`, identity on the input halves `a_in = c`, `b_in = f`.
  (The general-basis companion of `cnotGateTeleportResource_reshape_qubitBasis`, whose diagonal
  `c = d, e = f` case is the resource state's basis expansion.)
* `gateTeleportProtocolReshape_cnotOnOutputs_qubitBasis` — the **`CNOT`-onto-outputs geometry** on
  the computational basis:
  `reshape ((|a⟩ ⊗ |b⟩) ⊗ cnotOnOutputs.op resource)
  = (CNOT on the output factor) (reshape ((|a⟩ ⊗ |b⟩) ⊗ resource))`, i.e. the resource `CNOT` on
  `(a_out, b_out)` transports through the reshape to `cnotGate.onRight` on the co-located output
  factor `(a_out ⊗ b_out)`.

## Design notes

* **Why the reshape, and its build.**  `QSystem.assoc`/`QSystem.Iso.tmul` re-bracket but cannot
  swap adjacent factors; `QSystem.Iso.comm` swaps a bipartite composite; `QSystem.Iso.interchange`
  swaps the two *interior* factors of a fourfold composite.  The protocol reshape needs all three:
  `interchange` splits the physical register into the two teleportation lines
  `(q_A ⊗ (a_in ⊗ a_out)) ⊗ (q_B ⊗ (b_out ⊗ b_in))`, then per line the associator groups the
  measured pair and (for line `B`) `comm` first fixes the `(b_out, b_in)` ordering, and a final
  `interchange` blocks the two measured pairs together and the two outputs together.  Its
  pure-tensor action is the chain of the backbone `_tmul` action lemmas (`simp only`), exactly the
  idiom of `QSystem.interchangeBCAD_toIsometry_tmul`.
* **Basis, not arbitrary vectors, for the `CNOT`-onto-outputs identity.**  The transport of the
  resource `CNOT` onto the outputs is genuinely an operator conjugation on the six-qubit register;
  stated over *all* vectors it is an `Evolution` equality that would need a bespoke extensionality
  for the nested composite `((q ⊗ q) ⊗ (q ⊗ q)) ⊗ (q ⊗ q)` (no such `…_evolution_ext` exists — the
  library's are for `q ⊗ q`, `q ⊗ (q ⊗ q)`, `q ⊗ R`).  On the computational basis the identity is a
  direct chain of the two action lemmas here plus the `CNOT` truth table, needing no extensionality;
  since the teleportation-identity assembly expands the resource over the computational basis
  (`cnotGateTeleportResource_vec`) anyway, this basis form is exactly what it consumes.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-! ### The protocol register reshape -/

set_option maxHeartbeats 1000000 in
-- The type-check of this deeply nested composite of transport-backbone isos (two `interchange`
-- braids over composite systems, plus an inner `tmul`/`comm`/`assoc`) exceeds the default
-- heartbeat budget; the elaboration itself is pure `QSystem.Iso` data (no proof search).
/-- The **gate-teleportation protocol reshape**
`(q ⊗ q) ⊗ ((q ⊗ q) ⊗ (q ⊗ q)) ≃ₛ ((q ⊗ q) ⊗ (q ⊗ q)) ⊗ (q ⊗ q)`.  On the physical register
`(q_A ⊗ q_B) ⊗ ((a_in ⊗ a_out) ⊗ (b_out ⊗ b_in))` it produces
`((q_A ⊗ a_in) ⊗ (q_B ⊗ b_in)) ⊗ (a_out ⊗ b_out)`: the two Bell-measured pairs `(q_A, a_in)`,
`(q_B, b_in)` blocked on the left, the two teleported output halves `a_out, b_out` co-located on the
right (where the resource `CNOT` acts).  Built from the transport backbone only:
`QSystem.Iso.interchange` splits the register into the two teleportation lines
`(q_A ⊗ (a_in ⊗ a_out)) ⊗ (q_B ⊗ (b_out ⊗ b_in))`; per line `QSystem.assoc` groups the measured pair
(with `QSystem.Iso.comm` first swapping the `(b_out, b_in)` ordering on line `B`); a final
`QSystem.Iso.interchange` blocks the measured pairs and the outputs. -/
def gateTeleportProtocolReshape :
    ((qubit ⊗ qubit) ⊗ ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)))
      ≃ₛ (((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ qubit)) :=
  (QSystem.Iso.interchange qubit qubit (qubit ⊗ qubit) (qubit ⊗ qubit)).trans
    ((QSystem.Iso.tmul (QSystem.assoc qubit qubit qubit)
        ((QSystem.Iso.tmul (QSystem.Iso.refl qubit) (QSystem.Iso.comm qubit qubit)).trans
          (QSystem.assoc qubit qubit qubit))).trans
      (QSystem.Iso.interchange (qubit ⊗ qubit) qubit (qubit ⊗ qubit) qubit))

/-- **Pure-tensor action of the protocol reshape**:
`gateTeleportProtocolReshape ((a ⊗ b) ⊗ ((c ⊗ d) ⊗ (e ⊗ f))) = ((a ⊗ c) ⊗ (b ⊗ f)) ⊗ (d ⊗ e)`.
With the physical labels `a = q_A`, `b = q_B`, `c = a_in`, `d = a_out`, `e = b_out`, `f = b_in`, the
two measured pairs `(q_A, a_in) = (a, c)` and `(q_B, b_in) = (b, f)` block on the left and the two
output halves `(a_out, b_out) = (d, e)` co-locate on the right.  Proved by unfolding the reshape and
firing the outer `interchange` action lemma, after which the remaining backbone isos compute
definitionally on the pure tensor (`rfl`). -/
theorem gateTeleportProtocolReshape_toIsometry_tmul (a b c d e f : qubit.space) :
    gateTeleportProtocolReshape.toIsometry
        ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] ((c ⊗ₜ[ℂ] d) ⊗ₜ[ℂ] (e ⊗ₜ[ℂ] f)))
      = ((a ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] f)) ⊗ₜ[ℂ] (d ⊗ₜ[ℂ] e) := by
  simp only [gateTeleportProtocolReshape, QSystem.Iso.trans_toIsometry]
  rfl

/-! ### The resource `CNOT` on the computational basis, and its transport onto the outputs -/

/-- **`cnotOnOutputs` as the reshape conjugation.**  Unfolding the `Evolution.congr` transport,
`cnotOnOutputs.op x = gateTeleportReshape⁻¹ (cnotMiddleGate.op (gateTeleportReshape x))`: apply the
middle-qubit regrouping, the placed middle `CNOT`, then regroup back.  The operator form the
computational-basis action reads off. -/
theorem cnotOnOutputs_op_apply (x : ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space) :
    cnotOnOutputs.op x
      = gateTeleportReshape.symm.toIsometry
          (cnotMiddleGate.op (gateTeleportReshape.toIsometry x)) := by
  rw [cnotOnOutputs, Evolution.congr_op, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    QSystem.Iso.symm_toIsometry, LinearIsometryEquiv.symm_symm]

/-- **Computational-basis action of the resource `CNOT`** `cnotOnOutputs`
(`CNOT` on the two output halves `a_out, b_out` of the resource register `(a_in a_out) ⊗ (b_out
b_in)`): `cnotOnOutputs.op ((|c⟩ ⊗ |d⟩) ⊗ (|e⟩ ⊗ |f⟩)) = (|c⟩ ⊗ |d⟩) ⊗ (|e ⊕ d⟩ ⊗ |f⟩)`, i.e.
control `a_out = d`, target `b_out = e ↦ e ⊕ d`, identity on the input halves `a_in = c`,
`b_in = f`.  The general-basis companion of `cnotGateTeleportResource_reshape_qubitBasis` (which is
its diagonal `c = d`, `e = f` case).  Proved from `cnotOnOutputs_op_apply` and the reshape /
middle-`CNOT` / `CNOT`-truth-table action lemmas. -/
theorem cnotOnOutputs_op_qubitBasis (c d e f : Fin 2) :
    cnotOnOutputs.op (((qubitBasis c).vec ⊗ₜ[ℂ] (qubitBasis d).vec) ⊗ₜ[ℂ]
        ((qubitBasis e).vec ⊗ₜ[ℂ] (qubitBasis f).vec))
      = ((qubitBasis c).vec ⊗ₜ[ℂ] (qubitBasis d).vec) ⊗ₜ[ℂ]
          ((qubitBasis (e + d)).vec ⊗ₜ[ℂ] (qubitBasis f).vec) := by
  -- `have`-instantiate at the concrete tensor (rather than `rw`) so the compose-space instance
  -- diamond on `((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space` gets crossed by full elaboration.
  have hop := cnotOnOutputs_op_apply (((qubitBasis c).vec ⊗ₜ[ℂ] (qubitBasis d).vec) ⊗ₜ[ℂ]
    ((qubitBasis e).vec ⊗ₜ[ℂ] (qubitBasis f).vec))
  -- keep the reshape symbolic in the goal; reduce it inside `hmid` (matching the
  -- reshape-produced tensor head avoids the composite-space instance diamond).
  have hmid : cnotMiddleGate.op (gateTeleportReshape.toIsometry
        (((qubitBasis c).vec ⊗ₜ[ℂ] (qubitBasis d).vec) ⊗ₜ[ℂ]
          ((qubitBasis e).vec ⊗ₜ[ℂ] (qubitBasis f).vec)))
      = (qubitBasis c).vec ⊗ₜ[ℂ]
          (((qubitBasis d).vec ⊗ₜ[ℂ] (qubitBasis (e + d)).vec) ⊗ₜ[ℂ] (qubitBasis f).vec) := by
    rw [gateTeleportReshape_toIsometry_tmul_tmul]
    refine (cnotMiddleGate_op_tmul (qubitBasis c).vec (qubitBasis f).vec
      ((qubitBasis d).vec ⊗ₜ[ℂ] (qubitBasis e).vec)).trans ?_
    rw [cnotGate_op_qubitBasisVec_tmul]
    rfl
  rw [hop, hmid]
  exact gateTeleportReshape_symm_toIsometry_tmul_tmul (qubitBasis c).vec (qubitBasis d).vec
    (qubitBasis (e + d)).vec (qubitBasis f).vec

/-- **The resource `CNOT` transports through the protocol reshape to a `CNOT` on the co-located
outputs**, on the computational basis (Nielsen & Chuang Problem 4.6).  For all computational-basis
labels,
`gateTeleportProtocolReshape ((|a⟩ ⊗ |b⟩) ⊗ cnotOnOutputs.op ((|c⟩ ⊗ |d⟩) ⊗ (|e⟩ ⊗ |f⟩)))
= (cnotGate.onRight _) (gateTeleportProtocolReshape ((|a⟩ ⊗ |b⟩) ⊗ ((|c⟩ ⊗ |d⟩) ⊗ (|e⟩ ⊗ |f⟩))))`:
applying the resource `CNOT` (on the output halves `a_out, b_out`) *before* the reshape equals
applying `cnotGate` to the right (output) factor `(a_out ⊗ b_out)` *after* the reshape.  This is the
geometric heart of gate teleportation — the pre-applied resource `CNOT` acts on exactly the two
qubits that carry the teleported result — recorded on the basis (the assembly expands the resource
over the basis, so no operator extensionality is needed).  Both sides reduce, via the reshape and
resource-`CNOT` action lemmas and the `CNOT` truth table, to
`((|a⟩ ⊗ |c⟩) ⊗ (|b⟩ ⊗ |f⟩)) ⊗ (|d⟩ ⊗ |e ⊕ d⟩)`. -/
theorem gateTeleportProtocolReshape_cnotOnOutputs_qubitBasis (a b c d e f : Fin 2) :
    gateTeleportProtocolReshape.toIsometry
        (((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec) ⊗ₜ[ℂ]
          cnotOnOutputs.op (((qubitBasis c).vec ⊗ₜ[ℂ] (qubitBasis d).vec) ⊗ₜ[ℂ]
            ((qubitBasis e).vec ⊗ₜ[ℂ] (qubitBasis f).vec)))
      = (cnotGate.onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).op
          (gateTeleportProtocolReshape.toIsometry
            (((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec) ⊗ₜ[ℂ]
              (((qubitBasis c).vec ⊗ₜ[ℂ] (qubitBasis d).vec) ⊗ₜ[ℂ]
                ((qubitBasis e).vec ⊗ₜ[ℂ] (qubitBasis f).vec)))) := by
  -- both sides reduce to the common value `((|a⟩⊗|c⟩)⊗(|b⟩⊗|f⟩))⊗(|d⟩⊗|e⊕d⟩)`; `exact` bridges
  -- the composite-space instance diamond on the reshape/`CNOT`-produced tensors.
  have hL : gateTeleportProtocolReshape.toIsometry
        (((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec) ⊗ₜ[ℂ]
          cnotOnOutputs.op (((qubitBasis c).vec ⊗ₜ[ℂ] (qubitBasis d).vec) ⊗ₜ[ℂ]
            ((qubitBasis e).vec ⊗ₜ[ℂ] (qubitBasis f).vec)))
      = ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis c).vec) ⊗ₜ[ℂ]
            ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis f).vec) ⊗ₜ[ℂ]
          ((qubitBasis d).vec ⊗ₜ[ℂ] (qubitBasis (e + d)).vec) := by
    rw [cnotOnOutputs_op_qubitBasis]
    exact gateTeleportProtocolReshape_toIsometry_tmul (qubitBasis a).vec (qubitBasis b).vec
      (qubitBasis c).vec (qubitBasis d).vec (qubitBasis (e + d)).vec (qubitBasis f).vec
  have hR : (cnotGate.onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).op
        (gateTeleportProtocolReshape.toIsometry
          (((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec) ⊗ₜ[ℂ]
            (((qubitBasis c).vec ⊗ₜ[ℂ] (qubitBasis d).vec) ⊗ₜ[ℂ]
              ((qubitBasis e).vec ⊗ₜ[ℂ] (qubitBasis f).vec))))
      = ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis c).vec) ⊗ₜ[ℂ]
            ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis f).vec) ⊗ₜ[ℂ]
          ((qubitBasis d).vec ⊗ₜ[ℂ] (qubitBasis (e + d)).vec) := by
    rw [gateTeleportProtocolReshape_toIsometry_tmul]
    refine (Evolution.onRight_op_tmul cnotGate ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))
      ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis c).vec ⊗ₜ[ℂ]
        ((qubitBasis b).vec ⊗ₜ[ℂ] (qubitBasis f).vec))
      ((qubitBasis d).vec ⊗ₜ[ℂ] (qubitBasis e).vec)).trans ?_
    rw [cnotGate_op_qubitBasisVec_tmul]
    rfl
  exact hL.trans hR.symm

end AxQM
