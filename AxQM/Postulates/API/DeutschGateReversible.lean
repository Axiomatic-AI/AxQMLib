/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DeutschGatePhaseGate

/-!
# AxQM.Postulates.API — the reversible gates `CNOT` and `Toffoli` from the Deutsch gate

The *universality* half of Nielsen & Chuang, Exercise 4.44 — the
**reversible (permutation) gates**. Universality via the §4.5 assembly needs, besides a dense family
of single-qubit gates on each wire, the reversible gates `CNOT` and `Toffoli` (the
decomposition of an arbitrary unitary is a product of Toffoli/`CNOT`/`NOT` and single-qubit gates,
`Concrete.exists_isToffoliOrSingleQubit_list_prod_eq`). This file shows the Deutsch gate
`G = C²(iR_x(πα))` **densely reaches both** when `α` is irrational.

## The mechanism

The analytic core is the `i`-coset density `Concrete.iScaledRotX_mem_closure_cyclic_iRx`: every
phased `x`-rotation `i · R_x(β)` lies in the closure of the Deutsch orbit `⟨iR_x(πα)⟩`. At `β = π`
this is
the **Pauli `X`**, since `i · R_x(π) = i · (-iX) = X` (`Concrete.pauliX_mem_closure_cyclic_iRx`). So
`X` — although `iR_x(πα)` never *equals* it for irrational `α` (that needs the rational value
`α = 1`, `deutschGate_one_eq_toffoliGate`) — is a genuine *closure limit* of the Deutsch target's
iterates. Applying the (continuous) controlled embeddings then lifts this to the physics gates:

* the **once**-controlled `C(X) = CNOT` lies in the closure of the once-controlled iterates
  `deutschControlledReachableOps` (the control–target pair of `C(iR_x(πα))`);
* the **doubly**-controlled `C²(X) = Toffoli` lies in the closure of the doubly-controlled iterates
  `deutschReachableOps` (the Deutsch gate `G` itself).

This says that `G` densely reaches Toffoli (hence `CNOT`), the reversible-gate input of the
universality argument. Both proofs are the exact continuity transport already used for
the `x`-rotation density lift and the phase-gate `S` extraction, with the reachable concrete target
`R_x(β)` / `i · I` replaced by the Pauli `X`.

## Design notes

* **Fidelity.** The hypothesis is exactly `Irrational α`. `CNOT`/`Toffoli` are genuine *closure*
  limits (no iterate equals them: an exact iterate `iⁿ R_x(nπα)` equal to `X = i · R_x(π)` needs
  `iⁿ = i` and `nπα ≡ π (mod 2π)`, i.e. `nα ≡ 1 (mod 2)` with `n ≡ 1 (mod 4)`, impossible for
  irrational `α` and `n ≠ 0`). Nothing is weakened.
* **Statement form.** The gates are written in their unfolded
  `controlledUnitary`/`ccontrolledUnitary pauliXGate` forms (definitionally the two named gates).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **`CNOT` is densely reachable from the once-controlled Deutsch gate (Nielsen & Chuang,
Exercise 4.44).** When `α` is irrational, the `CNOT` gate `C(X)` lies in the closure of the
once-controlled Deutsch gate's iterates `deutschControlledReachableOps α`: iterating `C(iR_x(πα))`
approximates `CNOT` to arbitrary accuracy.

The counterpart of `Concrete.pauliX_mem_closure_cyclic_iRx` (`X ∈ closure ⟨iR_x(πα)⟩`,
`X = i · R_x(π)`): the controlled embedding `controlledOp ∘ Matrix.toEuclideanCLM` is continuous, so
it carries the matrix closure into the operator closure
(`image_closure_subset_closure_image`), sending the concrete orbit onto the reachable set
`deutschControlledReachableOps` and the target `X` onto `(controlledUnitary pauliXGate).op =
cnotGate.op`. -/
theorem cnotGate_op_mem_closure_deutschControlledReachableOps {α : ℝ} (hα : Irrational α) :
    cnotGate.op ∈ closure (deutschControlledReachableOps α) := by
  have hcont : Continuous fun M : Matrix (Fin 2) (Fin 2) ℂ =>
      controlledOp (S := qubit) (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) M) :=
    (continuous_controlledOp (S := qubit)).comp Matrix.continuous_toEuclideanCLM
  have hx := image_closure_subset_closure_image hcont
    (Set.mem_image_of_mem _ (Concrete.pauliX_mem_closure_cyclic_iRx hα))
  rw [← Set.range_comp] at hx
  rw [cnotGate, controlledUnitary_op_eq, pauliXGate_op]
  exact hx

/-- **`Toffoli` is densely reachable from the Deutsch gate (Nielsen & Chuang, Exercise 4.44).** When
`α` is irrational, the `Toffoli` gate `C²(X)` lies in the closure of the Deutsch gate's iterates
`deutschReachableOps α`: iterating `G = C²(iR_x(πα))` approximates `Toffoli` to arbitrary accuracy.

The counterpart of `Concrete.pauliX_mem_closure_cyclic_iRx` (`X ∈ closure ⟨iR_x(πα)⟩`,
`X = i · R_x(π)`): the doubly-controlled embedding `ccontrolledOp ∘ Matrix.toEuclideanCLM` is
continuous, so it carries the matrix closure into the operator closure
(`image_closure_subset_closure_image`), sending the concrete orbit onto the reachable set
`deutschReachableOps` and the target `X` onto `(ccontrolledUnitary pauliXGate).op = toffoliGate.op`.
This is the density counterpart of `deutschGate_one_eq_toffoliGate` (which gives `Toffoli`
*exactly*, but only at the rational value `α = 1`); for irrational `α` the gate `G` never equals
`Toffoli`, yet its iterates approximate it. -/
theorem toffoliGate_op_mem_closure_deutschReachableOps {α : ℝ} (hα : Irrational α) :
    toffoliGate.op ∈ closure (deutschReachableOps α) := by
  have hcont : Continuous fun M : Matrix (Fin 2) (Fin 2) ℂ =>
      ccontrolledOp (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) M) :=
    continuous_ccontrolledOp.comp Matrix.continuous_toEuclideanCLM
  have hx := image_closure_subset_closure_image hcont
    (Set.mem_image_of_mem _ (Concrete.pauliX_mem_closure_cyclic_iRx hα))
  rw [← Set.range_comp] at hx
  rw [toffoliGate, ccontrolledUnitary_op_eq, pauliXGate_op]
  exact hx

end AxQM

end
