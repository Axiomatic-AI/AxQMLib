/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QftHadamardEvolution
import AxQM.Postulates.API.UnitaryBlochRotation
import AxQM.Concrete.PauliStringDiagonalize
import AxQM.Concrete.KronFamilyWireProduct

/-!
# The Problem 4.3(3) basis-change gate on a register wire, as an `Evolution`

Problem 4.3(3)'s `O(n)`-gate circuit for `exp(-i h_g g Δ)` opens with a layer `B = ⨂ₖ B_{gₖ}` of
single-qubit basis-change gates, one per wire: `B_{gₖ} = pauliDiagGate (gₖ)` diagonalises the Pauli
factor `σ_{gₖ}` to `Z` (Hadamard for `X`, `S·H` for `Y`, identity for `I`/`Z`;
`Concrete/PauliStringDiagonalize`). To *count* that layer with the elementary-gate budget
`CircuitBudget` — which operates on the qubit control tower — each per-wire factor must first be a
named register `Evolution`, exactly as Problem 4.1's phase layer is built from
`phaseWireEvolution`. This file supplies that register-side gate.

## What is formalised

* `pauliDiagGateEvolution a` — the diagonalising gate `B_a = pauliDiagGate a` as a one-qubit
  `Evolution qubit` (the `unitaryGate` promotion of the unitary matrix `pauliDiagGate a`). It is the
  single-qubit factor the wire gate collapses to on a tower wire.
* `pauliDiagWireEvolution n t a` — `B_a` placed on wire `t` of the `2ⁿ`-level register, as an
  `Evolution (qudit (2ⁿ))`: the `quditGate` promotion of `singleQubitOnWire finFunctionFinEquiv t
  (pauliDiagGate a)`. It is the direct analogue of `phaseWireEvolution n t φ` /
  `rotZWireEvolution n t θ`, the basis-change gate indexed by the Pauli `a : Fin 4` rather than a
  real angle.
* `pauliDiagWireEvolution_evolvePure_quditBasis` — its computational-basis action: on
  `|finFunctionFinEquiv f⟩` the wire-`t` component is mixed through the `f t`-column of
  `pauliDiagGate a`. The instance of the reusable single-wire bridge
  `quditGate_singleQubitOnWire_evolvePure_quditBasis` at `G = pauliDiagGate a`.
* `pauliDiagGateEvolution_evolvePure_qubitBasis_sum` — the single-qubit companion:
  `pauliDiagGateEvolution a |z⟩ = ∑_w (pauliDiagGate a) w z · |w⟩`, the `z`-column of `pauliDiagGate
  a`. The instance of the general `unitaryGate_evolvePure_qubitBasis_sum` (in
  `UnitaryBlochRotation`, beside `unitaryGate`) at `M = pauliDiagGate a`.
* `pauliDiagLayer n g` — **the whole basis-change layer** `B = ⨂ₖ B_{gₖ}` as one `Evolution (qudit
  (2ⁿ))`: the ordered product `∏_{t<n} pauliDiagWireEvolution n t (g t)` of the `n` per-wire gates
  (a `List.prod` over `List.finRange n`), the `n`-gate object opening Problem 4.3(3)'s circuit. The
  direct analogue of Problem 4.1's `phaseGradientLayer`.
* `pauliDiagLayer_op` — **faithfulness**: `(pauliDiagLayer n g).op = Matrix.toEuclideanCLM
  (kronFamilyStd (fun k => pauliDiagGate (g k)))`. The layer's operator is *exactly* the matrix
  basis change `B` of `Concrete/PauliStringDiagonalize`, so the `Evolution` promotion genuinely
  realises the tensor basis change and not merely some product of `n` gates. Via the operator
  product law `pauliDiagWireEvolution_listProd_op` and the matrix factorisation
  `Concrete.kronFamilyStd_pauliDiagGate_eq_prod_singleQubitOnWire`.
-/

open Matrix

namespace AxQM

noncomputable section

open AxQM.Concrete

/-- **The Problem 4.3(3) diagonalising gate `B_a` as a one-qubit `Evolution`.** `pauliDiagGate a`
(the identity for `I`/`Z`, Hadamard for `X`, `S·H` for `Y`) promoted to `Evolution qubit` via
`unitaryGate` (unitary by `pauliDiagGate_mem_unitaryGroup`). It is the
single-qubit factor the wire gate `pauliDiagWireEvolution` collapses to on a tower wire. -/
def pauliDiagGateEvolution (a : Fin 4) : Evolution qubit :=
  unitaryGate (pauliDiagGate_mem_unitaryGroup a)

/-- **The Problem 4.3(3) basis-change gate `B_a` on a register wire, as an `Evolution`.** The
diagonalising gate `pauliDiagGate a` placed on wire `t` of the `2ⁿ`-level register `qudit (2ⁿ)`: the
`quditGate` promotion of `singleQubitOnWire finFunctionFinEquiv t (pauliDiagGate a)`. Its basis
action is `pauliDiagWireEvolution_evolvePure_quditBasis`. The direct analogue of
`phaseWireEvolution n t φ`, with the phase gate replaced by the basis-change gate indexed by the
Pauli `a : Fin 4`. Taking `a = g t` over all wires `t` gives the layer `B = ⨂ₖ B_{gₖ}` factor by
factor. -/
def pauliDiagWireEvolution (n : ℕ) (t : Fin n) (a : Fin 4) : Evolution (qudit (2 ^ n)) :=
  quditGate
    (singleQubitOnWire_mem_unitaryGroup finFunctionFinEquiv t (pauliDiagGate_mem_unitaryGroup a))

/-- **The wire-`t` basis-change gate mixes wire `t` through the `pauliDiagGate a` column.**
`pauliDiagWireEvolution n t a |finFunctionFinEquiv f⟩ = ∑_z (pauliDiagGate a) z (f t) ·
|finFunctionFinEquiv (update f t z)⟩`: the bit-string `f` addressing the wires has its wire-`t`
component mixed through the `f t`-column of `pauliDiagGate a`. The instance of the reusable bridge
`quditGate_singleQubitOnWire_evolvePure_quditBasis` at `G = pauliDiagGate a`,
`enc = finFunctionFinEquiv`. -/
theorem pauliDiagWireEvolution_evolvePure_quditBasis (n : ℕ) (t : Fin n) (a : Fin 4)
    (f : Fin n → Fin 2) :
    ((pauliDiagWireEvolution n t a).evolvePure (quditBasis (finFunctionFinEquiv f))).vec
      = ∑ z : Fin 2, pauliDiagGate a z (f t) •
          (quditBasis (finFunctionFinEquiv (Function.update f t z))).vec :=
  quditGate_singleQubitOnWire_evolvePure_quditBasis finFunctionFinEquiv t
    (pauliDiagGate_mem_unitaryGroup a) f

/-- **The one-qubit diagonalising gate acts as its matrix column.**
`pauliDiagGateEvolution a |z⟩ = ∑_w (pauliDiagGate a) w z · |w⟩`, the `z`-column of `pauliDiagGate
a`. The instance of the general `unitaryGate_evolvePure_qubitBasis_sum` at `M = pauliDiagGate a`.
The single-wire factor the tower re-expression matches the register superposition
`pauliDiagWireEvolution_evolvePure_quditBasis` against. -/
theorem pauliDiagGateEvolution_evolvePure_qubitBasis_sum (a : Fin 4) (z : Fin 2) :
    ((pauliDiagGateEvolution a).evolvePure (qubitBasis z)).vec
      = ∑ w : Fin 2, pauliDiagGate a w z • (qubitBasis w).vec :=
  unitaryGate_evolvePure_qubitBasis_sum (pauliDiagGate_mem_unitaryGroup a) z

/-- **A product of single-wire basis-change gates is `toEuclideanCLM` of the matrix product.** For
any list `l` of wires, the operator of the composed circuit `∏_{t ∈ l} B_{gₜ}` of per-wire
diagonalising gates is the promotion through `Matrix.toEuclideanCLM` of the ordered matrix product
of the single-wire gate matrices `singleQubitOnWire finFunctionFinEquiv t (pauliDiagGate (g t))`:

`((l.map fun t => pauliDiagWireEvolution n t (g t)).prod).op`
`= Matrix.toEuclideanCLM ((l.map fun t => singleQubitOnWire finFunctionFinEquiv t
    (pauliDiagGate (g t))).prod)`.

This is the operator-level shadow of the matrix factorisation
`Concrete.kronFamilyStd_pauliDiagGate_eq_prod_singleQubitOnWire`: each factor's operator is
`toEuclideanCLM` of its gate matrix (`quditGate_op`), and `Matrix.toEuclideanCLM` is a `⋆`-algebra
isomorphism, so it carries the matrix product to the operator composition (`map_mul`) and the empty
product to the identity (`map_one`). Proved by induction on `l`: each `cons` splits off the head
gate (`Evolution.comp_op`; `map_mul`) and the `nil` base is `map_one`. -/
theorem pauliDiagWireEvolution_listProd_op (n : ℕ) (g : Fin n → Fin 4) (l : List (Fin n)) :
    ((l.map fun t => pauliDiagWireEvolution n t (g t)).prod).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n))
        ((l.map fun t => singleQubitOnWire finFunctionFinEquiv t (pauliDiagGate (g t))).prod) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Evolution.one_def, Evolution.id_op]
    exact (map_one (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)))).symm
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [Evolution.mul_def, Evolution.comp_op, ih, pauliDiagWireEvolution, quditGate_op, map_mul]
    rfl

/-- **The Problem 4.3(3) basis-change layer** `B = ⨂ₖ B_{gₖ}` as an `Evolution`. The composition
`∏_{t<n} B_{gₜ}` of the `n` single-qubit basis-change gates `pauliDiagWireEvolution n t (g t)`, one
on each wire `t = 0, …, n-1` of the `2ⁿ`-level register, in wire order (a `List.prod` over
`List.finRange n`, `Evolution` being a `Monoid`). This is the `n`-gate layer that opens Problem
4.3(3)'s `O(n)` circuit for `exp(-i h_g g Δ)`: conjugating the Pauli string `g` by `B` sends it to
the all-`Z` string on its support (`pauliStringStd_exp_smul_conj_kronFamilyStd_pauliDiagGate` in
`Concrete/PauliStringDiagonalize`), turning the exponential into a `Z`-string phase circuit. Its
operator is exactly the matrix basis change `B` (`pauliDiagLayer_op`), and its gate cost is `n`
single-qubit gates (`pauliDiagLayer_circuitBudget`, `Core/PauliDiagWireTower`). The direct analogue
of Problem 4.1's `phaseGradientLayer`. -/
def pauliDiagLayer (n : ℕ) (g : Fin n → Fin 4) : Evolution (qudit (2 ^ n)) :=
  ((List.finRange n).map fun t => pauliDiagWireEvolution n t (g t)).prod

/-- **The basis-change layer realises the tensor basis change `B`.** The operator of
`pauliDiagLayer n g` is exactly the matrix basis change `B = ⨂ₖ B_{gₖ}` diagonalising the Pauli
string `g`, promoted through `Matrix.toEuclideanCLM`:

`(pauliDiagLayer n g).op = Matrix.toEuclideanCLM (kronFamilyStd (fun k => pauliDiagGate (g k)))`.

This is the **faithfulness** of the promotion: the `n`-gate `Evolution` layer really *is* the
tensor-product basis change of `Concrete/PauliStringDiagonalize`, not merely some product of `n`
gates. Immediate from the operator product law `pauliDiagWireEvolution_listProd_op` and the matrix
factorisation `Concrete.kronFamilyStd_pauliDiagGate_eq_prod_singleQubitOnWire`. -/
theorem pauliDiagLayer_op (n : ℕ) (g : Fin n → Fin 4) :
    (pauliDiagLayer n g).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n))
          (kronFamilyStd (fun k => pauliDiagGate (g k))) := by
  rw [pauliDiagLayer, pauliDiagWireEvolution_listProd_op,
    kronFamilyStd_pauliDiagGate_eq_prod_singleQubitOnWire]

/-- **Adjoint faithfulness of the basis-change layer (the uncomputation `B†`).** The operator of
`(pauliDiagLayer n g).adjoint` is `Matrix.toEuclideanCLM` of the conjugate transpose of the tensor
basis-change matrix `B = ⨂ₖ B_{gₖ}`:

`(pauliDiagLayer n g).adjoint.op = Matrix.toEuclideanCLM ((kronFamilyStd (fun k => pauliDiagGate
(g k)))ᴴ)`.

The adjoint companion of `pauliDiagLayer_op`: the `Evolution` adjoint's operator is the
Hilbert-space adjoint of the layer's operator (`Evolution.adjoint_op`), which `toEuclideanCLM`
carries to the matrix conjugate transpose (`Matrix.toEuclideanCLM_conjTranspose_eq_adjoint`). This
is the faithfulness of the basis change's *uncomputation* — the `B†` that closes the Figure-4.19
compute–rotate–uncompute cascade (Problem 4.3(3)). -/
theorem pauliDiagLayer_adjoint_op (n : ℕ) (g : Fin n → Fin 4) :
    (pauliDiagLayer n g).adjoint.op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n))
          ((kronFamilyStd (fun k => pauliDiagGate (g k)))ᴴ) := by
  rw [Evolution.adjoint_op, pauliDiagLayer_op]
  exact (Matrix.toEuclideanCLM_conjTranspose_eq_adjoint _).symm

end

end AxQM
