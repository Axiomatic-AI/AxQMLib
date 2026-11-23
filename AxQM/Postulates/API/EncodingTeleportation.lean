/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Teleportation

/-!
# AxQM.Postulates.API — Encoding an unknown qubit by teleportation

The verifiable mathematical core of **Nielsen & Chuang Problem 10.4** ("Encoding by
teleportation"): teleporting an *unknown* qubit `|ψ⟩` into the logical qubit of a stabilizer code,
using the *partially encoded* resource state `(|0⟩|0_L⟩ + |1⟩|1_L⟩)/√2` and a Bell-basis
measurement, with logical Pauli byproduct corrections.  This is the standard §1.3.7 teleportation
protocol (`AxQM/Postulates/API/Teleportation.lean`) with **Bob's half of the Bell pair replaced by
the encoder's image**
in the code space, so that the teleported qubit lands *already encoded*.

## The encoder

A **code encoder** is a linear isometry `E : qubit.space →ₗ[ℂ] C.space` sending the logical basis
`|0⟩, |1⟩` to the code's logical codewords `|0_L⟩ = E|0⟩`, `|1_L⟩ = E|1⟩` — orthonormal states of
the (larger) code system `C`.  This is exactly the logical embedding of a single encoded qubit into
any `[n, 1]` stabilizer code; the identities below are stated for an *arbitrary* `E`, so they hold
for every such code, matching Problem 10.4's unspecified "a stabilizer code".  (The core algebra
needs only linearity of `E`; `E` is taken to be an honest linear map here, with the isometric
structure — orthonormal codewords, hence a genuine normalised resource `PureState` — recorded by
`encoderBellState` for a `LinearIsometry` `E`.)

## What is formalised

* `encoderBellVec E` — the **partially encoded resource vector**
  `(|0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩)/√2 = (I ⊗ E)|Φ⁺⟩` on `qubit ⊗ C` (N&C eq. 10.126, the state prepared in
  part (1)): Bob's half of a Bell pair pushed through the encoder `E`.
* `encoderBellState E` (for a `LinearIsometry` `E`) — the same resource packaged as a genuine
  **`PureState (qubit ⊗ C)`**: an isometric `E` maps the orthonormal logical basis to orthonormal
  codewords, so the resource is normalised (`encoderBellState_vec` exposes its vector).
* `encodingTeleportation_identity` — the **encoding-teleportation identity**: for an arbitrary qubit
  `|ψ⟩`, re-associating `|ψ⟩ ⊗ (partially encoded resource)` and grouping the first two qubits gives
  `|ψ⟩ ⊗ resource = ½ Σ_{x,y} |β_xy⟩ ⊗ E(X^y Z^x |ψ⟩)`.
  A Bell measurement of the first pair (part (2)) therefore leaves the code register in
  `E(X^y Z^x |ψ⟩) = X_L^y Z_L^x |ψ_L⟩` — the encoded input up to the *logical* Pauli byproduct
  `E ∘ (X^y Z^x) ∘ E†`, undone by the same outcome-indexed correction `pauliByproduct x y` applied
  logically (part (3)).  Setting `C = qubit`, `E = id` (so the resource is `|Φ⁺⟩`) recovers exactly
  `teleportation_identity`.
* `encodingTeleportation_identity_qubitBasis` — its specialisation to a computational-basis input
  `|i⟩`.

## Design notes

* **What is formalised, and what is not.**  Problem 10.4 is a fault-tolerant *circuit
  construction* question; its parts (1)–(3) reduce to one linear-algebra identity — the encoding
  analogue of teleportation — which is what is proved here.  The surrounding requests are claims
  about a circuit / error model the library has no vocabulary for and so are noted,
  not formalised: *"prepare the resource fault-tolerantly by measuring stabilizer generators"* and
  *"perform the Bell measurement fault-tolerantly"* are fault-tolerance constructions (no
  fault-tolerance framework); *"compute the probability of error of this circuit"* needs a physical
  error model over gates (none in the library); *"modify the circuit to perform fault-tolerant
  decoding"* is the same construction run in reverse. 
  `AxQM/NC/Ch10/Problem10_4_EncodingByTeleportation.lean`
  records these on top of the identity, exactly as `AxQM/NC/Ch4/Problem4_6.lean`
  (universality by gate teleportation) records "universal" on top of its teleportation identity.
* **Byproduct convention.**  The correction pairing with Bell outcome `β_xy` is `X^y Z^x`
  (`pauliByproduct x y`), the same convention as `teleportation_identity`; here it is applied
  *logically*, i.e. `E` carries `X^y Z^x |ψ⟩` to the encoded corrected state.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {C : QSystem}

/-! ### The partially encoded resource state -/

/-- The **unnormalised partially encoded vector** `|0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩` on `qubit ⊗ C`, where the
logical codewords are the encoder images `|0_L⟩ = E|0⟩`, `|1_L⟩ = E|1⟩`.  Its norm is `√2` for an
isometric encoder (`encoderBellUnnormVec_inner_self`); the normalised resource is `encoderBellVec`.
Built directly from the tensor of basis vectors (like `bellVec`), so it presents the composite
`(qubit ⊗ C).space` head that the scalar-factoring lemmas want. -/
def encoderBellUnnormVec (E : qubit.space →ₗ[ℂ] C.space) : (qubit ⊗ C).space :=
  (qubitBasis 0).vec ⊗ₜ[ℂ] E (qubitBasis 0).vec + (qubitBasis 1).vec ⊗ₜ[ℂ] E (qubitBasis 1).vec

/-- The **partially encoded resource vector** `(|0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩)/√2` on `qubit ⊗ C`
(Nielsen & Chuang eq. 10.126), where the logical codewords are the encoder images
`|0_L⟩ = E|0⟩`, `|1_L⟩ = E|1⟩`.  Equivalently `(I ⊗ E)|Φ⁺⟩`: Bob's half of a shared Bell pair
pushed through the code encoder `E`. -/
def encoderBellVec (E : qubit.space →ₗ[ℂ] C.space) : (qubit ⊗ C).space :=
  (Real.sqrt 2 : ℂ)⁻¹ • encoderBellUnnormVec E

/-- **The squared norm of the unnormalised partially encoded vector is `2`** (for an isometric
encoder): `⟨0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩ | same⟩ = 2`.  Because an isometry sends the orthonormal logical
basis to orthonormal codewords (`LinearIsometry.inner_map_map` and `qubitBasis_inner_qubitBasis`),
the cross terms vanish and the two diagonal terms each contribute `⟨i|i⟩⟨i_L|i_L⟩ = 1`.  Mirrors
`bellVec_inner_self`, restating the inner product over the raw tensor head to expand it. -/
theorem encoderBellUnnormVec_inner_self (E : qubit.space →ₗᵢ[ℂ] C.space) :
    (inner ℂ (encoderBellUnnormVec E.toLinearMap) (encoderBellUnnormVec E.toLinearMap) : ℂ)
      = 2 := by
  change (@inner ℂ (TensorProduct ℂ qubit.space C.space) _ (encoderBellUnnormVec E.toLinearMap)
    (encoderBellUnnormVec E.toLinearMap) : ℂ) = 2
  rw [encoderBellUnnormVec, inner_add_left, inner_add_right, inner_add_right,
    TensorProduct.inner_tmul, TensorProduct.inner_tmul,
    TensorProduct.inner_tmul, TensorProduct.inner_tmul]
  simp only [LinearIsometry.coe_toLinearMap, LinearIsometry.inner_map_map,
    qubitBasis_inner_qubitBasis]
  norm_num

/-- **The partially encoded resource as a genuine pure state** (Nielsen & Chuang eq. 10.126): for
an *isometric* encoder `E : qubit.space →ₗᵢ[ℂ] C.space` (the logical embedding of a stabilizer
code — orthonormal logical basis to orthonormal codewords), the resource vector `encoderBellVec E`
is normalised, so it is a `PureState (qubit ⊗ C)`.  This is the "state to be prepared" of part (1):
the isometric `E` makes `|0_L⟩ = E|0⟩`, `|1_L⟩ = E|1⟩` orthonormal, whence the two summands
`|0⟩⊗|0_L⟩`, `|1⟩⊗|1_L⟩` are orthonormal and `(|0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩)/√2` is a unit vector. -/
def encoderBellState (E : qubit.space →ₗᵢ[ℂ] C.space) : PureState (qubit ⊗ C) where
  vec := encoderBellVec E.toLinearMap
  normalized := by
    have hb : ‖encoderBellUnnormVec E.toLinearMap‖ = Real.sqrt 2 := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), encoderBellUnnormVec_inner_self]; norm_num
    rw [encoderBellVec, norm_smul, hb, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), inv_mul_cancel₀ (by positivity)]

/-- The underlying unit vector of the partially encoded resource `encoderBellState E` is
`encoderBellVec E.toLinearMap = (|0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩)/√2`.  A `simp` lemma exposing the
state vector. -/
@[simp]
theorem encoderBellState_vec (E : qubit.space →ₗᵢ[ℂ] C.space) :
    (encoderBellState E).vec = encoderBellVec E.toLinearMap := rfl

/-! ### The encoding-teleportation identity -/

/-- Apply the associator to `v ⊗ (partially encoded resource)`, distributing the Bell normalisation
and re-bracketing to the left-nested `(v ⊗ ·) ⊗ ·` head:
`assoc (v ⊗ encoderBellVec E) = (√2)⁻¹ ((v⊗|0⟩)⊗E|0⟩ + (v⊗|1⟩)⊗E|1⟩)`.  Each pure summand is
rewritten back into `assoc (v ⊗ (|k⟩⊗E|k⟩))` by `assoc_toIsometry_tmul_tmul`, and the associator's
`ℂ`-linearity (`map_smul`, `map_add`) then discharges the normalisation and the sum.  The encoding
analogue of `assoc_toIsometry_tmul_bellPhiPlus`, needing no head-`change` because `encoderBellVec`
is already built at the composite `(qubit ⊗ C).space` head. -/
theorem assoc_toIsometry_tmul_encoderBellVec (E : qubit.space →ₗ[ℂ] C.space) (v : qubit.space) :
    (QSystem.assoc qubit qubit C).toIsometry (v ⊗ₜ[ℂ] encoderBellVec E)
      = (Real.sqrt 2 : ℂ)⁻¹ • ((v ⊗ₜ[ℂ] (qubitBasis 0).vec) ⊗ₜ[ℂ] E (qubitBasis 0).vec
          + (v ⊗ₜ[ℂ] (qubitBasis 1).vec) ⊗ₜ[ℂ] E (qubitBasis 1).vec) := by
  have h1 : v ⊗ₜ[ℂ] encoderBellVec E
      = (Real.sqrt 2 : ℂ)⁻¹ • (v ⊗ₜ[ℂ] ((qubitBasis 0).vec ⊗ₜ[ℂ] E (qubitBasis 0).vec)
          + v ⊗ₜ[ℂ] ((qubitBasis 1).vec ⊗ₜ[ℂ] E (qubitBasis 1).vec)) := by
    change v ⊗ₜ[ℂ] ((Real.sqrt 2 : ℂ)⁻¹ • ((qubitBasis 0).vec ⊗ₜ[ℂ] E (qubitBasis 0).vec
        + (qubitBasis 1).vec ⊗ₜ[ℂ] E (qubitBasis 1).vec) : qubit.space ⊗[ℂ] C.space) = _
    rw [TensorProduct.tmul_smul, TensorProduct.tmul_add]
  rw [h1, ← assoc_toIsometry_tmul_tmul v (qubitBasis 0).vec (E (qubitBasis 0).vec),
    ← assoc_toIsometry_tmul_tmul v (qubitBasis 1).vec (E (qubitBasis 1).vec)]
  exact (map_smul _ _ _).trans (congrArg _ (map_add _ _ _))

/-- **The encoding-teleportation identity** (Nielsen & Chuang Problem 10.4): for an arbitrary qubit
state `|ψ⟩` and a code encoder `E`, re-associating `|ψ⟩ ⊗ (|0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩)/√2` and grouping
the first two qubits gives
`|ψ⟩ ⊗ (partially encoded resource) = ½ Σ_{x,y} |β_xy⟩ ⊗ E(X^y Z^x |ψ⟩)`.
Measuring the first pair in the Bell basis therefore leaves the code register in the *encoded*
byproduct-corrected state `E(X^y Z^x |ψ⟩)`, which the logical Pauli correction (the byproduct
`pauliByproduct x y` conjugated into the code) undoes — teleportation directly into the logical
qubit.  With `C = qubit` and `E = id` (the resource is then `|Φ⁺⟩`) this is exactly
`teleportation_identity`; the proof mirrors it, distributing both sides over the computational basis
and closing the resulting linear identity by `module`. -/
theorem encodingTeleportation_identity (E : qubit.space →ₗ[ℂ] C.space) (v : qubit.space) :
    (QSystem.assoc qubit qubit C).toIsometry (v ⊗ₜ[ℂ] encoderBellVec E)
      = (2 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2,
          bellBasisVec p.1 p.2 ⊗ₜ[ℂ] E ((pauliByproduct p.1 p.2).op v) := by
  have hv : v = v.ofLp 0 • (qubitBasis 0).vec + v.ofLp 1 • (qubitBasis 1).vec := by
    have h := (EuclideanSpace.sum_single_ofLp_eq v).symm
    rw [Fin.sum_univ_two] at h
    simp only [qubitBasis_vec]
    exact h
  rw [assoc_toIsometry_tmul_encoderBellVec, Fintype.sum_prod_type]
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  simp only [Fin.sum_univ_two, TensorProduct.add_tmul, ← TensorProduct.smul_tmul',
    pauliByproduct_op_apply_qubitBasis, bellBasisVec_tmul, map_add, map_smul,
    TensorProduct.tmul_add, TensorProduct.tmul_smul, Fin.isValue, Fin.val_zero, Fin.val_one,
    Nat.mul_zero, Nat.mul_one, pow_zero, pow_one, one_smul, Fin.reduceAdd]
  generalize v.ofLp 0 = c₀
  generalize v.ofLp 1 = c₁
  generalize (qubitBasis 0).vec = a
  generalize (qubitBasis 1).vec = b
  generalize E a = ea
  generalize E b = eb
  let s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  -- A linear identity in the eight computational basis atoms `(·⊗·)⊗·` (the first two factors in
  -- `qubit.space`, the third `ea, eb : C.space`), weighted by the amplitudes `c₀, c₁` of `|ψ⟩`.
  -- The `change` re-elaborates the tensors with canonical instances so the atoms coincide across
  -- both sides (they are defeq but arrive by two construction paths carrying different instance
  -- arguments, which `module`'s atom-matching distinguishes), and `module` then closes it.
  change s • (c₀ • a ⊗ₜ[ℂ] a ⊗ₜ[ℂ] ea + c₁ • b ⊗ₜ[ℂ] a ⊗ₜ[ℂ] ea +
        (c₀ • a ⊗ₜ[ℂ] b ⊗ₜ[ℂ] eb + c₁ • b ⊗ₜ[ℂ] b ⊗ₜ[ℂ] eb)) =
      (2 : ℂ)⁻¹ •
        (c₀ • s • (a ⊗ₜ[ℂ] a ⊗ₜ[ℂ] ea + b ⊗ₜ[ℂ] b ⊗ₜ[ℂ] ea) +
              c₁ • (1 : ℂ) • s • (a ⊗ₜ[ℂ] a ⊗ₜ[ℂ] eb + b ⊗ₜ[ℂ] b ⊗ₜ[ℂ] eb) +
            (c₀ • s • (a ⊗ₜ[ℂ] b ⊗ₜ[ℂ] eb + b ⊗ₜ[ℂ] a ⊗ₜ[ℂ] eb) +
              c₁ • (1 : ℂ) • s • (a ⊗ₜ[ℂ] b ⊗ₜ[ℂ] ea + b ⊗ₜ[ℂ] a ⊗ₜ[ℂ] ea)) +
          (c₀ • s • (a ⊗ₜ[ℂ] a ⊗ₜ[ℂ] ea + (-1 : ℂ) • b ⊗ₜ[ℂ] b ⊗ₜ[ℂ] ea) +
              c₁ • (-1 : ℂ) • s •
                (a ⊗ₜ[ℂ] a ⊗ₜ[ℂ] eb + (-1 : ℂ) • b ⊗ₜ[ℂ] b ⊗ₜ[ℂ] eb) +
            (c₀ • s • (a ⊗ₜ[ℂ] b ⊗ₜ[ℂ] eb + (-1 : ℂ) • b ⊗ₜ[ℂ] a ⊗ₜ[ℂ] eb) +
              c₁ • (-1 : ℂ) • s •
                (a ⊗ₜ[ℂ] b ⊗ₜ[ℂ] ea + (-1 : ℂ) • b ⊗ₜ[ℂ] a ⊗ₜ[ℂ] ea))))
  module

/-- **Per-basis encoding-teleportation identity:** the `encodingTeleportation_identity` for a
computational-basis input `|i⟩`.  A direct specialisation. -/
theorem encodingTeleportation_identity_qubitBasis (E : qubit.space →ₗ[ℂ] C.space) (i : Fin 2) :
    (QSystem.assoc qubit qubit C).toIsometry ((qubitBasis i).vec ⊗ₜ[ℂ] encoderBellVec E)
      = (2 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2,
          bellBasisVec p.1 p.2 ⊗ₜ[ℂ] E ((pauliByproduct p.1 p.2).op (qubitBasis i).vec) :=
  encodingTeleportation_identity E (qubitBasis i).vec

end AxQM
