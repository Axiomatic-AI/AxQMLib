/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CSSMaxEntVec

/-!
# Nielsen & Chuang, Exercise 12.36 (verify Equation (12.203))

*(N&C §12.6.3 "Quantum cryptography", p. 598.)*

Verify Equation (12.203) expressing |beta>^n in the CSS state basis.

Equation (12.203) rewrites Alice's `n`-EPR-pair state in the CSS phase-coset basis:

  `|β₀₀⟩⊗ⁿ = ∑ⱼ |j⟩|j⟩ = ∑_{v_k,z,x} |ξ_{v_k,z,x}⟩|ξ_{v_k,z,x}⟩`,     (12.203)

where the first ket in each term is the `n` qubits Alice keeps and the second the `n` qubits sent to
Bob, and `|ξ_{v_k,z,x}⟩ = |C₂|^{-1/2} ∑_{w ∈ C₂} (-1)^{z·w} |v_k + w + x⟩` are the CSS states of
(12.202), which form an orthonormal basis (Exercise 12.35).

## The formalisation

The content of (12.203) is a **vector identity** in `(bitReg ι).space ⊗ (bitReg ι).space`, stated
with `OrthonormalBasis.maxEntVec`, `TensorProduct` and the bases `regBasis` / `cssPhaseBasis`. See
also Exercise 12.34 for related maximally-entangled-vector material.

### The declarations

The linear-algebra **core** — basis-independence of the (unnormalised, same-space-twice,
no-conjugation) maximally entangled vector under a *real* orthonormal change of basis, and the
criterion for the realness hypothesis — in the file
`ToMathlib/Analysis/InnerProductSpace/MaxEntVecBasis.lean`:

* `OrthonormalBasis.maxEntVec_eq_of_forall_conjVec_eq` — if every `b' k` is real relative to `b`
  (`b.conjVec (b' k) = b' k`) then `b'.maxEntVec = b.maxEntVec`. This is the "and thus we may write"
  step of N&C's argument, in full generality. The realness hypothesis is *necessary*: for a
  genuinely complex change of basis the two vectors differ (the vector face of the transpose trick
  `(A ⊗ I)|α⟩ = (I ⊗ Aᵀ)|α⟩`).
* `OrthonormalBasis.conjVec_eq_self_of_forall_inner_comm` — the criterion discharging that
  hypothesis from real coordinates (`⟪ψ, b i⟫ = ⟪b i, ψ⟫`).

The **instantiation** to the CSS basis — i.e. Equation (12.203) itself — in
`AxQM/Postulates/API/CSSMaxEntVec.lean` (namespace `AxQM`):

* `nEPRVec` — the (unnormalised) maximally entangled vector `|β₀₀⟩⊗ⁿ = ∑ⱼ |j⟩ ⊗ |j⟩` of the `n` EPR
  pairs, with `nEPRVec_eq_sum_regBasis_tmul` the **first equality** (definitional).
* `cssPhaseState_conjVec_regBasis` — the CSS states are real in the computational basis (their
  `± |C₂|^{-1/2}` coefficients are real), the realness hypothesis of (12.203).
* `cssPhaseBasis_maxEntVec_eq_regBasis` — the **second equality** `cssPhaseBasis.maxEntVec =
  regBasis.maxEntVec`, the substance of Ex 12.36.
* `nEPRVec_eq_sum_cssPhaseFamily_tmul` — Equation (12.203) in full,
  `|β₀₀⟩⊗ⁿ = ∑_{v_k,z,x} |ξ⟩ ⊗ |ξ⟩`.

These use Exercise 12.35's `cssPhaseState` (eq. (12.202)) and `cssPhaseBasis` (the CSS
orthonormal basis, `AxQM/Postulates/API/CSSPhaseBasis.lean`) rather than re-deriving them.
-/
