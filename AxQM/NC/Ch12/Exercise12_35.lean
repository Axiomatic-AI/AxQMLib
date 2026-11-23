/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CSSPhaseBasis
import AxQM.Postulates.API.ProjectiveMeasurement

/-!
# Nielsen & Chuang, Exercise 12.35 (the CSS phase-coset states form an orthonormal basis)

*(N&C p. 598.)*

Show CSS states |xi_{v,z,x}> form an orthonormal basis (sum of projectors = I).

## The formalisation

The exercise has two assertions about vectors and one physical reading. The first two are in
`AxQM/Postulates/API/CSSPhaseBasis.lean`, and this file states the physical reading.

* **Orthonormal basis.** `AxQM.cssPhaseBasis` is the resulting
  `OrthonormalBasis (cssPhaseIndex C₂) ℂ (bitReg ι).space`, built from the orthonormal family
  `cssPhaseFamily` (`cssPhaseFamily_orthonormal`) of the phase-coset states `cssPhaseState`
  (eq. (12.202)) once counted to full dimension (`card_cssPhaseIndex_eq_finrank`).
* **Resolution of the identity (12.204).** `AxQM.cssPhaseFamily_sum_rankOne_eq_id` is
  `∑_p |ξ_p⟩⟨ξ_p| = I` literally, immediate from the basis via `OrthonormalBasis.sum_rankOne_eq_id`.
* **Physics (this file).** A resolution of the identity into orthogonal rank-one projectors *is* a
  projective (von Neumann) measurement (N&C §2.2.5). `cssPhaseMeasurement` is that measurement —
  the `Measurement` reading the register in the CSS phase-coset basis — and
  `cssPhaseMeasurement_isProjective` is the exercise as physics: its operators `Mₚ = |ξ_p⟩⟨ξ_p|` are
  orthogonal projectors. The full N&C projective structure then follows from the derived theorems:
  distinct operators annihilate (`Measurement.IsProjective.orthogonal`, `Pₘ Pₘ' = δₘₘ' Pₘ`) and
  they resolve the identity (`Measurement.IsProjective.sum_op_eq_one`, `∑ₚ Mₚ = I`, i.e. (12.204)).

Both declarations here are stated for `Measurement` and the predicate `Measurement.IsProjective`
(cf. Exercise 2.62).

## Indexing: cosets, not N&C's transversal triple

As a *vector*, `|ξ_{v_k,z,x}⟩` depends only on the total offset `a = v_k + x` (a coset of `C₂` in
`𝔽₂ⁿ`) and the phase `z` mod `C₂⊥`, so the states are indexed by the canonical cosets
`cssPhaseIndex C₂ = (𝔽₂ⁿ ⧸ C₂) × (𝔽₂ⁿ ⧸ C₂⊥)`. N&C's transversal triple `(v_k, z, x)` — with `v_k`
a coset of `C₂` in `C₁`, `x` a coset of `C₁` in `𝔽₂ⁿ`, and `z` a coset of `C₂⊥` in `C₁⊥` — is only
their device for *counting* the states, `2^{k₂} · 2^{n-k₁} · 2^{m}` (`m = k₁ - k₂`), which is
exactly `2^{k₂} · 2^{n-k₂} = 2ⁿ`, the register dimension. Indexing by the cosets directly makes the
formalisation `C₁`-free and representative-independent, holding for *any* linear code `C₂ ≤ 𝔽₂ⁿ`; it
is a faithful, strictly more general rendering of the exercise, not a weakening.
-/

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)]

/-- The **CSS phase-coset measurement**: the projective (von Neumann) measurement reading the
`n`-qubit register `bitReg ι` in the CSS phase-coset basis `cssPhaseBasis` (Nielsen & Chuang,
Exercise 12.35). Its outcome `p = (a, z)` has measurement operator the rank-one projector
`Mₚ = |ξ_p⟩⟨ξ_p|` onto the CSS state `|ξ_{z,a}⟩` (eq. (12.202)); the completeness relation of the
`Measurement` is the resolution of the identity (12.204). -/
noncomputable def cssPhaseMeasurement : Measurement (cssPhaseIndex C₂) (bitReg ι) :=
  Measurement.ofOrthonormalBasis (cssPhaseBasis C₂)

/-- **N&C Exercise 12.35 (physics).** The CSS phase-coset states realise a *projective* (von
Neumann) measurement `cssPhaseMeasurement`: every measurement operator `Mₚ = |ξ_p⟩⟨ξ_p|` is an
orthogonal projector (`Measurement.IsProjective`). This is the physical content of "the states form
an orthonormal basis with `∑ |ξ⟩⟨ξ| = I`" (§2.2.5): the projectors are pairwise orthogonal
(`Measurement.IsProjective.orthogonal`, `Pₘ Pₘ' = δₘₘ' Pₘ`) and resolve the identity
(`Measurement.IsProjective.sum_op_eq_one`, `∑ₚ Mₚ = I`, equation (12.204)). Immediate from
`Measurement.isProjective_ofOrthonormalBasis` applied to the orthonormal basis `cssPhaseBasis`. -/
theorem cssPhaseMeasurement_isProjective : (cssPhaseMeasurement C₂).IsProjective :=
  Measurement.isProjective_ofOrthonormalBasis (cssPhaseBasis C₂)

end AxQM
