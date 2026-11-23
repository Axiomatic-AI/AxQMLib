/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BellBasis

/-!
# Nielsen & Chuang, Exercise 2.69 (the Bell basis is an orthonormal basis)

Verify the Bell basis forms an orthonormal basis for the two qubit state space.

The four **Bell states** (Nielsen & Chuang, §1.3.6 / §2.3, eqs. (2.134)–(2.137)) are

`|β₀₀⟩ = (|00⟩+|11⟩)/√2`, `|β₀₁⟩ = (|01⟩+|10⟩)/√2`,
`|β₁₀⟩ = (|00⟩−|11⟩)/√2`, `|β₁₁⟩ = (|01⟩−|10⟩)/√2`,

i.e. `|β_xy⟩ = (|0,y⟩ + (-1)ˣ |1, ȳ⟩)/√2` in N&C's own two-bit `β_xy` indexing (`ȳ` the flip of
`y`).  The exercise asks to verify these four pure states of the two-qubit system `qubit ⊗ qubit`
form an orthonormal basis of its state space.

The Bell states are `PureState`s of the composite system `qubit ⊗ qubit`. That they form an
orthonormal basis of the state space is a statement about the state vectors `PureState.vec` in
`QSystem.space`, using `EuclideanSpace` / `TensorProduct` / `OrthonormalBasis`, `inner` and
`Orthonormal`.

## The declarations

The formalisation is in `AxQM/Postulates/API/BellBasis.lean`:

* `AxQM.bellState x y` — the Bell state `|β_xy⟩`, a `PureState (qubit ⊗ qubit)`.
* `AxQM.bellState_orthonormal` — the family `(x, y) ↦ |β_xy⟩` is **orthonormal**
  (`⟨β_xy|β_x'y'⟩ = δ`), the first half of the exercise.
* `AxQM.bellBasis` — the Bell states packaged as an
  `OrthonormalBasis (Fin 2 × Fin 2) ℂ (qubit ⊗ qubit).space`: the statement that the Bell
  basis **is an orthonormal basis** of the two-qubit state space.  `AxQM.bellBasis_apply`
  records that its `(x, y)` basis vector is exactly `|β_xy⟩`.
* `AxQM.bellState_zero_zero` — `|β₀₀⟩ = |Φ⁺⟩`, tying the family to the standalone
  maximally entangled state `bellPhiPlus` of `Postulates/API/BellState.lean`.

Supporting facts (shared with later Bell-state items such as Exercises 2.70, 2.75):
`AxQM.qubitBasis_tmul_inner` (`⟨ab|cd⟩ = δ_{ac}δ_{bd}`, built on the single-qubit
orthonormality `qubitBasis_inner_qubitBasis` from `Postulates/API/Qubit.lean`),
`AxQM.bellBasisVec` / `AxQM.bellBasisVec_inner` (the Bell vectors and their
inner-product table), and `AxQM.bell_card_eq` (`dim (qubit ⊗ qubit) = 4`).
-/
