/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.GroverRotation

/-!
# Nielsen & Chuang, Exercise 6.3 (the Grover iteration is a 2×2 rotation)

*(N&C p. 252.)*

Show that in the |alpha>,|beta> basis the Grover iteration is a 2x2 rotation matrix.

In N&C's geometric picture (§6.1.3), `|α⟩` is the uniform superposition of the **non-solutions** and
`|β⟩` that of the **solutions**; the starting state is `|ψ⟩ = cos(θ/2)|α⟩ + sin(θ/2)|β⟩` (Eq. 6.10).
On the plane `span{|α⟩, |β⟩}` the oracle `O` reflects about `|α⟩` and `2|ψ⟩⟨ψ| − I` reflects about
`|ψ⟩`; the product of two reflections is a rotation, so `G = (2|ψ⟩⟨ψ| − I) O` is the rotation
(6.13).

## The matrix representation

The statement is about the `2 × 2` matrix representation *in the `|α⟩, |β⟩` basis*, i.e. over the
two-dimensional coordinate space `ℂ²`: `|α⟩, |β⟩` are the standard basis, the two operators are the
reusable reflection `reflectionMatrix` (`= 2|u⟩⟨u| − I`, from Exercise 6.2), and `G` is their matrix
product. Every statement concerns only complex matrices/vectors and real trigonometry.

## The formalisation

`AxQM/Concrete/GroverRotation.lean` (all in namespace `AxQM.Concrete`):

* `groverState` — the starting state `|ψ⟩ = cos(θ/2)|α⟩ + sin(θ/2)|β⟩` (Eq. 6.10), with
  `groverState_normalized` (`⟨ψ|ψ⟩ = 1`, so `|ψ⟩` is a genuine unit state).
* `groverOracle` — the oracle restricted to `span{|α⟩,|β⟩}` (`= reflectionMatrix |α⟩`), with
  `groverOracle_eq` (`= diag(1, −1)`) and `groverOracle_reflect` (`O(a|α⟩ + b|β⟩) = a|α⟩ − b|β⟩`,
  N&C's characterization of the oracle as the reflection about `|α⟩`).
* `groverIteration` (`= (2|ψ⟩⟨ψ| − I) O`), `groverRotation` (the target matrix of Eq. 6.13), and
  `reflectionMatrix_groverState` (the diffusion `2|ψ⟩⟨ψ| − I` in the `|α⟩, |β⟩` basis).
* `AxQM.Concrete.groverIteration_eq_rotation` — **Exercise 6.3 (Eq. 6.13)**:
  `groverIteration θ = groverRotation θ`, i.e. `G = [[cos θ, −sin θ], [sin θ, cos θ]]`.
* `groverIteration_mulVec_groverState` — Eq. 6.11: one iteration rotates `|ψ⟩` by `θ` to
  `cos(3θ/2)|α⟩ + sin(3θ/2)|β⟩`.
* `sin_groverAngle` — Eq. 6.14: with `cos(θ/2) = √((N−M)/N)`, `sin(θ/2) = √(M/N)` the rotation angle
  satisfies `sin θ = 2√(M(N−M))/N`.
-/
