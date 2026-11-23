/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationError

/-!
# Nielsen & Chuang, Exercise 4.40

Show E(R_n(a),R_n(a+b))=|1-exp(i b/2)| and use it to justify (4.76).

Here `E(U, V) ≡ max_{‖ψ‖=1} ‖(U − V)ψ‖` is the gate-approximation error of eq. (4.61) — the
L²-operator norm `‖U − V‖` — and `R_n̂(θ) = exp(−iθ (n·σ)/2) = cos(θ/2) I − i sin(θ/2)(n·σ)` is the
rotation of a qubit about the unit axis `n̂` (eq. 4.8). Equation (4.76), the statement being
justified, is `E(R_n̂(α), R_n̂(θ)^n) < ε/3`: some iterate of a fixed rotation `R_n̂(θ)` approximates
an arbitrary rotation `R_n̂(α)`.

Both ingredients are pure mathematics: `E(U, V)` is the operator norm and `R_n̂(θ)` is a concrete
`2 × 2` unitary matrix.

## The formalisation

The general fact is in
`ToMathlib/Analysis/InnerProductSpace/InvolutionRotation.lean`. For a self-adjoint involution `A`
(`star A = A`, `A * A = 1`) on a complex Hilbert space, the **involution rotation**
`ContinuousLinearMap.rotOfInvol A θ = cos(θ/2) • 1 − (sin(θ/2)·i) • A` is the closed form of
`exp(−i(θ/2)A)`, and:

* `ContinuousLinearMap.norm_sub_rotOfInvol` — **eq. (4.77)** in maximal generality:
  `‖rotOfInvol A α − rotOfInvol A (α+β)‖ = ‖1 − exp(iβ/2)‖`, on any nontrivial space. The base angle
  `α` cancels because the difference is a scalar multiple of an isometry
  (`norm_sub_rotOfInvol_apply`: `star D * D = (2 − 2cos(β/2)) • 1`), so *every* unit vector attains
  the operator norm — the maximiser in eq. (4.61) is arbitrary.
* `ContinuousLinearMap.norm_sub_rotOfInvol_le_sub_int_mul_four_pi` — the **`4π`-periodic** bound
  `‖…‖ ≤ |β − 4π·m|/2` for every integer `m`: `E = ‖1 − exp(iβ/2)‖` is a function of `β` only
  modulo `4π`, so it is small exactly when `β` is near a multiple of `4π`.

The specialisation to the actual qubit rotation operators is in
`AxQM/Concrete/RotationError.lean` (the `2 × 2` matrix `Concrete.rotAxis n θ` is promoted
to the operator `Concrete.rotAxisCLM n θ = R_n̂(θ)` on `EuclideanSpace ℂ (Fin 2)` through the
`⋆`-algebra isomorphism `Matrix.toEuclideanCLM`, with `n·σ` a self-adjoint involution for a unit
axis):

* `AxQM.Concrete.rotAxis_opNorm_sub` — **eq. (4.77) for `R_n̂`**:
  `E(R_n̂(α), R_n̂(α+β)) = ‖1 − exp(iβ/2)‖`.
* `AxQM.Concrete.rotAxis_opNorm_sub_le_mod_four_pi` — the `4π`-periodic bound
  `E(R_n̂(α), R_n̂(α+β)) ≤ |β − 4π·m|/2` for every integer `m`.
* `AxQM.Concrete.rotAxisCLM_pow` — `R_n̂(θ)^k = R_n̂(kθ)`, so the iterate `R_n̂(θ)^n` of
  eq. (4.76) is again a rotation about `n̂`.
* `AxQM.Concrete.exists_pow_opNorm_sub_lt` — **eq. (4.76) as an actual theorem**: given the
  density of `{kθ mod 4π}` near `α` as an explicit hypothesis (a genuine restriction — it holds iff
  `θ` is an irrational multiple of `2π`, by the pigeonhole argument of §4.5.3, external to this
  identity; it fails for `θ` a rational multiple of `2π`), for every `ε > 0` some iterate satisfies
  `‖R_n̂(α) − R_n̂(θ)^k‖ < ε`. The correct bridge is the `4π`-**periodicity** of the error, not the
  raw `|kθ − α|`: `{kθ}` is discrete/unbounded in `ℝ`, so `|kθ − α|` cannot be driven to `0` — only
  the residue mod `4π` can, and `R_n̂(α+2π) = −R_n̂(α)` is why the period is `4π`, not `2π`.
-/
