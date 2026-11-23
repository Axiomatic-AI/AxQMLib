/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Refocusing

/-!
# Nielsen & Chuang, Exercise 7.38 (Refocusing)

Refocusing: explicitly show (7.150), R²x1 e^{-iaZ1t} R²x1 = e^{iaZ1t}, using Pauli
anti-commutativity.

Here (7.150) is the NMR *refocusing identity* `R²ₓ₁ · e^{−iaZ₁t} · R²ₓ₁ = e^{+iaZ₁t}`, where
`Rₓ₁ = exp(−iπX₁/4)` is the `90°` `x`-rotation on spin 1 (eq. 7.149), so `R²ₓ₁ = exp(−iπX₁/2)` is
the `180°` pulse. Sandwiching the free-precession propagator `e^{−iaZ₁t}` between two `180°` pulses
reverses the evolution.

**Answer.** With `X² = I` one has `R²ₓ₁ = exp(−iπX/2) = −iX`, and the anti-commutation `{X, Z} = 0`
(i.e. `X Z X = −Z`) gives `X e^{−iaZt} X = e^{+iaZt}`. Hence the `180°` pulse reverses the sign of
the `Z`-evolution — the physical content of refocusing. Read literally with the exact exponential
pulse `R²ₓ₁ = −iX`, the two `−i` factors multiply to `−1`, so
`R²ₓ₁ e^{−iaZt} R²ₓ₁ = −e^{+iaZt}`: the printed identity (7.150) holds up to the (physically
irrelevant) global phase `−1`, which vanishes if the `180°` pulse is identified with the Pauli `X`,
or if the sandwich is read as the conjugation `R²ₓ₁ e^{−iaZt} (R²ₓ₁)†`.

The exercise is a `2 × 2` complex-matrix computation about the Pauli
matrices, the matrix exponential, and the `x`-rotation.

## The formalisation

In `AxQM/Concrete/Refocusing.lean` (namespace `AxQM.Concrete`):

* `zEvolution a t = exp(−i a Z t)` — the free-precession propagator of a single spin under
  `H = a Z`, with closed form `zEvolution_eq : zEvolution a t = cos(at) • I − (sin(at) · i) • Z` and
  the bridge `zEvolution_eq_rotZ : zEvolution a t = rotZ (2 a t)` to `Concrete/Rotation`'s `rotZ`.
* `pauliX_conj_smul_one_sub_smul_pauliZ` — the anti-commutativity core the exercise asks for:
  `X (c • I − d • Z) X = c • I + d • Z`, from `X X = I` and `X Z X = −Z`.
* `pauliX_mul_zEvolution_mul_pauliX : pauliX * zEvolution a t * pauliX = zEvolution a (−t)` — the
  exact, phase-free refocusing identity `X e^{−iaZt} X = e^{+iaZt}`.
* `refocusPulse = rotX π` — the `180°` `x`-pulse `R²ₓ₁`, with `refocusPulse_eq_sq` certifying it is
  the square `Rₓ₁²` of the `90°` pulse (eq. 7.149) and `refocusPulse_eq : refocusPulse = −i • X`.
* `refocusPulse_mul_zEvolution_mul_refocusPulse : refocusPulse * zEvolution a t * refocusPulse
  = −zEvolution a (−t)` — the literal (7.150) with the exact exponential pulse, exhibiting the
  global phase `−1`.

## Fidelity

The formalisation is faithful: `zEvolution` is defined as N&C's genuine matrix
exponential `e^{−iaZt}` (not an ad hoc matrix), the sign reversal is proved from Pauli
anti-commutativity exactly as the exercise directs, and both facets of (7.150) are recorded — the
exact refocusing content (`pauliX_mul_zEvolution_mul_pauliX`) and the literal printed equation with
its global phase (`refocusPulse_mul_zEvolution_mul_refocusPulse`) — so the physics is captured and
the printed equation is reported honestly.
-/
